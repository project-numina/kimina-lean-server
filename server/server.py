import asyncio
import uuid
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import asynccontextmanager
from datetime import datetime
from typing import Annotated

from fastapi import Depends, FastAPI, Header, HTTPException, Request
from loguru import logger
from pydantic import BaseModel, Field
from tqdm import tqdm

from utils.proof_utils import split_proof_header
from utils.repl_cache import LRUReplCache

from .config import settings
from .healthcheck import router
from .leanrepl import LeanCrashError, LeanREPL

time_stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
logger.remove()
logger.add(f"{settings.LOG_DIR}/server_{time_stamp}.log")

repls = {}
semaphore = asyncio.Semaphore(settings.MAX_CONCURRENT_REQUESTS)
repl_cache = LRUReplCache(max_size=settings.MAX_REPLS)


async def _repl_creater():
    while True:
        await asyncio.sleep(10)
        if len(repl_cache.create_queue) > 0:
            repl_to_create = Counter(repl_cache.create_queue)
            repl_cache.create_queue = []

            for header, amount in tqdm(repl_to_create.items(), desc="Creating REPLs"):
                tasks = []
                creating_repls = []
                try:
                    for _ in range(amount):
                        repl = LeanREPL()
                        creating_repls.append(repl)
                        tasks.append(asyncio.to_thread(repl.create_env, header, 600))

                    responses = await asyncio.gather(*tasks)
                    logger.info(
                        f"Created {len(responses)} {str([header])[:50]} repls with response {str(responses)[:50]}"
                    )
                except LeanCrashError:
                    for repl in creating_repls:
                        repl_cache.close_queue.put(repl)

                # put the repls in the cache
                for repl in creating_repls:
                    await repl_cache.put(header, repl)


async def _repl_cleaner():
    while True:
        await asyncio.sleep(1)
        while not repl_cache.close_queue.empty():
            id, repl = repl_cache.close_queue.get()
            await asyncio.to_thread(repl.close)
            logger.info(f"Closed {id} repl")


async def _stat_printer():
    update_interval = 15
    while True:
        await asyncio.sleep(update_interval)
        await repl_cache.print_status(update_interval)


@asynccontextmanager
async def lifespan(app: FastAPI):
    """App lifespan context manager"""
    app.state.executor = ThreadPoolExecutor(max_workers=5000)
    asyncio.get_running_loop().set_default_executor(app.state.executor)

    # Repl cache manager tasks
    relp_cache_tasks = [
        asyncio.create_task(_repl_cleaner()),
        asyncio.create_task(_repl_creater()),
        asyncio.create_task(_stat_printer()),
    ]

    # Prefill repl_cache, The pre-filled amount should not be greater than settings.MAX_REPLS.
    # repl_cache.create_queue.extend(["import Mathlib"] * int(settings.MAX_REPLS / 2))
    # TODO: Make it an initialization parameter.
    repl_cache.create_queue.extend(
        ["import Mathlib\nimport Aesop"] * int(settings.MAX_REPLS)
    )

    try:
        yield
    finally:
        # Cancel cache manager task
        for task in relp_cache_tasks:
            task.cancel()
            try:
                await task
            except asyncio.CancelledError:
                pass

        # Close thread pools
        app.state.executor.shutdown(wait=True)


app = FastAPI(lifespan=lifespan)


# ------ Dependencies ------
def validate_api_access(request: Request, authorization: str = Header(None)) -> None:
    api_key = settings.API_KEY
    if api_key is None:
        return

    if authorization is None or not authorization.startswith("Bearer "):
        raise HTTPException(
            status_code=401, detail="Missing or invalid Authorization header"
        )

    token = authorization.split("Bearer ")[-1]
    if token != api_key:
        raise HTTPException(status_code=403, detail="Invalid API Key")


async def get_repl(request: Request):
    repl = {}

    try:
        yield repl
    except Exception as ex:
        for _, id_and_repl in repl.items():
            if id_and_repl is None:
                continue
            id, repl_instance = id_and_repl
            if id is not None:
                assert repl_instance.header is not None
                await repl_cache.destroy(repl_instance.header, id, repl_instance)
                repl_cache.create_queue.append(repl_instance.header)
                logger.info("teardown_request:", id, id in repl_cache.global_repl_pool)
            repl_cache.close_queue.put((id, repl_instance))

        raise ex


require_access_dep = Annotated[None, Depends(validate_api_access)]
lean_repl_dep = Annotated[dict[str, tuple[str, LeanREPL | None]], Depends(get_repl)]


# ------ Schemas ------
class Code(BaseModel):
    custom_id: str | int
    proof: str = Field(None)
    code: str = Field(None)  # To be backward compatibility with autoformalizer client

    def get_proof_content(self) -> str:
        return self.proof if self.proof is not None else self.code


class VerifyRequestBody(BaseModel):
    codes: list[Code]
    timeout: int = 300
    infotree_type: str | None = None
    disable_cache: bool = False


# ------ Endpoint ------
@app.get("/")
async def root(require_access_dep: require_access_dep):
    return {"status": "ok"}


@app.post("/verify")
async def verify(
    body: VerifyRequestBody,
    lean_repl: lean_repl_dep,
    access: require_access_dep,
):
    """verify the proof code."""
    codes = body.codes
    timeout = body.timeout
    infotree_type = body.infotree_type
    disable_cache = body.disable_cache

    tasks = [
        process_one_code_with_repl_fast(
            code, timeout, infotree_type, lean_repl, disable_cache=disable_cache
        )
        for code in codes
    ]

    # Await the results of all the tasks concurrently
    results_data = await asyncio.gather(*tasks)

    results = []
    for result in results_data:
        custom_id, error, response = result
        results.append(
            {
                "custom_id": custom_id,
                "error": error,
                "response": response,
            }
        )

    return {"results": results}


async def process_one_code_with_repl_fast(
    code: Code,
    timeout: int,
    infotree_type: str | None,
    repl: lean_repl_dep,
    disable_cache: bool = False,
):
    # Throttle the incoming request
    async with semaphore:
        error_msg = None
        response = None
        grepl_id = str(uuid.uuid4())

        custom_id = code.custom_id
        proof = code.get_proof_content()

        if proof is None:
            return custom_id, "No code provided", response

        proof_header, proof_body = split_proof_header(proof)

        # if we can not found the proof header, create a new repl
        if len(proof_header.strip()) == 0 or disable_cache:
            lean_repl = LeanREPL()
            try:
                response = await asyncio.to_thread(
                    lean_repl.one_pass_verify, proof, timeout, infotree_type
                )
            except LeanCrashError as e:
                error_msg = str(e)
            finally:
                del lean_repl
            return custom_id, error_msg, response

        # Get lean repl instance from the lrucache
        repl[grepl_id] = await repl_cache.get(proof_header)

        # If we can not get the repl from the lrucache, we will create a new repl
        if repl[grepl_id][0] is None:
            repl[grepl_id] = None, LeanREPL()

            # And import the proof header
            try:
                response = await asyncio.to_thread(
                    repl[grepl_id][1].create_env, proof_header, timeout
                )
            except LeanCrashError as e:
                error_msg = str(e)
                return custom_id, error_msg, response

        try:
            response = await asyncio.to_thread(
                repl[grepl_id][1].extend_env,
                0,
                proof_body,
                timeout,
                infotree_type,
            )
        except LeanCrashError as e:
            error_msg = str(e)
            if repl[grepl_id][0] is None:
                await repl_cache.destroy(proof_header, *repl[grepl_id])
            return custom_id, error_msg, response

        # Successfully extended the context, release the REPL back to the cache
        if repl[grepl_id][0] is None:
            await repl_cache.put(proof_header, repl[grepl_id][1])
        else:
            await repl_cache.release(proof_header, *repl[grepl_id])

        repl[grepl_id] = None
        return custom_id, error_msg, response


@app.post("/one_pass_verify_batch")
async def one_pass_verify_batch(
    body: VerifyRequestBody,
    lean_repl: lean_repl_dep,
    access: require_access_dep,
):
    """Backward compatible endpoint: accepts both 'proof' / 'code' fields."""
    return await verify(body, lean_repl, access)


app.include_router(router)
