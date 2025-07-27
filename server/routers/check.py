import asyncio
import json
from typing import cast

from fastapi import APIRouter, Depends, HTTPException, Request
from kimina import CheckRequest, Infotree, ReplResponse, Snippet
from kimina.models import CheckResponse
from loguru import logger

from ..db import db
from ..errors import NoAvailableReplError
from ..manager import Manager
from ..prisma_client import prisma
from ..repl import Repl
from ..split import split_snippet

router = APIRouter()


def get_manager(request: Request) -> Manager:
    """Dependency: retrieve the REPL manager from app state"""
    return cast(Manager, request.app.state.manager)


async def run_checks(
    snippets: list[Snippet],
    timeout: float,
    debug: bool,
    manager: Manager,
    reuse: bool,
    infotree: Infotree | None = None,
) -> list[ReplResponse]:
    async def run_one(snippet: Snippet) -> ReplResponse:
        repl: Repl | None = None
        try:
            header, body = split_snippet(snippet.code)
            try:
                repl = await manager.get_repl(header, snippet.id, reuse=reuse)
            except NoAvailableReplError:
                logger.exception("No available REPLs")
                raise HTTPException(429, "No available REPLs") from None
            except Exception as e:
                logger.exception("Failed to get REPL: %s", e)
                raise HTTPException(500, str(e)) from e

            # if reuse is false we should not run the header separate from body
            try:
                prep = await manager.prep(repl, snippet.id, timeout, debug)
                if prep and prep.error:
                    return prep
            except TimeoutError as e:
                error = f"Lean REPL header command timed out in {timeout} seconds"
                uuid_hex = repl.uuid.hex
                await manager.destroy_repl(repl)
                if db.connected:
                    await prisma.proof.create(
                        data={
                            "id": snippet.id,
                            "code": header,
                            "time": timeout,
                            "error": error,
                            "repl": {
                                "connect": {"uuid": uuid_hex},
                            },
                        }  # type: ignore
                    )
                return ReplResponse(
                    id=snippet.id,
                    error=error,
                    time=timeout,
                    diagnostics={
                        "repl_uuid": uuid_hex,
                    },
                )
            except Exception as e:
                logger.error("REPL prep failed")
                await manager.destroy_repl(repl)
                raise HTTPException(500, str(e)) from e

            try:
                resp = await repl.send_timeout(
                    Snippet(id=snippet.id, code=body), timeout, infotree=infotree
                )
            except TimeoutError as e:
                error = f"Lean REPL command timed out in {timeout} seconds"
                uuid_hex = repl.uuid.hex
                await manager.destroy_repl(repl)
                if db.connected:
                    await prisma.proof.create(
                        data={
                            "id": snippet.id,
                            "code": body,
                            "time": timeout,
                            "error": error,
                            "repl": {
                                "connect": {"uuid": uuid_hex},
                            },
                        }  # type: ignore
                    )
                resp = ReplResponse(
                    id=snippet.id,
                    error=error,
                    time=timeout,
                    diagnostics={
                        "repl_uuid": uuid_hex,
                    },
                )
                logger.info(
                    "[{}] Response for [bold magenta]{}[/bold magenta] body →\n{}",
                    repl.uuid.hex[:8],
                    snippet.id,
                    json.dumps(resp.model_dump(exclude_none=True), indent=2),
                )
                return resp
            except Exception as e:
                logger.exception("Snippet execution failed")
                await manager.destroy_repl(repl)
                raise HTTPException(500, str(e)) from e
            else:
                logger.info(
                    "[{}] Response for [bold magenta]{}[/bold magenta] body →\n{}",
                    repl.uuid.hex[:8],
                    snippet.id,
                    json.dumps(resp.model_dump(exclude_none=True), indent=2),
                )
                await manager.release_repl(repl)
                # todo: Try catch everything DB related
                if db.connected:
                    await prisma.proof.create(
                        data={
                            "id": snippet.id,
                            "code": body,
                            "diagnostics": json.dumps(
                                resp.diagnostics if resp.diagnostics else None
                            ),
                            "response": json.dumps(
                                resp.response if resp.response else None
                            ),
                            "time": resp.time,
                            "error": resp.error,
                            "repl": {
                                "connect": {"uuid": repl.uuid.hex},
                            },
                        }  # type: ignore
                    )
                if not debug:
                    resp.diagnostics = None
                return resp
        except asyncio.CancelledError:
            if repl:
                await manager.destroy_repl(repl)  # Kill REPL on cancel
            raise

    results = await asyncio.gather(*(run_one(s) for s in snippets))
    return list(results)


@router.post(
    "/check",
    response_model=CheckResponse,
    response_model_exclude_none=True,
)
@router.post(
    "/check/",
    response_model=CheckResponse,
    response_model_exclude_none=True,
    include_in_schema=False,  # To not clutter OpenAPI spec.
)
async def check(
    request: CheckRequest,
    raw_request: Request,
    manager: Manager = Depends(get_manager),
) -> CheckResponse:
    task = asyncio.create_task(
        run_checks(
            request.snippets,
            float(request.timeout),
            request.debug,
            manager,
            request.reuse,
            request.infotree,
        )
    )

    while not task.done():
        if await raw_request.is_disconnected():
            task.cancel()
            raise HTTPException(499, "Client disconnected")
        await asyncio.sleep(0.1)

    results = await task
    return CheckResponse(results=results)
