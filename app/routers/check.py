import asyncio
import json
from typing import cast

from fastapi import APIRouter, Depends, HTTPException, Request
from loguru import logger

from app.auth import require_key
from app.db import db
from app.errors import NoAvailableReplError
from app.manager import Manager
from app.prisma_client import prisma
from app.schemas import CheckRequest, CheckResponse, ChecksRequest, Infotree, Snippet
from app.split import split_snippet

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
) -> list[CheckResponse]:
    async def run_one(snippet: Snippet) -> CheckResponse:
        header, body = split_snippet(snippet.code)
        try:
            repl = await manager.get_repl(header, snippet.id, reuse=reuse)
        except NoAvailableReplError:
            logger.exception("No available REPLs")
            raise HTTPException(429, "No available REPLs") from None
        except Exception as e:
            logger.exception("Failed to get REPL: %s", e)
            raise HTTPException(500, str(e)) from e

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
            return CheckResponse(
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
            return CheckResponse(
                id=snippet.id,
                error=error,
                time=timeout,
                diagnostics={
                    "repl_uuid": uuid_hex,
                },
            )
        except Exception as e:
            logger.exception("Snippet execution failed")
            await manager.destroy_repl(repl)
            raise HTTPException(500, str(e)) from e
        else:
            logger.info(
                "[{}] Result for [bold magenta]{}[/bold magenta] body →\n{}",
                repl.uuid.hex[:8],
                snippet.id,
                json.dumps(resp.model_dump(exclude_none=True), indent=2),
            )
            await manager.release_repl(repl)
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

    return await asyncio.gather(*(run_one(s) for s in snippets))


@router.post(
    "/checks",
    response_model=list[CheckResponse],
    response_model_exclude_none=True,
)
@router.post(
    "/checks/",
    response_model=list[CheckResponse],
    response_model_exclude_none=True,
    include_in_schema=False,  # To not clutter OpenAPI spec.
)
async def check_batch(
    request: ChecksRequest,
    manager: Manager = Depends(get_manager),
) -> list[CheckResponse]:
    return await run_checks(
        request.snippets,
        float(request.timeout),
        request.debug,
        manager,
        request.reuse,
        request.infotree,
    )


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
async def check_single(
    request: CheckRequest,
    manager: Manager = Depends(get_manager),
    _: str = Depends(require_key),
) -> CheckResponse:
    resp_list = await run_checks(
        [request.snippet],
        float(request.timeout),
        request.debug,
        manager,
        request.reuse,
        request.infotree,
    )
    return resp_list[0]
