from fastapi import APIRouter, Depends
from kimina import (
    BackwardResponse,
    CommandResponse,
    Error,
    ExtendedCommandResponse,
    ExtendedError,
    Snippet,
    VerifyRequestBody,
    VerifyResponse,
)

from ..auth import require_key
from ..manager import Manager
from .check import get_manager, run_checks

router = APIRouter()


@router.post(
    "/one_pass_verify_batch",
    response_model=VerifyResponse,
    response_model_exclude_none=True,
)
@router.post("/verify", response_model=VerifyResponse, response_model_exclude_none=True)
async def one_pass_verify_batch(
    body: VerifyRequestBody,
    manager: Manager = Depends(get_manager),
    _: str = Depends(require_key),
) -> VerifyResponse:
    """Backward compatible endpoint: accepts both 'proof' / 'code' fields."""

    codes = body.codes
    snippets = [
        Snippet(id=str(code.custom_id), code=code.get_proof_content()) for code in codes
    ]

    timeout = body.timeout
    debug = False
    reuse = not body.disable_cache
    infotree = body.infotree_type

    check_responses = await run_checks(
        snippets, float(timeout), debug, manager, reuse, infotree
    )

    results: list[BackwardResponse] = []

    for check_response in check_responses:
        extended_response = extend(check_response.response)

        result = BackwardResponse(
            custom_id=check_response.id,
            error=check_response.error,
            response=extended_response,
        )
        results.append(result)

    return VerifyResponse(results=results)


def extend(
    response: CommandResponse | Error | None,
) -> ExtendedCommandResponse | ExtendedError | None:
    if response is None:
        return None
    elif "message" in response:
        return ExtendedError(
            message=response.get("message", ""),
            time=response.get("time", None),
        )
    else:
        return ExtendedCommandResponse(
            env=response.get("env", None),
            messages=response.get("messages", None),
            sorries=response.get("sorries", None),
            tactics=response.get("tactics", None),
            infotree=response.get("infotree", None),
            time=response.get("time", None),
        )
