from fastapi import APIRouter, Depends

from app.manager import Manager
from app.routers.check import get_manager, run_checks
from app.schemas import BackwardResponse, Snippet, VerifyRequestBody, VerifyResponse

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
    # access: require_access_dep, # TODO: later implement authentication
) -> VerifyResponse:
    """Backward compatible endpoint: accepts both 'proof' / 'code' fields."""

    codes = body.codes
    snippets = [
        Snippet(id=str(code.custom_id), code=code.get_proof_content() or "no-id")
        for code in codes
    ]

    timeout = body.timeout
    debug = False
    reuse = not body.disable_cache
    infotree = body.infotree_type

    checks_response = await run_checks(
        snippets, float(timeout), debug, manager, reuse, infotree
    )

    results: list[BackwardResponse] = []

    for resp in checks_response:
        response = None
        if resp.response is not None:
            response = dict(resp.response)
            response["time"] = resp.time

        result = BackwardResponse(
            custom_id=resp.id,
            error=resp.error,
            response=response,
        )
        results.append(result)

    return VerifyResponse(results=results)
