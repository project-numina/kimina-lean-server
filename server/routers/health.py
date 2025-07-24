from fastapi import APIRouter, Depends

from ..auth import require_key

router = APIRouter()


# TODO: add stats endpoint in webapp typescript


@router.get("/health")
@router.get("/health/", include_in_schema=False)
@router.get("/", include_in_schema=False)
async def get_health(_: str = Depends(require_key)) -> dict[str, str]:
    return {"status": "ok"}
