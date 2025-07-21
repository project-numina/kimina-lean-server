from fastapi import APIRouter

router = APIRouter()


# TODO: add stats endpoint in webapp typescript
@router.get("/", include_in_schema=False)
async def read_root() -> dict[str, str]:
    return {"status": "ok"}


@router.get("/health")
@router.get("/health/", include_in_schema=False)
async def get_health() -> dict[str, str]:
    return {"status": "ok"}
