from fastapi import APIRouter, HTTPException, status
from pydantic import BaseModel

router = APIRouter()


class HealthResponse(BaseModel):
    status: str
    version: str


@router.get("/health", response_model=HealthResponse)
async def health_check():
    try:
        # Read the Lean version from the file
        with open("version_info.txt", "r") as f:
            version = f.read().strip()

        return {"status": "healthy", "version": version}
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_503_SERVICE_UNAVAILABLE,
            detail=f"Service unhealthy: {str(e)}",
        )
