from fastapi import APIRouter, HTTPException, status
import psutil
from pydantic import BaseModel
from .config import settings

router = APIRouter()


class HealthResponse(BaseModel):
    status: str
    version: str
    cpu_usage: float | None
    memory_usage: float | None


@router.get("/health", response_model=HealthResponse)
async def health_check():
    service_healthy = True
    cpu_usage = None
    memory_usage = None
    version = "unknown"

    try:
        # Read the Lean version from the file
        with open("version_info.txt", "r") as f:
            version = f.read().strip()
    except Exception as e:
        service_healthy = False
    
    # check cpu usage
    if settings.HEALTHCHECK_CPU_USAGE_THRESHOLD is not None:
        try:
            cpu_usage = psutil.cpu_percent(interval=1)
            if cpu_usage > settings.HEALTHCHECK_CPU_USAGE_THRESHOLD:
                service_healthy = False
        except Exception as e:
            service_healthy = False

    # check memory usage
    if settings.HEALTHCHECK_MEMORY_USAGE_THRESHOLD is not None:
        try:
            memory_usage = psutil.virtual_memory().percent
            if memory_usage > settings.HEALTHCHECK_MEMORY_USAGE_THRESHOLD:
                service_healthy = False
        except Exception as e:
            service_healthy = False

    if service_healthy:
        return {"status": "healthy", "version": version, "cpu_usage": cpu_usage, "memory_usage": memory_usage}
    else:
        raise HTTPException(
            status_code=status.HTTP_503_SERVICE_UNAVAILABLE,
            detail=f"Service unhealthy: lean_version={version}, cpu_usage={cpu_usage}, memory_usage={memory_usage}",
        )
