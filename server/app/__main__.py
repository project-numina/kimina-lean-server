import uvicorn

from app.main import app
from app.settings import Environment, settings

uvicorn.run(
    app,
    host=settings.HOST,
    port=settings.PORT,
    backlog=4096,  # On Google Cloud VMs: `cat /proc/sys/net/core/somaxconn` = 4096
    use_colors=settings.ENVIRONMENT != Environment.production,
)
