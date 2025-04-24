import uvicorn
from .server import app, settings

uvicorn.run(
    app,
    host=settings.HOST,
    port=settings.PORT,
    log_level=settings.LOG_LEVEL.lower(),
    backlog=100000,
)
