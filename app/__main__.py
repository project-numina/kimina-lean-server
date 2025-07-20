import uvicorn

from app.main import app
from app.settings import settings

uvicorn.run(
    app,
    host=settings.HOST,
    port=settings.PORT,
    backlog=100000,
    use_colors=settings.ENVIRONMENT.lower() != "production",
)
