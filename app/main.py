import json
import shutil
from contextlib import asynccontextmanager
from importlib.metadata import PackageNotFoundError, version
from typing import Any, AsyncGenerator

from fastapi import FastAPI
from loguru import logger
from pydantic.json_schema import GenerateJsonSchema
from rich.console import Console
from rich.logging import RichHandler

from app.db import db
from app.manager import Manager
from app.routers.backward import router as backward_router
from app.routers.check import router as check_router
from app.routers.health import router as health_router
from app.settings import Settings

try:
    __version__ = version("kimina-lean-server")
except PackageNotFoundError:
    __version__ = "0.0.0"  # fallback for local dev


def no_sort(self: GenerateJsonSchema, value: Any, parent_key: Any = None) -> Any:
    return value


setattr(GenerateJsonSchema, "sort", no_sort)


# @app.on_event("startup")
# def on_startup():
#     seed_key()


def create_app(settings: Settings) -> FastAPI:
    @asynccontextmanager
    async def lifespan(app: FastAPI) -> AsyncGenerator[None, None]:
        if settings.DATABASE_URL:
            try:
                await db.connect()
                logger.info("DB connected: %s", db.connected)
            except Exception as e:
                logger.exception("Failed to connect to database: %s", e)

        manager = Manager(
            max_repls=settings.MAX_REPLS,
            max_uses=settings.MAX_USES,
            max_mem=settings.MAX_MEM,
            init_repls=settings.INIT_REPLS,
        )
        app.state.manager = manager
        await app.state.manager.initialize_repls()

        yield

        await app.state.manager.cleanup()
        await db.disconnect()

        logger.info("Disconnected from database")

    app = FastAPI(
        lifespan=lifespan,
        title="Lean 4 Proof-Check API",
        description="Submit Lean 4 snippets to be checked/validated via REPL",
        version=__version__,
        openapi_url="/api/openapi.json",
        docs_url="/docs",
        redoc_url="/redoc",
        logger=logger,
    )

    app.include_router(
        check_router,
        prefix="/api",
        tags=["check"],
    )
    app.include_router(
        health_router,
        tags=["health"],
    )
    app.include_router(
        backward_router,
        tags=["backward"],
    )
    return app


def setup_logging(settings: Settings) -> None:
    logger.remove()

    if settings.ENVIRONMENT.lower() == "production":

        def gcp_formatter(message: Any) -> None:
            record = message.record
            log_entry = {
                "severity": record["level"].name,
                "message": record["message"],
                "time": record["time"].isoformat(),
                # Optional: Add more structured data as needed
                "logging.googleapis.com/sourceLocation": {
                    "file": record["file"].name,
                    "line": record["line"],
                    "function": record["function"],
                },
            }
            # The entire log entry must be a single JSON string
            # on one line for Google Cloud Logging to parse it correctly.
            print(json.dumps(log_entry))

        logger.add(
            gcp_formatter,
            level=settings.LOG_LEVEL,
            format="{message}",
        )
    else:
        # Your existing RichHandler for local development
        terminal_width, _ = shutil.get_terminal_size()
        logger.add(
            RichHandler(
                console=Console(width=terminal_width), show_time=True, markup=True
            ),
            colorize=True,
            level=settings.LOG_LEVEL,
            format="{message}",
            backtrace=True,
            diagnose=True,
        )


settings = Settings()

terminal_width, _ = shutil.get_terminal_size()

setup_logging(settings)
app = create_app(settings)
