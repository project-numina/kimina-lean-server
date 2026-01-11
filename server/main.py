import textwrap
import threading
from contextlib import asynccontextmanager
from typing import Any, AsyncGenerator, Awaitable, Callable

from fastapi import FastAPI, Request, Response
from loguru import logger
from pydantic.json_schema import GenerateJsonSchema

from .__version__ import __version__
from .logger import setup_logging
from .manager import Manager
from .routers.backward import router as backward_router
from .routers.check import router as check_router
from .routers.health import router as health_router
from .settings import Environment, Settings


def no_sort(self: GenerateJsonSchema, value: Any, parent_key: Any = None) -> Any:
    return value


setattr(GenerateJsonSchema, "sort", no_sort)


def create_app(settings: Settings) -> FastAPI:
    @asynccontextmanager
    async def lifespan(app: FastAPI) -> AsyncGenerator[None, None]:
        logger.info(
            "Running Kimina Lean Server [bold]'v{}'[/bold] in [bold]{}[/bold] mode with Lean version: '{}'",
            __version__,
            settings.environment.value,
            settings.lean_version,
        )

        manager = Manager(
            max_repls=settings.max_repls,
            max_repl_uses=settings.max_repl_uses,
            max_repl_mem=settings.max_repl_mem,
            init_repls=settings.init_repls,
        )
        app.state.manager = manager
        await app.state.manager.initialize_repls()

        if settings.environment == Environment.dev:
            threading.Timer(
                0.1,
                lambda: logger.info(
                    "Try me with:\n"
                    + textwrap.indent(
                        "curl --request POST \\\n"
                        "  --url http://localhost:8000/api/check \\\n"
                        "  --header 'Content-Type: application/json' \\\n"
                        "  --data '{"
                        '"snippets":[{"id":"check-nat-test","code":"#check Nat"}]'
                        "}' | jq\n",
                        "  ",
                    )
                ),
            ).start()

        yield

        await app.state.manager.cleanup()

    app = FastAPI(
        lifespan=lifespan,
        title="Kimina Lean Server API",
        description="Check Lean 4 snippets at scale via REPL",
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


settings = Settings()
setup_logging()
app = create_app(settings)


@app.middleware("http")
async def log_requests(
    request: Request, call_next: Callable[[Request], Awaitable[Response]]
) -> Response:
    logger.bind(path=request.url.path, method=request.method).info("→ request")
    response = await call_next(request)
    logger.bind(status_code=response.status_code).info("← response")
    return response
