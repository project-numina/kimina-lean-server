import logging
from types import FrameType
from typing import Any

import uvicorn
from loguru import logger

from .main import app
from .settings import Environment, settings


class InterceptHandler(logging.Handler):
    def emit(self, record: Any) -> None:
        try:
            lvl = logger.level(record.levelname).name
        except ValueError:
            lvl = record.levelno
        frame: FrameType | None = logging.currentframe()
        depth = 2
        while frame and frame.f_code.co_filename == logging.__file__:
            frame = frame.f_back
            depth += 1

        logger.opt(depth=depth, exception=record.exc_info).log(lvl, record.getMessage())


if __name__ == "__main__":
    logging.basicConfig(handlers=[InterceptHandler()], level=0, force=True)

    for name in ("uvicorn", "uvicorn.error", "uvicorn.access"):
        logging.getLogger(name).handlers = []
        logging.getLogger(name).propagate = True

    uvicorn.run(
        app,
        host=settings.host,
        port=settings.port,
        backlog=4096,  # On Google Cloud VMs: `cat /proc/sys/net/core/somaxconn` = 4096
        use_colors=settings.environment != Environment.prod,
        log_config=None,
    )
