from datetime import datetime
import logging
import sys
import uvicorn
from loguru import logger
from .server import app, settings

time_stamp = datetime.now().strftime("%Y%m%d-%H%M%S")

def register_logging(app=None) -> None:
    level = settings.LOG_LEVEL
    path = f"{settings.LOG_DIR}/server_{time_stamp}.log"
    retention = "1 days"

    logging.root.handlers = [InterceptHandler()]
    logging.root.setLevel(level)

    # remove every other logger's handlers
    # and propagate to root logger
    for name in logging.root.manager.loggerDict.keys():
        logging.getLogger(name).handlers = []
        logging.getLogger(name).propagate = True

    # configure loguru
    logger.configure(
        handlers=[
            {"sink": sys.stdout},
            {"sink": path, "rotation": "00:00", "retention": retention},
        ]
    )


class InterceptHandler(logging.Handler):
    def emit(self, record: logging.LogRecord) -> None:
        try:
            level = logger.level(record.levelname).name
        except ValueError:
            level = record.levelno

        # Simplify the depth calculation. You may need to adjust this value.
        depth = 6  # This is an example value; you may need to adjust it based on your actual logging calls

        logger.opt(depth=depth, exception=record.exc_info).log(
            level, record.getMessage()
        )

register_logging(app)

uvicorn.run(
    app,
    host=settings.HOST,
    port=settings.PORT,
    backlog=100000,
    log_config=None,
)