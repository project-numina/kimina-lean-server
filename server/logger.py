from google.auth.exceptions import DefaultCredentialsError
from google.cloud.logging import Client as GCPClient
from google.cloud.logging.handlers import CloudLoggingHandler
from loguru import logger
from rich.console import Console
from rich.logging import RichHandler
from rich.traceback import install

from .settings import Environment, settings

console = Console()


def setup_logging() -> None:
    logger.remove()
    install(show_locals=True)

    if settings.environment == Environment.prod:
        try:
            gcp_client = GCPClient()
            gcp_handler = CloudLoggingHandler(gcp_client)
            logger.add(gcp_handler, level="INFO", serialize=True)
        except DefaultCredentialsError:
            logger.add(
                RichHandler(
                    console=console,
                    show_time=False,
                    markup=True,
                    show_level=True,
                    rich_tracebacks=True,
                ),
                colorize=True,
                level=settings.log_level,
                format="{message}",
                backtrace=True,
                diagnose=True,
            )
    else:
        logger.add(
            RichHandler(
                console=console,
                show_time=False,
                markup=True,
                show_level=True,
                rich_tracebacks=True,
            ),
            colorize=True,
            level=settings.log_level,
            format="{message}",
            backtrace=True,
            diagnose=True,
        )


# def gcp_formatter(message: Any) -> None:
#     record = message.record
#     log_entry = {
#         "severity": record["level"].name,
#         "message": record["message"],
#         "time": record["time"].isoformat(),
#         # Optional: Add more structured data as needed
#         "logging.googleapis.com/sourceLocation": {
#             "file": record["file"].name,
#             "line": record["line"],
#             "function": record["function"],
#         },
#     }
#     # The entire log entry must be a single JSON string
#     # on one line for Google Cloud Logging to parse it correctly.
#     print(json.dumps(log_entry))

# logger.add(
#     gcp_formatter,
#     level=settings.log_level,
#     format="{message}",
# )
