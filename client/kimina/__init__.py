import logging
import sys
from typing import Any

from .async_client import AsyncKimina
from .models import (
    BackwardResponse,
    CheckRequest,
    CheckResponse,
    Code,
    Command,
    CommandResponse,
    Diagnostics,
    Error,
    ExtendedCommandResponse,
    ExtendedError,
    Infotree,
    Message,
    ReplRequest,
    ReplResponse,
    Snippet,
    VerifyRequestBody,
    VerifyResponse,
)
from .sync_client import Kimina

__all__ = [
    "AsyncKimina",
    "BackwardResponse",
    "ReplRequest",
    "ReplResponse",
    "CheckRequest",
    "CheckResponse",
    "Code",
    "Command",
    "CommandResponse",
    "Diagnostics",
    "Error",
    "ExtendedCommandResponse",
    "ExtendedError",
    "Infotree",
    "Kimina",
    "Message",
    "Snippet",
    "VerifyRequestBody",
    "VerifyResponse",
]

from colorama import Fore, Style, init

init(autoreset=True)


class ColorFormatter(logging.Formatter):
    COLORS = {
        logging.DEBUG: Fore.CYAN,
        logging.INFO: Fore.WHITE,
        logging.WARNING: Fore.YELLOW,
        logging.ERROR: Fore.RED,
        logging.CRITICAL: Fore.MAGENTA + Style.BRIGHT,
    }

    def format(self, record: Any) -> str:
        log_color = self.COLORS.get(record.levelno, "")
        message = super().format(record)
        return f"{log_color}{message}{Style.RESET_ALL}"


logger = logging.getLogger("kimina")

if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = ColorFormatter("%(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)
