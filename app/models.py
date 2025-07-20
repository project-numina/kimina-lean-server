from __future__ import annotations

from datetime import datetime
from enum import Enum
from typing import Any
from uuid import UUID

from pydantic import BaseModel


class ReplStatus(str, Enum):
    RUNNING = "RUNNING"
    STOPPED = "STOPPED"


class Repl(BaseModel):
    uuid: UUID
    created_at: datetime
    max_uses: int
    max_mem: int
    header: str
    status: ReplStatus


class Proof(BaseModel):
    uuid: UUID
    id: str
    code: str
    diagnostics: dict[str, Any] | None = None
    response: dict[str, Any] | None = None
    time: float = 0.0
    error: str | None = None
    repl_uuid: UUID
