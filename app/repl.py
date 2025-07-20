import asyncio
import json
import os
import platform
import signal
import tempfile
from asyncio.subprocess import Process
from datetime import datetime
from uuid import UUID, uuid4

import psutil
from loguru import logger
from rich.console import Console
from rich.syntax import Syntax

from app.db import db
from app.errors import LeanError, ReplError
from app.models import ReplStatus
from app.prisma_client import prisma
from app.schemas import (
    CheckResponse,
    Command,
    CommandResponse,
    Diagnostics,
    Infotree,
    Snippet,
)
from app.settings import settings
from app.utils import is_blank

log_lock = asyncio.Lock()
console = Console(log_time_format="[%m/%d/%y %H:%M:%S]", force_terminal=True)


async def log_snippet(uuid: UUID, snippet_id: str, code: str) -> None:
    header = (
        f"\\[{uuid.hex[:8]}] Running snippet [bold magenta]{snippet_id}[/bold magenta]:"
    )
    syntax = Syntax(
        code or "<empty>",
        "lean",
        theme="solarized-dark",
        line_numbers=False,
        word_wrap=True,
    )

    async with log_lock:
        logger.info(header)
        console.log(syntax)


class Repl:
    def __init__(
        self,
        uuid: UUID,
        created_at: datetime,
        header: str = "",
        *,
        max_mem: int,
        max_uses: int,
    ) -> None:
        self.uuid = uuid
        self.header = header
        self.use_count = 0
        self.created_at = created_at

        # Stores the response received when running the import header.
        self.header_cmd_response: CheckResponse | None = None

        self.proc: Process | None = None
        self.error_file = tempfile.TemporaryFile("w+")
        self.max_memory_bytes = max_mem * 1024 * 1024
        self.max_uses = max_uses

        self._loop: asyncio.AbstractEventLoop | None = None

        # REPL statistics
        self.cpu_per_exec: dict[int, float] = {}
        self.mem_per_exec: dict[int, int] = {}

        # Vars that hold max CPU / mem usage per proof.
        self._cpu_max: float = 0.0  # CPU as a percentage of a single core
        self._mem_max: int = 0

        self._ps_proc: psutil.Process | None = None
        self._cpu_task: asyncio.Task[None] | None = None
        self._mem_task: asyncio.Task[None] | None = None

    @classmethod
    async def create(cls, header: str, max_uses: int, max_mem: int) -> "Repl":
        if db.connected:
            record = await prisma.repl.create(
                data={
                    "header": header,
                    "max_uses": max_uses,
                    "max_mem": max_mem,
                }
            )
            return cls(
                uuid=UUID(record.uuid),
                created_at=record.created_at,
                header=record.header,
                max_uses=record.max_uses,
                max_mem=record.max_mem,
            )
        return cls(
            uuid=uuid4(),
            created_at=datetime.now(),
            header=header,
            max_uses=max_uses,
            max_mem=max_mem,
        )

    @property
    def exhausted(self) -> bool:
        if self.header and not is_blank(self.header):
            # Header does not count towards uses.
            return self.use_count >= self.max_uses + 1
        return self.use_count >= self.max_uses

    async def start(self) -> None:
        # TODO: try/catch this bit and raise as REPL startup error.
        self._loop = asyncio.get_running_loop()

        def _preexec() -> None:
            import resource

            # Memory limit
            if platform.system() != "Darwin":  # Only for Linux
                resource.setrlimit(
                    resource.RLIMIT_AS, (self.max_memory_bytes, self.max_memory_bytes)
                )

            # No CPU limit on REPL, most Lean proofs take up to one core.
            # The adjustment variables are the maximum number of REPLs and the timeout.
            # See https://github.com/leanprover-community/repl/issues/91

            os.setsid()

        self.proc = await asyncio.create_subprocess_exec(
            "lake",
            "env",
            settings.repl_bin_path,
            cwd=settings.path_to_mathlib,
            env=os.environ,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            preexec_fn=_preexec,
        )

        self._ps_proc = psutil.Process(self.proc.pid)
        now = self._loop.time()
        self._last_check = now
        self._last_cpu_time = self._sum_cpu_times(self._ps_proc)

        self._cpu_max = 0.0
        self._mem_max = 0
        self._cpu_task = self._loop.create_task(self._cpu_monitor())
        self._mem_task = self._loop.create_task(self._mem_monitor())

        logger.info(f"\\[{self.uuid.hex[:8]}] Started")

    @staticmethod
    def _sum_cpu_times(proc: psutil.Process) -> float:
        total = proc.cpu_times().user + proc.cpu_times().system
        for c in proc.children(recursive=True):
            t = c.cpu_times()
            total += t.user + t.system
        return float(total)

    async def _cpu_monitor(self) -> None:
        while self.is_running and self._ps_proc and self._loop:
            await asyncio.sleep(1)
            now = self._loop.time()

            cur_cpu = self._sum_cpu_times(self._ps_proc)
            delta_cpu = cur_cpu - self._last_cpu_time
            delta_t = now - self._last_check
            usage_pct = (delta_cpu / delta_t) * 100
            self._cpu_max = max(self._cpu_max, usage_pct)
            self._last_cpu_time = cur_cpu
            self._last_check = now

    async def _mem_monitor(self) -> None:
        while self.is_running and self._ps_proc:
            await asyncio.sleep(1)
            total = self._ps_proc.memory_info().rss
            for child in self._ps_proc.children(recursive=True):
                total += child.memory_info().rss
            self._mem_max = max(self._mem_max, total)

    @property
    def is_running(self) -> bool:
        if not self.proc:
            return False
        return self.proc.returncode is None

    async def send_timeout(
        self,
        snippet: Snippet,
        timeout: float,
        is_header: bool = False,
        infotree: Infotree | None = None,
    ) -> CheckResponse:
        error = None
        cmd_response = None
        elapsed_time = 0.0
        diagnostics = Diagnostics(repl_uuid=str(self.uuid))

        try:
            cmd_response, elapsed_time, diagnostics = await asyncio.wait_for(
                self.send(snippet, is_header=is_header, infotree=infotree),
                timeout=timeout,
            )
        except TimeoutError as e:
            logger.error(
                "\\[{}] Lean REPL command timed out in {} seconds",
                self.uuid.hex[:8],
                timeout,
            )
            raise e
        except LeanError as e:
            logger.exception("Lean REPL error: %s", e)
            raise e
        except ReplError as e:
            logger.exception("REPL error: %s", e)
            raise e

        return CheckResponse(
            id=snippet.id,
            error=error,
            response=cmd_response,
            time=elapsed_time,
            diagnostics=diagnostics if len(diagnostics) > 0 else None,
        )

    async def send(
        self,
        snippet: Snippet,
        is_header: bool = False,
        infotree: Infotree | None = None,
    ) -> tuple[CommandResponse, float, Diagnostics]:
        await log_snippet(self.uuid, snippet.id, snippet.code)

        self._cpu_max = 0.0
        self._mem_max = 0

        if not self.proc or self.proc.returncode is not None:
            logger.error("REPL process not started or shut down")
            raise ReplError("REPL process not started or shut down")

        loop = self._loop or asyncio.get_running_loop()

        if self.proc.stdin is None:
            raise ReplError("stdin pipe not initialized")
        if self.proc.stdout is None:
            raise ReplError("stdout pipe not initialized")

        input: Command = {"cmd": snippet.code}

        if self.use_count != 0 and not is_header:  # remove is_header
            input["env"] = 0  # Always run on first environment

        if infotree:
            input["infotree"] = infotree

        payload = (json.dumps(input, ensure_ascii=False) + "\n\n").encode("utf-8")

        start = loop.time()
        logger.debug("Sending payload to REPL")

        try:
            self.proc.stdin.write(payload)
            await self.proc.stdin.drain()
        except BrokenPipeError:
            logger.error("Broken pipe while writing to REPL stdin")
            raise LeanError("Lean process broken pipe")
        except Exception as e:
            logger.error("Failed to write to REPL stdin: %s", e)
            raise LeanError("Failed to write to REPL stdin")

        logger.debug("Reading response from REPL stdout")
        raw = await self._read_response()
        elapsed = loop.time() - start

        logger.debug("Raw response from REPL: %r", raw)
        try:
            resp: CommandResponse = json.loads(raw)
        except json.JSONDecodeError:
            logger.error("JSON decode error: %r", raw)
            raise ReplError("JSON decode error")

        self.error_file.seek(0)
        err = self.error_file.read().strip()
        self.error_file.seek(0)
        self.error_file.truncate(0)
        if err:
            logger.error("Stderr: %s", err)
            raise LeanError(err)

        elapsed_time = round(elapsed, 6)
        diagnostics: Diagnostics = {
            "repl_uuid": str(self.uuid),
            "cpu_max": self._cpu_max,
            "memory_max": self._mem_max,
        }

        self.cpu_per_exec[self.use_count] = self._cpu_max
        self.mem_per_exec[self.use_count] = self._mem_max

        self.use_count += 1
        return resp, elapsed_time, diagnostics

    async def _read_response(self) -> bytes:
        if not self.proc or self.proc.stdout is None:
            logger.error("REPL process not started or stdout pipe not initialized")
            raise ReplError("REPL process not started or stdout pipe not initialized")

        lines: list[bytes] = []
        try:
            while True:
                chunk = await self.proc.stdout.readline()
                # EOF or blank line as terminator
                if not chunk or not chunk.strip():
                    break
                lines.append(chunk)
        except Exception as e:
            logger.error("Failed to read from REPL stdout: %s", e)
            raise LeanError("Failed to read from REPL stdout")
        return b"".join(lines)

    async def close(self) -> None:
        if self.proc:
            assert self.proc.stdin is not None, "stdin pipe not initialized"
            self.proc.stdin.close()
            os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
            await self.proc.wait()
            if self._cpu_task:
                self._cpu_task.cancel()
            if self._mem_task:
                self._mem_task.cancel()

            if db.connected:
                await prisma.repl.update(
                    where={"uuid": str(self.uuid)},
                    data={"status": ReplStatus.STOPPED},  # type: ignore
                )
