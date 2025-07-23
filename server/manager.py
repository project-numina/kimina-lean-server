from __future__ import annotations

import asyncio
import json
from datetime import datetime
from time import time

from kimina import CheckResponse, Snippet
from loguru import logger

from .errors import NoAvailableReplError, ReplError
from .repl import Repl
from .settings import settings
from .utils import is_blank


class Manager:
    def __init__(
        self,
        *,
        max_repls: int = settings.max_repls,
        max_repl_uses: int = settings.max_repl_uses,
        max_repl_mem: int = settings.max_repl_mem,
        init_repls: dict[str, int] = settings.init_repls,
    ) -> None:

        self.max_repls = max_repls
        self.max_repl_uses = max_repl_uses
        self.max_repl_mem = max_repl_mem
        self.init_repls = init_repls

        self._lock = asyncio.Lock()
        self._cond = asyncio.Condition(self._lock)
        self._free: list[Repl] = []
        self._busy: set[Repl] = set()

        logger.info(
            "REPL manager initialized with: MAX_REPLS={}, MAX_REPL_USES={}, MAX_REPL_MEM={} MB",
            max_repls,
            max_repl_uses,
            max_repl_mem,
        )

    async def initialize_repls(self) -> None:
        if len(self.init_repls) == 0:
            return
        if self.max_repls < sum(self.init_repls.values()):
            raise ValueError(
                f"Cannot initialize REPLs: Σ (INIT_REPLS values) = {sum(self.init_repls.values())} > {self.max_repls} = MAX_REPLS"
            )
        initialized_repls: list[Repl] = []
        for header, count in self.init_repls.items():
            for _ in range(count):
                initialized_repls.append(await self.get_repl(header=header))

        async def _prep_and_release(repl: Repl) -> None:
            # All initialized imports should finish in 60 seconds.
            await self.prep(repl, snippet_id="init", timeout=60, debug=False)
            await self.release_repl(repl)

        await asyncio.gather(*(_prep_and_release(r) for r in initialized_repls))

        logger.info(f"Initialized REPLs with: {json.dumps(self.init_repls, indent=2)}")

    async def get_repl(
        self,
        header: str = "",
        snippet_id: str = "",
        timeout: float = settings.max_wait,
        reuse: bool = True,
    ) -> Repl:
        """
        Async-safe way to get a `Repl` instance for a given header.
        Immediately raises an Exception if not possible.
        """
        deadline = time() + timeout
        async with self._cond:
            while True:
                logger.info(
                    f"# Free = {len(self._free)} | # Busy = {len(self._busy)} | # Max = {self.max_repls}"
                )
                if reuse:
                    for i, r in enumerate(self._free):
                        if (
                            r.header == header
                        ):  # repl shouldn't be exhausted (max uses to check)
                            repl = self._free.pop(i)
                            self._busy.add(repl)

                            logger.info(
                                f"\\[{repl.uuid.hex[:8]}] Reusing ({"started" if repl.is_running else "non-started"}) REPL for {snippet_id}"
                            )
                            return repl
                total = len(self._free) + len(self._busy)
                if total < self.max_repls:
                    return await self.start_new(header)

                if self._free:
                    oldest = min(
                        self._free, key=lambda r: r.last_check_at
                    )  # Use the one that's been around the longest
                    self._free.remove(oldest)
                    uuid = oldest.uuid
                    logger.info(f"Destroying REPL {uuid.hex[:8]}")
                    await oldest.close()
                    del oldest
                    logger.info(f"Destroyed REPL {uuid.hex[:8]}")
                    return await self.start_new(header)

                remaining = deadline - time()
                if remaining <= 0:
                    raise NoAvailableReplError(f"Timed out after {timeout}s")

                await asyncio.wait_for(self._cond.wait(), timeout=remaining)

    async def destroy_repl(self, repl: Repl) -> None:
        async with self._cond:
            uuid = repl.uuid
            self._busy.discard(repl)
            if repl in self._free:
                self._free.remove(repl)
            logger.info(f"Destroying REPL {uuid.hex[:8]}")
            await repl.close()
            del repl
            logger.info(f"Destroyed REPL {uuid.hex[:8]}")

    async def release_repl(self, repl: Repl) -> None:
        async with self._cond:
            if repl not in self._busy:
                logger.error(
                    f"Attempted to release a REPL that is not busy: {repl.uuid.hex[:8]}"
                )
                return

            if repl.exhausted:
                uuid = repl.uuid
                logger.info(f"REPL {uuid.hex[:8]} is exhausted, closing it")
                self._busy.discard(repl)

                await repl.close()
                del repl
                logger.info(f"Deleted REPL {uuid.hex[:8]}")
                return
            self._busy.remove(repl)
            self._free.append(repl)
            repl.last_check_at = datetime.now()
            logger.info(f"\\[{repl.uuid.hex[:8]}] Released!")
            self._cond.notify(1)

    async def start_new(self, header: str) -> Repl:
        repl = await Repl.create(
            header, max_repl_uses=self.max_repl_uses, max_repl_mem=self.max_repl_mem
        )
        self._busy.add(repl)
        return repl

    async def cleanup(self) -> None:
        async with self._cond:
            logger.info("Cleaning up REPL manager...")
            for repl in self._free:
                await repl.close()
                del repl
            self._free.clear()

            for repl in self._busy:
                await repl.close()
                del repl
            self._busy.clear()

            logger.info("REPL manager cleaned up!")
        pass

    async def prep(
        self, repl: Repl, snippet_id: str, timeout: float, debug: bool
    ) -> CheckResponse | None:
        if repl.is_running:
            return None

        try:
            await repl.start()
        except Exception as e:
            logger.exception("Failed to start REPL: %s", e)
            raise ReplError("Failed to start REPL") from e

        if not is_blank(repl.header):
            try:
                cmd_response = await repl.send_timeout(
                    Snippet(id=f"{snippet_id}-header", code=repl.header),
                    timeout=timeout,
                    is_header=True,
                )
            except TimeoutError as e:
                logger.error("Header command timed out")
                raise e
            except Exception as e:
                logger.error("Failed to run header on REPL")
                raise ReplError("Failed to run header on REPL") from e

            if not debug:
                cmd_response.diagnostics = None

            if cmd_response.error:
                logger.error(f"Header command failed: {cmd_response.error}")
                await self.destroy_repl(repl)

            repl.header_cmd_response = cmd_response

            return cmd_response
        return repl.header_cmd_response
