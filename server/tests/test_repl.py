from typing import AsyncGenerator

import pytest

from app.repl import Repl


@pytest.fixture
async def repl() -> AsyncGenerator[Repl, None]:
    repl_instance = await Repl.create("", 1, 8192)
    yield repl_instance
    await repl_instance.close()


@pytest.mark.asyncio
async def test_start(repl: Repl) -> None:
    assert repl.proc is None

    await repl.start()

    assert repl.proc is not None
