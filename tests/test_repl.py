from typing import AsyncGenerator

import psutil
import pytest
from lean_verification_client import Snippet

from server.repl import Repl


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


@pytest.mark.asyncio
async def test_create_close_multiple() -> None:
    for _ in range(3):
        repl = await Repl.create("", 1, 8192)

        await repl.start()
        assert repl.proc is not None
        pid = repl.proc.pid
        assert pid is not None

        # Run a simple command
        response = await repl.send_timeout(
            Snippet(id="test", code="def f := 2"), timeout=10
        )

        assert response.error is None

        # Close the REPL
        await repl.close()

        # Verify the process has terminated
        assert not psutil.pid_exists(pid)


# @pytest.mark.asyncio
# @pytest.mark.skip
# async def test_del_calls_close(repl: Repl) -> None:
#     await repl.start()

#     assert repl.proc is not None
#     pid = repl.proc.pid

#     # Verify the process is running
#     assert psutil.pid_exists(pid)

#     # Delete the repl instance
#     del repl

#     # Give it 1 second to terminate
#     await asyncio.sleep(10)

#     # Verify the process has terminated
#     assert not psutil.pid_exists(pid), "Process did not terminate after __del__"
