import pytest

from app.errors import NoAvailableReplError
from app.manager import Manager


@pytest.mark.asyncio
async def test_get_repl() -> None:
    manager = Manager(max_repls=1, max_uses=1)

    repl = await manager.get_repl()

    assert repl is not None

    await manager.release_repl(repl)


@pytest.mark.asyncio
async def test_exhausted() -> None:
    manager = Manager(max_repls=0, max_uses=1)

    with pytest.raises(TimeoutError):
        await manager.get_repl(timeout=3)


@pytest.mark.asyncio
async def test_get_repl_with_reuse() -> None:
    manager = Manager(max_repls=1, max_uses=3)

    repl1 = await manager.get_repl()
    assert repl1 is not None

    await manager.release_repl(repl1)

    repl2 = await manager.get_repl()
    assert repl2.uuid == repl1.uuid

    await manager.release_repl(repl2)

    repl3 = await manager.get_repl(reuse=False)

    assert repl3.uuid != repl1.uuid

    assert manager._busy == {repl3}
    assert manager._free == []
