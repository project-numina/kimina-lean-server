import pytest

from server.errors import NoAvailableReplError
from server.manager import Manager


@pytest.mark.asyncio
async def test_lazy_lock_initialization() -> None:
    """Test that Lock and Condition are initialized lazily in async context."""
    manager = Manager(max_repls=1, max_repl_uses=1)
    
    # Initially, lock and condition should be None
    assert manager._lock is None
    assert manager._cond is None
    
    # After calling an async method, they should be initialized
    repl = await manager.get_repl()
    
    assert manager._lock is not None
    assert manager._cond is not None
    assert repl is not None
    
    await manager.release_repl(repl)


@pytest.mark.asyncio
async def test_get_repl() -> None:
    manager = Manager(max_repls=1, max_repl_uses=1)

    repl = await manager.get_repl()

    assert repl is not None

    await manager.release_repl(repl)


@pytest.mark.asyncio
async def test_exhausted() -> None:
    manager = Manager(max_repls=0, max_repl_uses=1)

    with pytest.raises(NoAvailableReplError):
        await manager.get_repl(timeout=3)


@pytest.mark.asyncio
async def test_get_repl_with_reuse() -> None:
    manager = Manager(max_repls=1, max_repl_uses=3)

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
