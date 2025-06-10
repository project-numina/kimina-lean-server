import asyncio
import gc
from server import server as srv
from server.leanrepl import LeanREPL


def test_repl_destroyed_when_memory_exceeds_limit(monkeypatch):
    # Configure settings so the memory check runs
    srv.settings.REPL_MEMORY_LIMIT_GB = 8
    srv.settings.REPL_MEMORY_CHECK_INTERVAL = 1

    closed = False

    # Stub LeanREPL to avoid starting external processes
    class DummyProcess:
        pid = 1
        def poll(self):
            return None

    def dummy_init(self):
        self.process = DummyProcess()
        self.run_command_total = 0
        self.header = None
        self.psutil_process = None
        self.children_processes = []

    def dummy_create_env(self, code, timeout=150):
        self.run_command_total += 1
        return {}

    def dummy_extend_env(self, context_id, code, timeout=150, infotree_type=None):
        self.run_command_total += 1
        return {}

    def dummy_close(self):
        nonlocal closed
        closed = True

    monkeypatch.setattr(LeanREPL, "__init__", dummy_init)
    monkeypatch.setattr(LeanREPL, "create_env", dummy_create_env)
    monkeypatch.setattr(LeanREPL, "extend_env", dummy_extend_env)
    monkeypatch.setattr(LeanREPL, "close", dummy_close)
    monkeypatch.setattr(LeanREPL, "exceeds_memory_limit", lambda self, limit: True)

    # Avoid interactions with repl cache
    monkeypatch.setattr(srv.repl_cache, "get", lambda header: (None, None))
    monkeypatch.setattr(srv.repl_cache, "put", lambda header, repl: None)
    monkeypatch.setattr(srv.repl_cache, "release", lambda header, id, repl: None)
    monkeypatch.setattr(srv.repl_cache, "destroy", lambda header, id, repl: None)

    proof = "import Mathlib\nexample : True := by trivial"
    code = srv.Code(custom_id="0", proof=proof)

    asyncio.run(srv.process_one_code_with_repl_fast(code, timeout=10, infotree_type=None, disable_cache=False))

    gc.collect()
    assert closed
