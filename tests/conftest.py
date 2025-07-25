import difflib
import json
from typing import Any, Literal

import pytest
from _pytest.fixtures import FixtureRequest
from fastapi.testclient import TestClient

from server.main import create_app
from server.settings import Environment, Settings


@pytest.fixture(params=[])
def client(request: FixtureRequest) -> TestClient:
    defaults = {
        "max_repls": 5,
        "max_repl_uses": 10,
        "init_repls": {},
        "database_url": None,
        "environment": Environment.prod,
    }

    overrides = {**defaults, **getattr(request, "param", {})}

    s = Settings(_env_file=None)
    for k, v in overrides.items():
        setattr(s, k, v)
    app = create_app(s)

    with TestClient(app, base_url="http://testserver/api") as client:
        yield client


@pytest.fixture(
    params=[
        {
            "max_repls": 5,
            "max_repl_uses": 10,
            "init_repls": {},
            "database_url": None,
            "environment": Environment.prod,
        },
    ]
)
def root_client(request: FixtureRequest) -> TestClient:
    overrides = getattr(request, "param", {})
    s = Settings(_env_file=None)
    for k, v in overrides.items():
        setattr(s, k, v)
    app = create_app(s)

    with TestClient(app, base_url="http://testserver") as root_client:
        yield root_client


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption(
        "--perfs-rows",
        action="store",
        default=10,
        type=int,
        help="Number of proofs to run in performance tests (default: 10)",
    )
    parser.addoption(
        "--perfs-shuffle",
        action="store_true",
        default=False,
        help="Shuffle dataset rows for performance tests (default: False)",
    )


@pytest.fixture(scope="session")
def perf_rows(request: pytest.FixtureRequest) -> int:
    return int(request.config.getoption("--perfs-rows"))


@pytest.fixture(scope="session")
def perf_shuffle(request: pytest.FixtureRequest) -> bool:
    return bool(request.config.getoption("--perfs-shuffle"))


def pytest_assertrepr_compare(
    op: Literal["=="], left: Any, right: Any
) -> list[str] | None:
    if op == "==" and isinstance(left, dict) and isinstance(right, dict):
        l = json.dumps(left, indent=2, sort_keys=True).splitlines(keepends=True)
        r = json.dumps(right, indent=2, sort_keys=True).splitlines(keepends=True)
        diff = difflib.unified_diff(l, r, fromfile="actual", tofile="expected")
        return [""] + list(diff)
    return None
