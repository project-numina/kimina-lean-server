import pytest

from client import Lean4Client


@pytest.fixture(scope="module", autouse=True)
def lean4client():
    client = Lean4Client(base_url="http://127.0.0.1:12332")
    return client
