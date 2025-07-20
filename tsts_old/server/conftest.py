import pytest
from fastapi.testclient import TestClient

from server import app


@pytest.fixture(scope="module", autouse=True)
def test_client():
    tc = TestClient(app)
    yield tc
