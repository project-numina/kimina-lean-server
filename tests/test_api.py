import asyncio
import importlib
import os
from uuid import uuid4

import pytest
from dotenv import load_dotenv
from fastapi.testclient import TestClient
from loguru import logger
from starlette import status
from utils import assert_json_equal

from app.schemas import CheckRequest, CheckResponse
from app.settings import settings


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"MAX_REPLS": 2, "MAX_USES": 2, "INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_repl_check_nat(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={"id": uuid, "code": "#check Nat"},
    ).model_dump()
    resp = client.post("check", json=payload)

    assert resp.status_code == status.HTTP_200_OK

    repl_response = {
        "messages": [
            {
                "severity": "info",
                "pos": {"line": 1, "column": 0},
                "endPos": {"line": 1, "column": 6},
                "data": "Nat : Type",
            }
        ],
        "env": 0,
    }

    expected = CheckResponse(
        id=uuid,
        response=repl_response,
        time=1.0,
    ).model_dump(exclude_none=True)

    assert_json_equal(resp.json(), expected, ignore_keys=["time"])


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_single_snippet(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={"id": uuid, "code": "#check Nat"},
    ).model_dump()
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_200_OK

    repl_response = {
        "messages": [
            {
                "severity": "info",
                "pos": {"line": 1, "column": 0},
                "endPos": {"line": 1, "column": 6},
                "data": "Nat : Type",
            }
        ],
        "env": 0,
    }
    expected = CheckResponse(
        id=uuid,
        response=repl_response,
        time=1.0,
    ).model_dump(exclude_none=True)

    assert_json_equal(resp.json(), expected, ignore_keys=["time"])


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {
            "MAX_REPLS": 1,
            "MAX_USES": 3,
            "INIT_REPLS": {},  # Ensure nothing preloaded
            "DATABASE_URL": None,
        },  # bumped max_uses to 3 because now header makes age increment
    ],
    indirect=True,
)
async def test_repl_mathlib(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={"id": uuid, "code": "import Mathlib\ndef f := 1"},
        debug=True,  # Enable debug to see diagnostics
    ).model_dump()
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_200_OK

    expected = {
        "id": uuid,
        "response": {
            "env": 1
        },  # Env is 1 because initialization with header bumps env value
    }

    assert_json_equal(resp.json(), expected, ignore_keys=["time", "diagnostics"])
    assert resp.json()["time"] < 15

    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={"id": uuid, "code": "import Mathlib\ndef f := 2"},
        debug=True,
    ).model_dump()
    resp1 = client.post("check", json=payload)
    assert resp1.status_code == status.HTTP_200_OK
    expected = {
        "id": uuid,
        "response": {"env": 2},
    }  # Env is 2 because max one repl and manager shared by all tests.

    assert_json_equal(resp1.json(), expected, ignore_keys=["time", "diagnostics"])

    assert resp1.json()["time"] < 1


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"MAX_REPLS": 1, "MAX_USES": 2, "INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_repl_timeout(client: TestClient) -> None:
    # Maximum of one REPL with two uses so that REPL can be reused.
    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={"id": uuid, "code": "import Mathlib"},
        timeout=1,  # Short timeout to trigger a timeout error
        debug=True,
    ).model_dump()
    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
    assert resp.status_code == status.HTTP_200_OK
    assert "diagnostics" in resp.json()
    assert "repl_uuid" in resp.json()["diagnostics"]

    logger.info(resp.json())

    used_repl_uuid = resp.json()["diagnostics"]["repl_uuid"]
    assert "timed out" in resp.json()["error"]

    await asyncio.sleep(5)  # 5 seconds should be enough to load Mathlib

    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={
            "id": uuid,
            "code": "theorem one_plus_one : 1 + 1 = 2 := by rfl",
        },
        timeout=5,
        debug=True,
    ).model_dump()
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_200_OK
    assert resp.json()["diagnostics"]["repl_uuid"] != used_repl_uuid

    expecteds = {
        "v4.19.0": {
            "id": uuid,
            "response": {
                "messages": [
                    {
                        "severity": "info",
                        "pos": {"line": 1, "column": 0},
                        "endPos": {"line": 1, "column": 42},
                        "data": "Goals accomplished!",
                    }
                ],
                "env": 0,
                "time": 0.450849,
            },
        },
        "v4.15.0": {
            "id": uuid,
            "response": {
                "env": 0,
            },
            "time": 0.450849,
        },
    }
    assert_json_equal(
        resp.json(),
        expected=expecteds[settings.LEAN_VERSION],
        ignore_keys=["time", "diagnostics"],
    )


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"MAX_REPLS": 1, "MAX_USES": 3, "INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,  # To parametrize fixture
)
async def test_repl_exhausted(client: TestClient) -> None:
    payload = CheckRequest(
        snippet={"id": "1", "code": "#check Nat"}, debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    repl_uuid = resp.json()["diagnostics"]["repl_uuid"]

    payload = CheckRequest(
        snippet={"id": "2", "code": "#check 0"}, debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    assert repl_uuid == resp.json()["diagnostics"]["repl_uuid"]

    payload = CheckRequest(
        snippet={"id": "3", "code": "#check 1"}, debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    assert repl_uuid == resp.json()["diagnostics"]["repl_uuid"]

    payload = CheckRequest(
        snippet={"id": "4", "code": "#check 2"}, debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    assert repl_uuid != resp.json()["diagnostics"]["repl_uuid"]


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_check_trailing_slash(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippet={"id": uuid, "code": "#check Nat"},
    ).model_dump()

    # Call with slash
    resp = client.post("check/", json=payload, follow_redirects=False)
    assert resp.status_code == status.HTTP_200_OK

    assert "messages" in resp.json()["response"]


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"MAX_REPLS": 1, "MAX_USES": 1, "INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_wrong_custom_id_on_check(client: TestClient) -> None:
    payload = {
        "snippet": {"custom_id": "check-nat", "code": "#check Nat"},
        "debug": True,
    }

    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_422_UNPROCESSABLE_ENTITY


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"MAX_REPLS": 1, "MAX_USES": 1, "INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_wrong_custom_id_on_checks(client: TestClient) -> None:
    payload = {
        "snippets": [
            {"custom_id": "check-nat", "code": "#check Nat"},
            {"custom_id": "check-deff1", "code": "import Mathlib\ndef f:= 1"},
            {
                "custom_id": "check-theo",
                "code": "import Mathlib\ntheorem onepp : 1 + 1 = 2 := by rfl",
            },
        ],
        "debug": True,
    }
    resp = client.post("checks", json=payload)
    assert resp.status_code == status.HTTP_422_UNPROCESSABLE_ENTITY


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"MAX_REPLS": 1, "MAX_USES": 1, "INIT_REPLS": {}, "DATABASE_URL": None},
    ],
    indirect=True,
)
async def test_infotree(client: TestClient) -> None:
    payload = {
        "snippet": {"id": "check-nat", "code": "theorem onepp : 1+1 = 2:= by rfl"},
        "infotree": "original",
    }
    resp = client.post("check", json=payload)
    expected = {
        "id": "check-nat",
        "time": 0.009034,
        "response": {
            "env": 5,
            "infotree": [
                {
                    "node": {
                        "stx": {
                            "range": {
                                "synthetic": False,
                                "start": {"line": 1, "column": 26},
                                "finish": {"line": 1, "column": 32},
                            },
                            "pp": "by rfl",
                        },
                        "name": "Lean.Parser.Term.byTactic",
                        "goalsBefore": ["⊢ 1 + 1 = 2"],
                        "goalsAfter": [],
                    },
                    "kind": "TacticInfo",
                    "children": [
                        {
                            "node": {
                                "stx": {
                                    "range": {
                                        "synthetic": False,
                                        "start": {"line": 1, "column": 26},
                                        "finish": {"line": 1, "column": 28},
                                    },
                                    "pp": "<failed to pretty print>",
                                },
                                "name": None,
                                "goalsBefore": ["⊢ 1 + 1 = 2"],
                                "goalsAfter": [],
                            },
                            "kind": "TacticInfo",
                            "children": [
                                {
                                    "node": {
                                        "stx": {
                                            "range": {
                                                "synthetic": False,
                                                "start": {"line": 1, "column": 29},
                                                "finish": {"line": 1, "column": 32},
                                            },
                                            "pp": "rfl",
                                        },
                                        "name": "Lean.Parser.Tactic.tacticSeq",
                                        "goalsBefore": ["⊢ 1 + 1 = 2"],
                                        "goalsAfter": [],
                                    },
                                    "kind": "TacticInfo",
                                    "children": [
                                        {
                                            "node": {
                                                "stx": {
                                                    "range": {
                                                        "synthetic": False,
                                                        "start": {
                                                            "line": 1,
                                                            "column": 29,
                                                        },
                                                        "finish": {
                                                            "line": 1,
                                                            "column": 32,
                                                        },
                                                    },
                                                    "pp": "rfl",
                                                },
                                                "name": "Lean.Parser.Tactic.tacticSeq1Indented",
                                                "goalsBefore": ["⊢ 1 + 1 = 2"],
                                                "goalsAfter": [],
                                            },
                                            "kind": "TacticInfo",
                                            "children": [
                                                {
                                                    "node": {
                                                        "stx": {
                                                            "range": {
                                                                "synthetic": False,
                                                                "start": {
                                                                    "line": 1,
                                                                    "column": 29,
                                                                },
                                                                "finish": {
                                                                    "line": 1,
                                                                    "column": 32,
                                                                },
                                                            },
                                                            "pp": "rfl",
                                                        },
                                                        "name": "Lean.Parser.Tactic.tacticRfl",
                                                        "goalsBefore": ["⊢ 1 + 1 = 2"],
                                                        "goalsAfter": [],
                                                    },
                                                    "kind": "TacticInfo",
                                                    "children": [],
                                                }
                                            ],
                                        }
                                    ],
                                }
                            ],
                        }
                    ],
                }
            ],
        },
    }

    assert_json_equal(resp.json(), expected, ignore_keys=["time", "env"])
