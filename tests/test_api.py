import asyncio
from uuid import uuid4

import pytest
from fastapi.testclient import TestClient
from kimina import (
    CheckRequest,
    CheckResponse,
    CommandResponse,
    Infotree,
    Message,
    ReplResponse,
    Snippet,
)
from loguru import logger
from starlette import status

from server.settings import settings

from .utils import assert_json_equal


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"max_repls": 2, "max_repl_uses": 2, "init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_repl_check_nat(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[Snippet(id=uuid, code="#check Nat")],
    ).model_dump()
    resp = client.post("check", json=payload)

    assert resp.status_code == status.HTTP_200_OK

    cmd_response = CommandResponse(
        messages=[
            Message(
                severity="info",
                pos={"line": 1, "column": 0},
                endPos={"line": 1, "column": 6},
                data="Nat : Type",
            )
        ],
        env=0,
    )

    expected = CheckResponse(
        results=[ReplResponse(id=uuid, response=cmd_response, time=1.0)]
    ).model_dump(exclude_none=True)

    assert_json_equal(resp.json(), expected, ignore_keys=["time"])


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_single_snippet(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[Snippet(id=uuid, code="#check Nat")],
    ).model_dump()
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_200_OK

    cmd_response = CommandResponse(
        messages=[
            Message(
                severity="info",
                pos={"line": 1, "column": 0},
                endPos={"line": 1, "column": 6},
                data="Nat : Type",
            )
        ],
        env=0,
    )
    expected = CheckResponse(
        results=[ReplResponse(id=uuid, response=cmd_response, time=1.0)]
    ).model_dump(exclude_none=True)

    assert_json_equal(resp.json(), expected, ignore_keys=["time"])


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {
            "max_repls": 1,
            "max_repl_uses": 3,
            "init_repls": {},  # Ensure nothing preloaded
            "database_url": None,
        },  # bumped max_repl_uses to 3 because now header makes age increment
    ],
    indirect=True,
)
async def test_mathlib(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[Snippet(id=uuid, code="import Mathlib\ndef f := 1")],
        debug=True,  # Enable debug to see diagnostics
    ).model_dump()
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_200_OK

    expected = CheckResponse(
        results=[
            ReplResponse(
                id=uuid,
                response=CommandResponse(
                    env=1
                ),  # Env is 1 because initialization with header bumps env value
            )
        ]
    ).model_dump(exclude_none=True)

    assert_json_equal(resp.json(), expected, ignore_keys=["time", "diagnostics"])
    assert resp.json()["results"][0]["time"] < 15

    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[Snippet(id=uuid, code="import Mathlib\ndef f := 2")],
        debug=True,
    ).model_dump()
    resp1 = client.post("check", json=payload)
    assert resp1.status_code == status.HTTP_200_OK
    expected = CheckResponse(
        results=[
            ReplResponse(
                id=uuid,
                response=CommandResponse(
                    env=2
                ),  # Env is 2 because max one repl and manager shared by all tests.
            )
        ]
    ).model_dump(exclude_none=True)

    assert_json_equal(resp1.json(), expected, ignore_keys=["time", "diagnostics"])

    assert resp1.json()["results"][0]["time"] < 1


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"max_repls": 1, "max_repl_uses": 2, "init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_timeout(client: TestClient) -> None:
    # Maximum of one REPL with two uses so that REPL can be reused.
    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[Snippet(id=uuid, code="import Mathlib")],
        timeout=1,  # Short timeout to trigger a timeout error
        debug=True,
    ).model_dump()
    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
    assert resp.status_code == status.HTTP_200_OK
    assert "diagnostics" in resp.json()["results"][0]
    assert "repl_uuid" in resp.json()["results"][0]["diagnostics"]

    used_repl_uuid = resp.json()["results"][0]["diagnostics"]["repl_uuid"]
    assert "timed out" in resp.json()["results"][0]["error"]

    await asyncio.sleep(5)  # 5 seconds should be enough to load Mathlib

    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[
            Snippet(
                id=uuid,
                code="theorem one_plus_one : 1 + 1 = 2 := by rfl",
            )
        ],
        timeout=5,
        debug=True,
    ).model_dump()
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_200_OK
    assert resp.json()["results"][0]["diagnostics"]["repl_uuid"] != used_repl_uuid

    expecteds = {
        "v4.19.0": CheckResponse(
            results=[
                ReplResponse(
                    id=uuid,
                    response=CommandResponse(
                        env=0,
                        messages=[
                            Message(
                                severity="info",
                                pos={"line": 1, "column": 0},
                                endPos={"line": 1, "column": 42},
                                data="Goals accomplished!",
                            )
                        ],
                    ),
                )
            ]
        ).model_dump(exclude_none=True),
        "v4.15.0": CheckResponse(
            results=[
                ReplResponse(
                    id=uuid,
                    response=CommandResponse(
                        env=0,
                    ),
                )
            ]
        ).model_dump(exclude_none=True),
    }
    assert_json_equal(
        resp.json(),
        expected=expecteds[settings.lean_version],
        ignore_keys=["time", "diagnostics"],
    )


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"max_repls": 1, "max_repl_uses": 3, "init_repls": {}, "database_url": None},
    ],
    indirect=True,  # To parametrize fixture
)
async def test_repl_exhausted(client: TestClient) -> None:
    payload = CheckRequest(
        snippets=[Snippet(id="1", code="#check Nat")], debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    repl_uuid = resp.json()["results"][0]["diagnostics"]["repl_uuid"]

    payload = CheckRequest(
        snippets=[Snippet(id="2", code="#check 0")], debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    assert repl_uuid == resp.json()["results"][0]["diagnostics"]["repl_uuid"]

    payload = CheckRequest(
        snippets=[Snippet(id="3", code="#check 1")], debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    assert repl_uuid == resp.json()["results"][0]["diagnostics"]["repl_uuid"]

    payload = CheckRequest(
        snippets=[Snippet(id="4", code="#check 2")], debug=True
    ).model_dump()

    try:
        resp = client.post("check", json=payload)
    except Exception as e:
        logger.info(f"Error during request: {e}")
        logger.info(resp.status_code)
        raise

    assert repl_uuid != resp.json()["results"][0]["diagnostics"]["repl_uuid"]


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_check_trailing_slash(client: TestClient) -> None:
    uuid = str(uuid4())
    payload = CheckRequest(
        snippets=[Snippet(id=uuid, code="#check Nat")],
    ).model_dump()

    # Call with slash
    resp = client.post("check/", json=payload, follow_redirects=False)
    assert resp.status_code == status.HTTP_200_OK

    assert "messages" in resp.json()["results"][0]["response"]


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"max_repls": 1, "max_repl_uses": 1, "init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_wrong_custom_id_on_check(client: TestClient) -> None:
    payload = {
        "snippets": {"custom_id": "check-nat", "code": "#check Nat"},
        "debug": True,
    }

    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_422_UNPROCESSABLE_ENTITY


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"max_repls": 1, "max_repl_uses": 1, "init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_wrong_custom_ids_on_check(client: TestClient) -> None:
    payload = {
        "snippets": [
            {"id": "check-nat", "code": "#check Nat"},
            {"custom_id": "check-deff1", "code": "import Mathlib\ndef f:= 1"},
            {
                "custom_id": "check-theo",
                "code": "import Mathlib\ntheorem onepp : 1 + 1 = 2 := by rfl",
            },
        ],
        "debug": True,
    }
    resp = client.post("check", json=payload)
    assert resp.status_code == status.HTTP_422_UNPROCESSABLE_ENTITY


@pytest.mark.asyncio
@pytest.mark.parametrize(
    "client",
    [
        {"max_repls": 1, "max_repl_uses": 1, "init_repls": {}, "database_url": None},
    ],
    indirect=True,
)
async def test_infotree(client: TestClient) -> None:
    payload = CheckRequest(
        snippets=[Snippet(id="onepp", code="theorem onepp : 1+1 = 2:= by rfl")],
        infotree=Infotree.original,
    ).model_dump()

    resp = client.post("check", json=payload)
    expected = CheckResponse(
        results=[
            ReplResponse(
                id="onepp",
                response=CommandResponse(
                    env=5,
                    infotree=[
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
                                                                "goalsBefore": [
                                                                    "⊢ 1 + 1 = 2"
                                                                ],
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
                ),
            )
        ]
    ).model_dump(exclude_none=True)

    assert resp.status_code == status.HTTP_200_OK
    assert_json_equal(resp.json(), expected, ignore_keys=["time", "env"])
