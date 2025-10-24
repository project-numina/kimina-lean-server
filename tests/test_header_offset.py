from kimina_client import ReplResponse

from server.routers.check import _apply_header_offset


def test_apply_header_offset_updates_positions() -> None:
    response = ReplResponse(
        id="snippet",
        response={
            "messages": [
                {
                    "severity": "error",
                    "pos": {"line": 2, "column": 1},
                    "endPos": {"line": 3, "column": 4},
                    "data": "oops",
                }
            ],
            "sorries": [
                {
                    "pos": {"line": 1, "column": 0},
                    "endPos": {"line": 1, "column": 5},
                    "goal": "sorry",
                }
            ],
        },
    )

    _apply_header_offset(response, 4)

    assert response.response is not None
    messages = response.response.get("messages")
    assert messages is not None
    assert messages[0]["pos"]["line"] == 6
    assert messages[0]["endPos"]["line"] == 7

    sorries = response.response.get("sorries")
    assert sorries is not None
    assert sorries[0]["pos"]["line"] == 5
    assert sorries[0]["endPos"]["line"] == 5


def test_apply_header_offset_ignores_zero_offset() -> None:
    response = ReplResponse(
        id="snippet",
        response={
            "messages": [
                {
                    "severity": "error",
                    "pos": {"line": 2, "column": 1},
                    "data": "oops",
                }
            ]
        },
    )

    _apply_header_offset(response, 0)

    assert response.response is not None
    message = response.response.get("messages")[0]
    assert message["pos"]["line"] == 2
