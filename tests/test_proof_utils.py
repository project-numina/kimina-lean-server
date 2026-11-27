import pytest

from kimina_client.proof_utils import has_error_response, parse_client_response


def sorry_warning(data: str) -> dict:
    return {
        "messages": [
            {
                "severity": "warning",
                "pos": {"line": 1, "column": 8},
                "endPos": {"line": 1, "column": 9},
                "data": data,
            }
        ]
    }


# Lean < 4.28 quotes sorry with '...', Lean >= 4.28 with `...`.
@pytest.mark.parametrize(
    "data", ["declaration uses 'sorry'", "declaration uses `sorry`"]
)
def test_sorry_is_not_a_valid_proof(data: str) -> None:
    feedback = sorry_warning(data)
    assert not has_error_response(feedback, accept_sorry=True)  # type: ignore
    assert has_error_response(feedback, accept_sorry=False)  # type: ignore

    parsed = parse_client_response({"response": feedback})  # type: ignore
    assert parsed["is_valid_with_sorry"]
    assert not parsed["is_valid_no_sorry"]
