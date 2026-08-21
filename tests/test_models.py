import pytest
from kimina_client.models import (
    CommandResponse,
    Message,
    ReplResponse,
    SnippetStatus,
)


@pytest.mark.parametrize(
    ("response", "expected"),
    [
        (
            CommandResponse(
                messages=[
                    Message(
                        severity="warning",
                        pos={"line": 1, "column": 0},
                        data="declaration uses 'sorry'",
                    )
                ]
            ),
            SnippetStatus.sorry,
        ),
        (
            CommandResponse(
                messages=[
                    Message(
                        severity="warning",
                        pos={"line": 1, "column": 0},
                        data="some unrelated warning",
                    )
                ]
            ),
            SnippetStatus.valid,
        ),
    ],
)
def test_sorry_classification(
    response: CommandResponse,
    expected: SnippetStatus,
) -> None:
    result = ReplResponse(id="test", response=response)

    assert result.analyze().status == expected
