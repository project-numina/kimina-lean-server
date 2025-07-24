import json
import textwrap
from enum import Enum
from typing import Any, Literal, NotRequired, Type, TypedDict

import pygments
from pydantic import BaseModel, ConfigDict, Field, model_validator
from pygments.formatters import Terminal256Formatter
from pygments.lexers import JsonLexer  # type: ignore


class Infotree(str, Enum):
    full = "full"
    tactics = "tactics"
    original = "original"
    substantive = "substantive"


# TODO: Separate schemas in schemas dir with separate files.
class Code(BaseModel):
    custom_id: str | int
    proof: str | None = Field(None)
    code: str | None = Field(
        None
    )  # To be backward compatibility with autoformalizer client

    def get_proof_content(self) -> str:
        content = self.proof if self.proof is not None else self.code
        if content is None:
            raise ValueError(f"Snippet {self.custom_id!r} has no proof/code content")
        return content


class VerifyRequestBody(BaseModel):
    codes: list[Code]
    timeout: int = 300
    infotree_type: Infotree | None = None
    disable_cache: bool = False


class Snippet(BaseModel):
    id: str = Field(..., description="Identifier to trace the snippet")
    code: str = Field(..., description="Lean 4 snippet or proof attempt")


# The classes below map to the REPL/JSON.lean in the Lean REPL repository:
# see https://github.com/leanprover-community/repl


class Command(TypedDict):
    cmd: str
    env: NotRequired[int | None]
    infotree: NotRequired[Infotree]


class Pos(TypedDict):
    line: int
    column: int


class Sorry(TypedDict):
    pos: Pos
    endPos: Pos
    goal: str
    proofState: NotRequired[int | None]


class Error(TypedDict):
    message: str


class ExtendedError(Error):
    time: float | None


class Message(TypedDict):
    severity: Literal["trace", "info", "warning", "error"]
    pos: Pos
    endPos: NotRequired[Pos | None]
    data: str


class ProofStep(TypedDict):
    proofState: int
    tactic: str


class Tactic(TypedDict):
    pos: int
    endPos: int
    goals: str
    tactic: str
    proofState: NotRequired[int | None]
    usedConstants: NotRequired[list[str]]


class Diagnostics(TypedDict, total=False):
    repl_uuid: str
    cpu_max: float
    memory_max: float


# TODO: use basemodel pydantic instead
class CommandResponse(TypedDict):
    env: NotRequired[
        int
    ]  # Have to make it not required now due to "gc" option already used on previous server
    messages: NotRequired[list[Message] | None]
    sorries: NotRequired[list[Sorry] | None]
    tactics: NotRequired[list[Tactic] | None]
    infotree: NotRequired[Any]


class ExtendedCommandResponse(CommandResponse):
    time: float | None


from typing import TypeVar

T = TypeVar("T", bound="CheckRequest")
TS = TypeVar("TS", bound="ChecksRequest")
U = TypeVar("U", bound="CheckResponse")


class CheckResponse(BaseModel):
    id: str = Field(..., description="Identifier to trace the snippet")
    time: float = 0.0
    error: str | None = None
    response: CommandResponse | Error | None = None
    diagnostics: Diagnostics | None = None

    def __repr__(self) -> str:
        data = self.model_dump(exclude_none=True)
        json_str = json.dumps(data, indent=2)

        colored: str = pygments.highlight(  # type: ignore
            json_str, JsonLexer(), Terminal256Formatter(style="monokai", full=False)  # type: ignore
        ).rstrip()  # type: ignore
        indented = textwrap.indent(colored, 2 * " ")  # type: ignore
        return f"{self.__class__.__name__}(\n{indented}\n)"

    @model_validator(mode="before")
    @classmethod
    def require_error_or_response(
        cls: Type[U], values: dict[str, Any]
    ) -> dict[str, Any]:
        if not (values.get("error") or values.get("response")):
            raise ValueError("either `error` or `response` must be set")
        return values


class BaseRequest(BaseModel):
    timeout: int = Field(
        30, description="Maximum time in seconds before aborting the check", ge=0
    )
    debug: bool = Field(
        False, description="Include CPU/RAM usage and REPL instance ID in the response"
    )
    reuse: bool = Field(
        True, description="Whether to attempt using a REPL if available"
    )
    infotree: Infotree | None = Field(
        None,
        description="Level of detail for the info tree.",
    )


class ChecksRequest(BaseRequest):
    snippets: list[Snippet] = Field(
        description="List of snippets to validate (batch or single element)"
    )

    @model_validator(mode="before")
    @classmethod
    def check_snippets(cls: Type[TS], values: dict[str, Any]) -> dict[str, Any]:
        arr = values.get("snippets")
        if not arr or len(arr) == 0:
            raise ValueError("`snippets` must be provided and non empty")

        for i, snippet in enumerate(arr):
            if not isinstance(snippet, dict) or "id" not in snippet:
                raise ValueError(f"`snippets[{i}].id` is required")

        ids = set({s["id"] for s in arr})
        if len(ids) != len(arr):
            raise ValueError("`snippets` must have unique ids")
        return values

    model_config = ConfigDict(
        json_schema_extra={
            "example": {
                "snippets": [
                    {
                        "id": "mathlib-import-def",
                        "code": "import Mathlib\ndef f := 1",
                    },
                ],
                "timeout": 20,
                "debug": False,
                "reuse": True,
                "infotree": "original",
            },
        }
    )


class CheckRequest(BaseRequest):
    snippet: Snippet = Field(description="Single snippet to validate")

    model_config = ConfigDict(
        json_schema_extra={
            "example": {
                "snippet": {
                    "id": "mathlib-import-def",
                    "code": "import Mathlib\ndef f := 1",
                },
                "timeout": 20,
                "debug": False,
                "reuse": True,
                "infotree": "original",
            },
        }
    )


class BackwardResponse(TypedDict):
    custom_id: str
    error: str | None  # TODO: check if error is required here, probably not
    response: NotRequired[ExtendedCommandResponse | ExtendedError | None]


class VerifyResponse(BaseModel):
    results: list[BackwardResponse]

    def __repr__(self) -> str:
        data = self.model_dump(exclude_none=True)
        json_str = json.dumps(data, indent=2)

        colored = pygments.highlight(  # type: ignore
            json_str,
            JsonLexer(),  # type: ignore
            Terminal256Formatter(style="monokai", full=False),  # type: ignore
        ).rstrip()

        indented = textwrap.indent(colored, "  ")  # type: ignore
        return f"{self.__class__.__name__}(\n{indented}\n)"
