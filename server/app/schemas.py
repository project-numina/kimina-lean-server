from typing import Any, Literal, NotRequired, Type, TypeAlias, TypedDict

from pydantic import BaseModel, ConfigDict, Field, model_validator

Infotree: TypeAlias = Literal["original", "synthetic"]


# TODO: Separate schemas in schemas dir with separate files.
class Code(BaseModel):
    custom_id: str | int
    proof: str | None = Field(None)
    code: str | None = Field(
        None
    )  # To be backward compatibility with autoformalizer client

    def get_proof_content(self) -> str | None:
        return self.proof if self.proof is not None else self.code


class BackwardResponse(TypedDict):
    custom_id: str
    error: str | None
    response: NotRequired[dict[str, Any] | None]


class VerifyResponse(BaseModel):
    results: list[BackwardResponse]


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


class CommandResponse(TypedDict):
    env: int
    messages: NotRequired[list[Message]]
    sorries: NotRequired[list[Sorry]]
    tactics: NotRequired[list[Tactic]]
    infotree: NotRequired[Any]


from typing import TypeVar

T = TypeVar("T", bound="CheckRequest")
TS = TypeVar("TS", bound="ChecksRequest")
U = TypeVar("U", bound="CheckResponse")


class CheckResponse(BaseModel):
    id: str = Field(..., description="Identifier to trace the snippet")
    time: float = 0.0
    error: str | None = None
    response: CommandResponse | None = None
    diagnostics: Diagnostics | None = None

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
        description="Level of detail for the info tree: 'original' | 'synthetic'",
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
