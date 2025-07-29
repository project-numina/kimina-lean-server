import json
import logging
import shutil
import textwrap
from enum import Enum
from itertools import chain
from textwrap import wrap
from typing import Any, Literal, NotRequired, Type, TypedDict, TypeVar
from uuid import uuid4

import pygments
from colorama import Fore
from pydantic import BaseModel, ConfigDict, Field, model_validator
from pygments.formatters import Terminal256Formatter
from pygments.lexers import JsonLexer  # type: ignore
from tabulate import tabulate  # type: ignore

logger = logging.getLogger("kimina-client")


class SnippetStatus(str, Enum):
    valid = "valid"
    sorry = "sorry"
    lean_error = "lean_error"  # Error in snippet, clearly identified by message of severity "error"
    repl_error = "repl_error"  # Error while running snippet, at REPL level
    timeout_error = "timeout_error"  # Error caught at server level, which contains "timed out" in the error message
    server_error = (
        "server_error"  # Error caught at server level, which is not a timeout error
    )

    # TODO: fix timing issue related to header non import?


class SnippetAnalysis(BaseModel):
    status: SnippetStatus
    time: float | None = None


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

    @classmethod
    def from_code(cls, code: str) -> "Snippet":
        return cls(id=uuid4().hex, code=code)

    @classmethod
    def from_snip(cls, snip: "str | Snippet") -> "Snippet":
        if isinstance(snip, str):
            return cls.from_code(snip)
        return snip


# The classes below map to the REPL/JSON.lean in the Lean REPL repository:
# see https://github.com/leanprover-community/repl


class Command(TypedDict):
    cmd: str
    env: NotRequired[int | None]
    infotree: NotRequired[Infotree]
    gc: NotRequired[bool]


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
        int | None
    ]  # Have to make it not required now due to "gc" option already used on previous server
    messages: NotRequired[list[Message] | None]
    sorries: NotRequired[list[Sorry] | None]
    tactics: NotRequired[list[Tactic] | None]
    infotree: NotRequired[Any]


# TODO: write a test validating partition of is_error + is_sorry + is_valid.
# Write the truth table.
def is_error(response: CommandResponse) -> bool:
    messages = response.get("messages")
    if messages is None:
        return False

    return any(m["severity"] == "error" for m in messages)


def has_sorry(response: CommandResponse) -> bool:
    sorries = response.get("sorries")
    if sorries is None:
        return False
    return len(sorries) > 0


def is_valid(response: CommandResponse) -> bool:
    """
    Valid means no error and no sorry.
    """
    return not is_error(response) and not has_sorry(response)


def is_sorry(response: CommandResponse) -> bool:
    """
    Information about sorry shows up twice:
    - as an element in the `sorries` array
    - as a "warning" message with data `declaration uses 'sorry'`

    We rely on the `sorries` array.
    Having a non-empty `sorries` array is not enough to be a sorry.
    You also need to have no errors.
    """
    return not is_error(response) and has_sorry(response)


class ExtendedCommandResponse(CommandResponse):
    time: float | None


# def make_extended_response(
#     response: CommandResponse, time: float | None
# ) -> ExtendedCommandResponse:
#     return ExtendedCommandResponse(**response, time=time)


# def make_extended_error(error: Error, time: float | None) -> ExtendedError:
#     return ExtendedError(**error, time=time)


T = TypeVar("T", bound="ReplRequest")
U = TypeVar("U", bound="ReplResponse")
TS = TypeVar("TS", bound="CheckRequest")
US = TypeVar("US", bound="CheckResponse")


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


class ReplRequest(BaseRequest):
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


class ReplResponse(BaseModel):
    id: str = Field(..., description="Identifier to trace the snippet")
    time: float = 0.0
    error: str | None = None
    response: CommandResponse | Error | None = None
    diagnostics: Diagnostics | None = None

    def __repr__(self) -> str:
        data = self.model_dump(exclude_none=True)
        json_str = json.dumps(data, indent=2)

        colored: str = pygments.highlight(  # type: ignore
            json_str,
            JsonLexer(),  # type: ignore
            Terminal256Formatter(style="monokai", full=False),  # type: ignore
        ).rstrip()  # type: ignore
        indented = textwrap.indent(colored, 2 * " ")  # type: ignore
        return f"{self.__class__.__name__}(\n{indented}\n)"

    @model_validator(mode="before")
    @classmethod
    def require_error_or_response(
        cls: Type[U], values: dict[str, Any]
    ) -> dict[str, Any]:
        if not values.get("error") and (values.get("response") is None):
            raise ValueError("Either `error` or `response` must be set")
        if values.get("error") is not None and values.get("response") is not None:
            raise ValueError("Only one of `error` or `response` can be set")
        return values

    def analyze(self) -> SnippetAnalysis:
        if self.error is not None:
            if "timed out" in self.error:
                return SnippetAnalysis(status=SnippetStatus.timeout_error)
            return SnippetAnalysis(status=SnippetStatus.server_error)

        if self.response is None:
            raise ValueError(
                f"`ReplResponse` for ID {self.id!r} has no response or error, which should not happen. Please report."
            )

        if "message" in self.response:
            return SnippetAnalysis(status=SnippetStatus.repl_error, time=self.time)

        if is_error(self.response):
            return SnippetAnalysis(status=SnippetStatus.lean_error, time=self.time)
        if is_valid(self.response):
            return SnippetAnalysis(status=SnippetStatus.valid, time=self.time)
        if is_sorry(self.response):
            return SnippetAnalysis(status=SnippetStatus.sorry, time=self.time)

        raise ValueError(
            f"`CommandResponse` for ID {self.id!r} is neither valid, nor sorry, nor error, which should not happen. Please report."
        )


class CheckRequest(BaseRequest):
    snippets: list[Snippet] = Field(
        description="List of snippets to validate (batch or single element)"
    )

    @model_validator(mode="after")
    def check_snippets(self) -> "CheckRequest":
        if not self.snippets:
            raise ValueError("`snippets` must be non empty")

        ids = set({s.id for s in self.snippets})
        if len(ids) != len(self.snippets):
            raise ValueError("`snippets` must have unique ids")
        return self

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


def add_color(text: str, color: str) -> str:
    return str(color + text + Fore.RESET)


def add_percent(count: int, total: int) -> str:
    if count == 0:
        return f"{count}"
    pct = 100 * (count / total)
    if pct >= 10:
        pct_str = f"{int(pct)}"
    elif pct >= 1:
        pct_str = f"{pct:.1f}".rstrip("0").rstrip(".")
    else:
        pct_str = f"{pct:.2f}".rstrip("0").rstrip(".")
    return f"{count} ({pct_str} %)"


def print_summary(
    n: int,
    valid_count: int,
    sorry_count: int,
    lean_error_count: int,
    timeout_error_count: int,
    repl_error_count: int,
    server_error_count: int,
    total_cpu_time: float,
    avg_cpu_time: float,
    elapsed: float,
) -> None:
    n_str = add_color(str(n), Fore.WHITE)
    valid_count_str = add_color(add_percent(valid_count, n), Fore.GREEN)
    sorry_count_str = add_color(add_percent(sorry_count, n), Fore.YELLOW)
    lean_error_count_str = add_color(add_percent(lean_error_count, n), Fore.RED)
    timeout_error_count_str = add_color(
        add_percent(timeout_error_count, n), Fore.MAGENTA
    )
    repl_error_count_str = add_color(add_percent(repl_error_count, n), Fore.RED)
    server_error_count_str = add_color(add_percent(server_error_count, n), Fore.RED)
    total_cpu_time_str = add_color(f"{total_cpu_time:.2f} s", Fore.CYAN)
    avg_cpu_time_str = add_color(f"{avg_cpu_time:.2f} s/snippet", Fore.CYAN)
    elapsed_str = add_color(f"{elapsed:.2f} s", Fore.WHITE)
    table = [
        [
            n_str,
            valid_count_str,
            sorry_count_str,
            lean_error_count_str,
            timeout_error_count_str,
            repl_error_count_str,
            server_error_count_str,
            total_cpu_time_str,
            avg_cpu_time_str,
            elapsed_str,
        ]
    ]
    headers = [
        add_color("#", Fore.WHITE),
        add_color("Valid ✅", Fore.GREEN),
        add_color("Sorry ⚠️", Fore.YELLOW),
        add_color("Lean Error ❌", Fore.RED),
        add_color("Timeout ⏰", Fore.MAGENTA),
        add_color("REPL Error", Fore.RED),
        add_color("Server Error", Fore.RED),
        add_color("Total CPU Time", Fore.CYAN),
        add_color("Avg CPU Time", Fore.CYAN),
        add_color("Elapsed", Fore.WHITE),
    ]

    logger.info(
        "\n"
        + tabulate(table, headers=headers, tablefmt="fancy_grid", stralign="center")  # type: ignore
    )


def log_table_multiline(table_str: str) -> None:
    width = shutil.get_terminal_size((80, 20)).columns
    for line in table_str.splitlines():
        if len(line) > width:
            for chunk in wrap(line, width):
                logger.info(chunk)
        else:
            logger.info(line)


class CheckResponse(BaseModel):
    results: list[ReplResponse]

    @classmethod
    def merge(cls, responses: list["CheckResponse"]) -> "CheckResponse":
        return cls(results=list(chain.from_iterable(r.results for r in responses)))

    def analyze(self, elapsed: float) -> None:
        analyses = [r.analyze() for r in self.results]

        valid_count = sum(1 for a in analyses if a.status == SnippetStatus.valid)
        sorry_count = sum(1 for a in analyses if a.status == SnippetStatus.sorry)
        lean_error_count = sum(
            1 for a in analyses if a.status == SnippetStatus.lean_error
        )
        repl_error_count = sum(
            1 for a in analyses if a.status == SnippetStatus.repl_error
        )
        timeout_error_count = sum(
            1 for a in analyses if a.status == SnippetStatus.timeout_error
        )
        server_error_count = sum(
            1 for a in analyses if a.status == SnippetStatus.server_error
        )

        cpu_times = [a.time for a in analyses if a.time is not None]
        total_cpu_time = sum(cpu_times)
        avg_cpu_time = total_cpu_time / len(cpu_times) if cpu_times else 0.0

        print_summary(
            n=len(self.results),
            valid_count=valid_count,
            sorry_count=sorry_count,
            lean_error_count=lean_error_count,
            timeout_error_count=timeout_error_count,
            repl_error_count=repl_error_count,
            server_error_count=server_error_count,
            total_cpu_time=total_cpu_time,
            avg_cpu_time=avg_cpu_time,
            elapsed=elapsed,
        )


class BackwardResponse(TypedDict):
    custom_id: str
    error: NotRequired[
        str | None
    ]  # TODO: check if error is required here, probably not
    response: NotRequired[ExtendedCommandResponse | ExtendedError | None]


def backward_response_from_repl(repl_response: ReplResponse) -> BackwardResponse:
    data = BackwardResponse(custom_id=repl_response.id)
    if repl_response.error is not None:
        data["error"] = repl_response.error
    if repl_response.response is not None:
        data["response"] = extend(repl_response.response, time=repl_response.time)
    return data


def extend(
    response: CommandResponse | Error | None, time: float | None = None
) -> ExtendedCommandResponse | ExtendedError | None:
    if response is None:
        return None
    elif "message" in response:
        return ExtendedError(**response, time=time)  # type: ignore
    else:
        return ExtendedCommandResponse(**response, time=time)


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
