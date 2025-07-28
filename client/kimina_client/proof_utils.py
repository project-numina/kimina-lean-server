import re
import statistics
from dataclasses import dataclass
from typing import Any, TypedDict

from .models import (
    BackwardResponse,
    CommandResponse,
    Error,
    ExtendedCommandResponse,
    ExtendedError,
    Message,
    Pos,
)

_ERR_RE = re.compile(r"^([^:]+):\n(.*)", re.DOTALL)


class FinalMessage(TypedDict):
    severity: str
    message: str
    pos: Pos
    endPos: Pos | None


def parse_messages(messages: list[Message]) -> list[FinalMessage]:
    parsed_messages: list[FinalMessage] = []
    for msg in messages:
        parsed_messages.append(
            FinalMessage(
                severity=msg.get("severity", "info"),
                message=msg.get("data", ""),
                pos=msg.get("pos", Pos(line=0, column=0)),
                endPos=msg.get("endPos", Pos(line=0, column=0)),
            )
        )
    return parsed_messages


def parse_error_message(message: str) -> list[FinalMessage]:
    # TODO : compare with partition c call and add real-life tests
    m = _ERR_RE.match(message)
    if m:
        severity, text = m.groups()
    else:
        severity, text = "error", message
    return [
        FinalMessage(
            severity=severity,
            message=text,
            pos=Pos(line=0, column=0),
            endPos=Pos(line=0, column=0),
        )
    ]


def parse_lean_response(response: CommandResponse | Error) -> dict[int, FinalMessage]:
    messages: list[FinalMessage] = []
    if "messages" in response:
        messages = parse_messages(response.get("messages", []) or [])  # type: ignore
    elif "message" in response:
        messages = parse_error_message(response.get("message", ""))  # type: ignore

    # TODO: @marco is it ok to filter out unsolved goals?
    # messages = list(filter(lambda x: "unsolved goals" not in x["message"], messages))
    # messages = sorted(messages, key=lambda x: (x["pos"]["line"], x["pos"]["column"]))

    # here if multiple errors on same line it will take last, why not first?
    # line_num_to_message = {(message["pos"]["line"]): message for message in messages}
    # here if multiple errors on same line it will take first

    # TODO: add tests on this
    # dict comprehension keeps last value for each key, so reverse gives first
    return {m["pos"]["line"]: m for m in reversed(messages)}


def get_messages_for_lines(
    messages: dict[int, FinalMessage], start_line: int, end_line: int
) -> tuple[list[FinalMessage], bool, bool]:
    selected_messages: list[FinalMessage] = []
    has_error = False
    is_unsolved_goals = False
    for idx in range(start_line, end_line + 1):
        if idx in messages:
            selected_messages.append(
                messages[idx]
            )  # TODO: check how we ensure there is indeed a message at line idx?
            if messages[idx]["severity"] == "error":
                has_error = True
            if "unsolved goals" in messages[idx]["message"]:
                is_unsolved_goals = True
    return selected_messages, has_error, is_unsolved_goals


# TODO: check who uses this apart from tests here.
def has_error_response(
    feedback: ExtendedCommandResponse | ExtendedError | None,
    accept_sorry: bool = True,
    return_error_messages: bool = False,
) -> bool:
    """
    Checks if the Lean feedback contains an error.

    Args:
        feedback: The Lean feedback as a dictionary.
        accept_sorry: Whether to accept "sorry" statements as "not an error".
            By default, "sorry" statements are not considered errors.
        return_error_messages: Whether to return the feedback error messages.
    """

    # TODO: check. This is a bit weird here, there is never error or stderr in the feedback...
    # if "error" in feedback:
    #     r = (True, [feedback["error"]]) if return_error_messages else True
    #     return r

    # if "stderr" in feedback:
    #     r = (True, [feedback["stderr"]]) if return_error_messages else True
    #     return r

    has_error = False
    error_data_values = []
    sorry_data_values = []
    if "messages" in feedback:  # type: ignore
        error_data_values = [
            message["data"]
            for message in feedback.get("messages", [])  # type: ignore
            if message.get("severity") == "error"
        ]
        has_error = bool(error_data_values)

        if not accept_sorry:
            warning_data_values = [
                message["data"]
                for message in feedback.get("messages", [])  # type: ignore
                if message.get("severity") == "warning"
            ]
            sorry_data_values = [
                warning_data
                for warning_data in warning_data_values
                if "declaration uses 'sorry'" in warning_data
            ]
            has_error = has_error or bool(sorry_data_values)

    if return_error_messages:
        return has_error, error_data_values + sorry_data_values  # type: ignore
    else:
        return has_error


class ParsedClientResponse(TypedDict):
    has_error: bool
    is_valid_no_sorry: bool
    is_valid_with_sorry: bool
    time: float | None


# TODO: Remove all this code
def parse_client_response(response: BackwardResponse) -> ParsedClientResponse:
    """
    Parses the response from the Lean4Client.
    Reponse should be the output of client.Lean4Client.(async_)verify which is BackwardResponse.
    TODO: Make sure that we implement the proper function for CheckResponse

    Args:
        - response (BackwardResponse): The response from the Lean4Client.

    Returns:
        - dict: A dictionary containing the following keys:
            - has_error: Whether the response contains an error.
            - is_valid_no_sorry: Whether the response is valid without "sorry" statements.
                this is used for proof verification.
            - is_valid_with_sorry: Whether the response is valid with "sorry.
                this is used for statement verification.
    """
    error_message = response.get("error", None)
    json_response: Any = response.get(
        "response", {}
    )  # time used to be included in the lean response :/

    error = bool(error_message) or has_error_response(json_response)  # type: ignore
    is_valid_no_sorry = (not bool(error_message)) and (
        not has_error_response(json_response, accept_sorry=False)  # type: ignore
    )
    is_valid_with_sorry = (not bool(error_message)) and (
        not has_error_response(json_response, accept_sorry=True)  # type: ignore
    )

    return ParsedClientResponse(
        has_error=error,
        is_valid_no_sorry=is_valid_no_sorry,
        is_valid_with_sorry=is_valid_with_sorry,
        time=json_response.get("time", None) if json_response else None,
    )


@dataclass
class SampleAnalysis:
    is_valid_no_sorry: bool
    is_valid_with_sorry: bool
    has_error: bool
    has_connection_error: bool
    time: float | None


# Only used here locally in this repo.
def analyze_sample(lean_feedback: BackwardResponse) -> SampleAnalysis:
    error = lean_feedback.get("error", None)
    output = parse_client_response(lean_feedback)

    return SampleAnalysis(
        is_valid_no_sorry=output["is_valid_no_sorry"],
        is_valid_with_sorry=output["is_valid_with_sorry"],
        has_error=output["has_error"],
        has_connection_error=bool(error),
        time=None if (error is not None and "timed out" in error) else output["time"],
    )


# Move to benchmark maybe
def analyze(results: list[BackwardResponse]) -> None:
    analyses = [analyze_sample(sample_result) for sample_result in results]
    total = len(analyses)

    valid_count = sum(a.is_valid_no_sorry for a in analyses)
    conn_errors = sum(a.has_connection_error for a in analyses)
    times = [a.time for a in analyses if a.time is not None]
    timeouts = total - len(times)

    print(f"Valid proofs: {100 * (valid_count / total):.2f} %")
    print(f"Connection errors rate: {100 * (conn_errors / total):.2f} %")

    # TODO: put the results of the analysis in an object which has a proper __repr__
    print(
        f"Total verification time: {sum(times):.2f} seconds "
        f"(excluding {timeouts} timeout{'' if timeouts == 1 else 's'})"
    )

    if times:
        print(
            f"Average verification time: {statistics.mean(times):.2f} seconds per successful verification"
        )
