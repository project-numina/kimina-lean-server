import re
from typing import List
import pandas


def split_proof_header(proof: str) -> tuple[str, str]:
    """
    Splits `proof` into:
    - header: the consecutive `import ...` lines at the beginning of the proof
    - context: rest of the proof

    Args:
        proof (str): The proof code to split

    Returns:
        tuple[str, str]: The header and context of the proof
    """
    proof = proof.strip()
    lines = proof.splitlines()
    body_start = 0

    for i, line in enumerate(lines):
        if line.startswith("import"):
            body_start = i + 1
        else:
            break

    header = "\n".join(lines[:body_start]).strip()
    body = "\n".join(lines[body_start:])

    return header, body


def get_error_msg(response): ...


def parse_messages(messages):
    parsed_messages = []
    for msg in messages:
        severity = msg.get("severity", "info")
        data = msg.get("data", "")
        pos = msg.get("pos", {"line": 0, "column": 0})
        end_pos = msg.get("endPos", {"line": 0, "column": 0})
        parsed_messages.append(
            {"severity": severity, "message": data, "pos": pos, "endPos": end_pos}
        )
    return parsed_messages


def parse_error_message(message):
    match = re.match(r"^(.*?):\n(.*)", message, re.DOTALL)
    if match:
        severity = match.group(1)
        msg = match.group(2)
    else:
        severity = "error"
        msg = message
    return [
        {
            "severity": severity,
            "message": msg,
            "pos": {"line": 0, "column": 0},
            "endPos": {"line": 0, "column": 0},
        }
    ]


def parse_lean_response(response):
    messages = []
    if "messages" in response:
        messages = parse_messages(response.get("messages", []))
    elif "message" in response:
        messages = parse_error_message(response.get("message", ""))

    # TODO: @marco is it ok to filter out unsolved goals?
    # messages = list(filter(lambda x: "unsolved goals" not in x["message"], messages))
    # messages = sorted(messages, key=lambda x: (x["pos"]["line"], x["pos"]["column"]))

    # here if multiple errors on same line it will take last, why not first?
    # line_num_to_message = {(message["pos"]["line"]): message for message in messages}
    # here if multiple errors on same line it will take first
    line_num_to_message = {}
    for message in messages:
        key = message["pos"]["line"]
        if key not in line_num_to_message:
            line_num_to_message[key] = message

    return line_num_to_message


def get_messages_for_lines(messages, start_line, end_line):
    selected_messages = []
    has_error = False
    is_unsolved_goals = False
    for idx in range(start_line, end_line + 1):
        if idx in messages:
            selected_messages.append(messages[idx])
            if messages[idx]["severity"] == "error":
                has_error = True
            if "unsolved goals" in messages[idx]["message"]:
                is_unsolved_goals = True
    return selected_messages, has_error, is_unsolved_goals


def has_error_response(
    feedback: dict, accept_sorry: bool = True, return_error_messages: bool = False
):
    """
    Checks if the Lean feedback contains an error.

    Args:
        feedback: The Lean feedback as a dictionary.
        accept_sorry: Whether to accept "sorry" statements as "not an error".
            By default, "sorry" statements are not considered errors.
        return_error_messages: Whether to return the feedback error messages.
    """
    if "error" in feedback:
        r = (True, [feedback["error"]]) if return_error_messages else True
        return r

    if "stderr" in feedback:
        r = (True, [feedback["stderr"]]) if return_error_messages else True
        return r

    has_error = False
    error_data_values = []
    sorry_data_values = []
    if "messages" in feedback:
        error_data_values = [
            message["data"]
            for message in feedback.get("messages", [])
            if message.get("severity") == "error"
        ]
        has_error = bool(error_data_values)

        if not accept_sorry:
            warning_data_values = [
                message["data"]
                for message in feedback.get("messages", [])
                if message.get("severity") == "warning"
            ]
            sorry_data_values = [
                warning_data
                for warning_data in warning_data_values
                if "declaration uses 'sorry'" in warning_data
            ]
            has_error = has_error or bool(sorry_data_values)

    if return_error_messages:
        return has_error, error_data_values + sorry_data_values
    else:
        return has_error


def parse_client_response(response: dict):
    """
    Parses the response from the Lean4Client.
    Reponse should be the output of client.Lean4Client.(async_)verify

    Args:
        - response (dict): The response from the Lean4Client.

    Returns:
        - dict: A dictionary containing the following keys:
            - has_error: Whether the response contains an error.
            - is_valid_no_sorry: Whether the response is valid without "sorry" statements.
                this is used for proof verification.
            - is_valid_with_sorry: Whether the response is valid with "sorry.
                this is used for statement verification.
    """
    error_message = response.get("error", None)
    json_response = response.get("response", {})

    error = bool(error_message) or has_error_response(json_response)
    is_valid_no_sorry = (not bool(error_message)) and (
        not has_error_response(json_response, accept_sorry=False)
    )
    is_valid_with_sorry = (not bool(error_message)) and (
        not has_error_response(json_response, accept_sorry=True)
    )

    return {
        "has_error": error,
        "is_valid_no_sorry": is_valid_no_sorry,
        "is_valid_with_sorry": is_valid_with_sorry,
        "time": json_response.get("time", None) if json_response else None,
    }


def analyze_sample(lean_feedback: dict):
    error = lean_feedback.get("error", None)
    output = parse_client_response(lean_feedback)

    return {
        "is_valid_no_sorry": output["is_valid_no_sorry"],
        "is_valid_with_sorry": output["is_valid_with_sorry"],
        "has_error": output["has_error"],
        "has_connection_error": bool(error),
        "time": None if error is not None and "timed out" in error else output["time"],
    }


def analyze(result: List[dict]):
    df = pandas.DataFrame([analyze_sample(sample_result) for sample_result in result])

    # % of proof which compiled and do not contain a sorry.
    valid_rate = df["is_valid_no_sorry"].sum() / len(df)
    print(f"Valid proofs: {100 * valid_rate:.2f} %")

    # Percentage of connection errors.
    connection_error_rate = df["has_connection_error"].sum() / len(df)
    print(f"Connection errors rate: {100 * connection_error_rate:.2f} %")

    # Calculate total verification time (excluding None values which represent timeout error)
    valid_times = df["time"].dropna()
    timeout_count = len(df) - len(valid_times)

    total_time = valid_times.sum()
    print(
        f"Total verification time: {total_time:.2f} seconds (excluding {timeout_count} timeout error)"
    )

    # Also provide average time for reference
    if len(valid_times) > 0:
        avg_time = valid_times.mean()
        print(
            f"Average verification time: {avg_time:.2f} seconds per successful verification"
        )
