import logging
from difflib import get_close_matches

from colorama import Style

logger = logging.getLogger("kimina-client")


def find_id_column(columns: list[str]) -> str | tuple[str, str]:
    """
    Finds column that's closest to "id".
    Option to concatenate two column to create id.
    """
    if "id" in columns:
        return "id"

    preferred_names = ["uuid", "proof_id", "problem_id"]

    match = get_close_matches("id", columns, n=1, cutoff=0.6)
    if not match:
        for name in preferred_names:
            match = get_close_matches(name, columns, n=1, cutoff=0.6)
            if match:
                break
    selected_column = match[0] if match else None
    logger.info("Available columns:")
    for i, col in enumerate(columns):
        logger.info(f"{i}: {col}")

    user_input = input("Select column index/name or type 'concat': ").strip()
    if user_input.lower() == "concat":
        idxs = input("Enter two column indices to concatenate (e.g. 0 1): ")
        idx1, idx2 = map(int, idxs.split())
        return (columns[idx1], columns[idx2])
    if not user_input and selected_column:
        return selected_column
    if user_input.isdigit() and 0 <= int(user_input) < len(columns):
        return columns[int(user_input)]
    if user_input not in columns:
        raise ValueError(f"Invalid column: {user_input}")

    return user_input


def find_code_column(columns: list[str]) -> str:
    """
    Finds column with Lean 4 code snippets.
    """
    if "code" in columns:
        return "code"

    preferred_names = ["code", "proof", "full_proof"]

    match = get_close_matches("code", columns, n=1, cutoff=0.6)
    if not match:
        for name in preferred_names:
            match = get_close_matches(name, columns, n=1, cutoff=0.6)
            if match:
                break
    selected_column = match[0] if match else None
    logger.info("Available columns:")
    for i, col in enumerate(columns):
        logger.info(f"{i}: {col}")

    user_input = input("Select column index/name: ").strip()
    if not user_input and selected_column:
        return selected_column
    if user_input.isdigit() and 0 <= int(user_input) < len(columns):
        return columns[int(user_input)]
    if user_input not in columns:
        raise ValueError(f"Invalid column: {user_input}")

    return user_input
    return user_input


def build_log(dataset_name: str, n: int, batch_size: int) -> str:
    """
    String builder to announce benchmark run.
    """
    final_log = (
        f"Running benchmark on {b(dataset_name)}: # Snippets = {b(str(n))} | Batches = "
    )

    n_full_batches = n // batch_size

    if n_full_batches == 0:
        final_log += f"[{b(str(n))}]"
    else:
        if n_full_batches == 1:
            final_log += f"[{b(str(batch_size))}]"
        else:
            final_log += f"{b(str(n_full_batches))} x [{b(str(batch_size))}]"
        if n % batch_size > 0:
            final_log += f" + [{b(str(n % batch_size))}]"
    return final_log


def b(s: str) -> str:
    return str(Style.BRIGHT + s + Style.RESET_ALL)
