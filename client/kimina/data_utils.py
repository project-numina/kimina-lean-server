import re


def normalize_formal_statement(formal_statement: str) -> str:
    formal_statement = formal_statement.rstrip()

    # Remove trailing "sorry" if present
    if formal_statement.endswith("sorry"):
        formal_statement = formal_statement[:-5].strip()

    if not formal_statement.endswith("by"):
        formal_statement += " by"

    return formal_statement


def extract_first_theorem_statement(text: str) -> str | None:
    # Regular expression to match 'theorem' followed by the name and ':=', accounting for multi-line
    pattern = r"theorem\s*(.*?)\s*:="

    # Find all matches (multi-line handling)
    matches = re.findall(pattern, text, flags=re.DOTALL)

    if not matches:
        # Try matching 'lemma' instead
        pattern = r"lemma\s*(.*?)\s*:="
        matches = re.findall(pattern, text, flags=re.DOTALL)

    if not matches:
        # Try matching 'example' instead
        pattern = r"example\s*(.*?)\s*:="
        matches = re.findall(pattern, text, flags=re.DOTALL)

    # Return the last matched theorem name if any matches exist
    return matches[0].strip() if matches else None  # type: ignore


def is_index_commented(lean4_code: str, index: int) -> bool:
    """
    Checks if a given index in the Lean 4 code is inside a comment.
    Handles both block comments (/- ... -/) and single-line comments (-- ...).
    """

    if index < 0 or index >= len(lean4_code):
        return False

    # Check if inside a block comment
    block_comments = [
        (m.start(), m.end()) for m in re.finditer(r"/-.*?-/", lean4_code, re.DOTALL)
    ]
    for start, end in block_comments:
        if start <= index < end:
            return True  # Inside a block comment

    # Check if inside a single-line comment
    lines = lean4_code.splitlines()
    char_count = 0  # Track character index in full string

    for line in lines:
        comment_start = line.find("--")
        if comment_start != -1:
            if char_count <= index < char_count + len(line):  # Index is in this line
                if index >= char_count + comment_start:  # Index is after `--`
                    return True  # Inside a single-line comment
        char_count += len(line) + 1  # +1 for newline character

    return False  # Not inside a comment


def extract_proof_from_text(output: str, formal_statement: str) -> str:
    """
    Extracts a proof from a Lean 4 code block, ensuring it follows the formal statement.
    """

    formal_statement = normalize_formal_statement(formal_statement)

    theorem_statement = extract_first_theorem_statement(formal_statement)

    if theorem_statement is None:
        return "Theorem statement couldn't be parsed from statement."

    # Extract all Lean 4 code blocks
    lean4_codes: list[str] = re.findall(r"```lean4\n(.*?)\n```", output, re.DOTALL)

    for lean4_code in reversed(lean4_codes):
        if theorem_statement in lean4_code:
            # Find the starting position of theorem_statement in the original lean4_code
            theorem_start = lean4_code.find(theorem_statement)
            if theorem_start == -1:
                continue  # This should not happen due to previous check, but added for safety

            # Check if the theorem statement is inside a comment
            if is_index_commented(lean4_code, theorem_start):
                continue

            # Search for `:= by` only after the theorem statement
            match = re.search(r":=\s*by", lean4_code[theorem_start:])
            if match:
                proof_start = (
                    theorem_start + match.end()
                )  # Adjust index relative to original string

                return formal_statement + lean4_code[proof_start:]

    return "No proof found in the output."


__all__ = ["extract_proof_from_text"]
