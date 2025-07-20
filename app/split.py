from typing import Tuple


def split_snippet(code: str) -> Tuple[str, str]:
    """
    Splits a code snippet into a header (imports) and body.

    - Header: all lines at the top that are 'import ...' or blank before the first non-import.
      If any import is 'import Mathlib', include a single 'import Mathlib' at the top of the header.
      Other imports follow in their original order, without duplicates.
    - Body: the rest of the code starting from the first non-import/non-blank line.
    """
    lines = code.splitlines()
    header_lines: list[str] = []
    body_lines: list[str] = []
    found_body = False

    # Separate header candidate lines and body
    for line in lines:
        if not found_body and (
            line.strip().startswith("import ") or line.strip() == ""
        ):
            header_lines.append(line)
        else:
            found_body = True
            body_lines.append(line)

    # Process imports in header
    imports: list[str] = []
    seen: set[str] = set()
    has_mathlib = False
    for line in header_lines:
        stripped = line.strip()
        if not stripped.startswith("import "):
            continue
        if stripped.startswith("import Mathlib"):
            has_mathlib = True
        else:
            if stripped not in seen:
                imports.append(stripped)
                seen.add(stripped)

    # Build final header
    result_header: list[str] = []
    if has_mathlib:
        result_header.append("import Mathlib")
    result_header.extend(imports)

    header = "\n".join(result_header)
    body = "\n".join(body_lines)
    return header, body
