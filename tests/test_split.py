from server.split import split_snippet


def test_only_imports() -> None:
    code = "import A\nimport Mathlib\nimport B"
    header, body = split_snippet(code)
    assert header.splitlines() == ["import Mathlib", "import A", "import B"]
    assert body == ""


def test_imports_and_body() -> None:
    code = "import X\n\nimport Mathlib\nimport Y\n\ndef foo():\n    pass"
    header, body = split_snippet(code)
    assert header.splitlines() == ["import Mathlib", "import X", "import Y"]
    assert body.splitlines() == ["def foo():", "    pass"]


def test_no_imports() -> None:
    code = "def bar():\n    return 1"
    header, body = split_snippet(code)
    assert header == ""
    assert body == code


def test_duplicate_imports() -> None:
    code = "import Mathlib\nimport Mathlib\nimport Z\nimport Z\nZ"
    header, body = split_snippet(code)
    assert header.splitlines() == ["import Mathlib", "import Z"]
    assert body.splitlines() == ["Z"]


def test_single_mathlib_import() -> None:
    code = "import Mathlib"
    header, body = split_snippet(code)
    assert header == code
    assert body == ""


def test_single_mathlib_import_with_trailing_spaces() -> None:
    code = """import Mathlib   

theorem one_plus_one : 1 + 1 = 2 := by rfl"""

    header, body = split_snippet(code)
    assert header == "import Mathlib"
    assert body == "theorem one_plus_one : 1 + 1 = 2 := by rfl"


def test_multiple_imports() -> None:
    code = """import Mathlib
import Aesop

theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    header, body = split_snippet(code)
    assert header == "import Mathlib\nimport Aesop"
    assert (
        body
        == """theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""
    )


def test_multiple_imports_preceded_by_eols() -> None:
    code = """

import Mathlib
import Aesop
theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    header, body = split_snippet(code)
    assert header == "import Mathlib\nimport Aesop"
    assert (
        body
        == """theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""
    )


def test_multiple_separated_imports() -> None:
    code = """import Mathlib

import Aesop

theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    header, body = split_snippet(code)
    assert header == "import Mathlib\nimport Aesop"
    assert (
        body
        == """theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""
    )


def test_multiple_mathlib_imports() -> None:
    code = """import Mathlib.Tactic
import Aesop
import Mathlib.Data.Nat"""
    header, body = split_snippet(code)
    assert header == "import Mathlib\nimport Aesop"
    assert body == ""
