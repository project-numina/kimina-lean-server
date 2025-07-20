from app.split import split_snippet


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
