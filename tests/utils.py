import difflib
import json
from typing import Any, Iterable

import pytest


def _strip_keys(obj: Any, ignore: Iterable[str]) -> Any:
    """Recursively remove any dict keys in `ignore` from obj."""
    if isinstance(obj, dict):
        return {k: _strip_keys(v, ignore) for k, v in obj.items() if k not in ignore}
    if isinstance(obj, list):
        return [_strip_keys(v, ignore) for v in obj]
    return obj


def assert_json_equal(
    actual: Any, expected: Any, *, ignore_keys: Iterable[str] = ()
) -> None:
    """
    Assert that two JSON-like structures are equal, ignoring any keys in ignore_keys.
    Usage:
        assert_json_equal(resp.json(), expected, ignore_keys=["time", "cpu_max"])
    """
    a = json.dumps(
        _strip_keys(actual, ignore_keys), indent=2, sort_keys=True, ensure_ascii=False
    )
    e = json.dumps(
        _strip_keys(expected, ignore_keys), indent=2, sort_keys=True, ensure_ascii=False
    )
    if a != e:
        diff = difflib.unified_diff(
            e.splitlines(),
            a.splitlines(),
            fromfile="expected",
            tofile="actual",
            lineterm="",
        )
        pytest.fail("\n" + "\n".join(diff))
