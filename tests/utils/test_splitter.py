from utils.proof_utils import split_proof_header


def test_single_mathlib_import():
    proof = """import Mathlib"""

    expected_header = "import Mathlib"
    expected_context = ""

    header, context = split_proof_header(proof)
    assert header == expected_header
    assert context == expected_context


def test_single_mathlib_import_with_trailing_spaces():
    proof = """import Mathlib   

theorem one_plus_one : 1 + 1 = 2 := by rfl"""

    expected_header = "import Mathlib"
    expected_context = "\ntheorem one_plus_one : 1 + 1 = 2 := by rfl"

    header, context = split_proof_header(proof)
    assert header == expected_header
    assert context == expected_context


def test_multiple_imports():
    proof = """import Mathlib
import Aesop

theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    expected_header = "import Mathlib\nimport Aesop"
    expected_context = """\ntheorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    header, context = split_proof_header(proof)
    assert header == expected_header
    assert context == expected_context


def test_multiple_imports_preceded_by_eols():
    proof = """

import Mathlib
import Aesop
theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    expected_header = "import Mathlib\nimport Aesop"
    expected_context = """theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    header, context = split_proof_header(proof)
    assert header == expected_header
    assert context == expected_context


# TODO: Remove this test when we allow for multiple new lines between imports.
def test_multiple_separated_imports():
    proof = """import Mathlib

import Aesop

theorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    expected_header = "import Mathlib"
    expected_context = """\nimport Aesop\n\ntheorem one_plus_one : 1 + 1 = 2 := by
  sorry"""

    header, context = split_proof_header(proof)
    assert header == expected_header
    assert context == expected_context
