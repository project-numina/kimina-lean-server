import nest_asyncio
from client import Lean4Client

# Enable nested asyncio for Jupyter notebooks
nest_asyncio.apply()

client = Lean4Client(base_url="http://127.0.0.0:80")
mock_proof = """import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/-- In a right-angled triangle ABC, with the right angle at A, let M be the midpoint of the hypotenuse BC. Let D be the foot of the perpendicular from M to the leg AB. Prove that D is the midpoint of AB.
-/
theorem right_triangle_median_perpendicular_midpoint:
  ∀ (A B C M D : Point) (AB BC : Line),
    rightTriangle A B C ∧
    distinctPointsOnLine A B AB ∧
    distinctPointsOnLine B C BC ∧
    midpoint B M C ∧
    foot M D AB
    → midpoint A D B := by
    euclid_intros
    have h_equidistant_AM_BM : |(A─M)| = |(B─M)| := by
      euclid_apply rightTriangle_midLine_half A B C M
      euclid_finish
    have h_tri_MAB : triangle M A B := by
      have h1: M ≠ A := by
        by_contra h_contra
        euclid_finish
      have h2: M ≠ B := by
        by_contra h_contra
        euclid_assert midpoint B B C
        euclid_assert B = C
        euclid_finish
      have h3: A ≠ B := by
        euclid_finish
      euclid_finish
    have h_iso_MAB : isoTriangle M A B := by
      euclid_assert |(M─A)| = |(M─B)|
      euclid_finish
    euclid_apply isoTriangle_threeLine_concidence_foot M A B D AB
    euclid_finish
"""

response = client.verify([
    {"proof": mock_proof, "custom_id": "1"},
    {"proof": mock_proof, "custom_id": "2"}
], timeout=120)

print(response)