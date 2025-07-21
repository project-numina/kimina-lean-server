import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that \(a^3+(a+1)^3+\ldots+(a+6)^3\equiv 0\,(mod\, 7)\) for any integer \(a\). -/
theorem lean_workbook_1006 (a : ℤ) :
    ∑ i in Finset.range 7, (a + i) ^ 3 ≡ 0 [ZMOD 7]  := by
  /-
  To prove that \(a^3 + (a+1)^3 + \ldots + (a+6)^3 \equiv 0 \pmod{7}\) for any integer \(a\), we start by expanding each cube modulo 7. We then sum these expanded terms and simplify the sum modulo 7.
  1. Expand each cube \((a + i)^3\) modulo 7 for \(i = 0, 1, 2, 3, 4, 5, 6\).
  2. Sum the expanded terms.
  3. Simplify the sum modulo 7 to show that it is congruent to 0 modulo 7.
  -/
  -- Expand each cube modulo 7 for \(i = 0, 1, 2, 3, 4, 5, 6\)
  simp only [Int.ModEq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_succ, Int.add_emod, Int.mul_emod, Int.emod_emod]
  -- Simplify the sum modulo 7 to show that it is congruent to 0 modulo 7
  have : ∀ x : ℤ, x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
    intro x
    omega
  rcases this a with (h | h | h | h | h | h | h) <;> simp [h]
  <;> decide
