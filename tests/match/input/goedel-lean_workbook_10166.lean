import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Compute $\frac{4}{7} \cdot \frac{5}{11}$ . -/
theorem lean_workbook_10166 (a b c d : ℚ) (h₁ : a = 4/7) (h₂ : b = 5/11) : a * b = 20/77  := by
  /-
  To compute the product of \(\frac{4}{7}\) and \(\frac{5}{11}\), we proceed as follows:
  1. Substitute the given values \(a = \frac{4}{7}\) and \(b = \frac{5}{11}\) into the expression \(a \cdot b\).
  2. Multiply the numerators: \(4 \cdot 5 = 20\).
  3. Multiply the denominators: \(7 \cdot 11 = 77\).
  4. Combine the results to obtain \(\frac{20}{77}\).
  -/
  -- Substitute the given values for a and b into the expression a * b.
  rw [h₁, h₂]
  -- Simplify the expression using numerical normalization to verify the result.
  norm_num
