import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Calculate $ 1 + 2 + 3 + 4 + 5 $ -/
theorem lean_workbook_10209 : ∑ i in Finset.range 6, i = 15  := by
  /-
  To prove that the sum of the first five natural numbers is 15, we use the formula for the sum of the first \( n \) natural numbers, which is given by \( \frac{n(n+1)}{2} \). For \( n = 5 \), this formula yields:
  \[
  \frac{5 \cdot 6}{2} = \frac{30}{2} = 15
  \]
  Thus, the sum of the first five natural numbers is indeed 15.
  -/
  -- Use the formula for the sum of the first n natural numbers: ∑ i in Finset.range (n+1), i = n * (n + 1) / 2
  rw [Finset.sum_range_succ]
  -- Simplify the expression using numerical computation
  norm_num
  -- Verify that the simplified expression matches the expected result
  <;> rfl
