import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $\sqrt{1+x}>1+\frac{x}{2}-x^2$ for all $x \in (0,1)$. -/
theorem lean_workbook_10396 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  Real.sqrt (1 + x) > 1 + x / 2 - x ^ 2  := by
  /-
  To prove that \(\sqrt{1+x} > 1 + \frac{x}{2} - x^2\) for all \(x \in (0,1)\), we start by noting that the square root function is positive for positive arguments. We then use the fact that the square of a real number is non-negative to establish the inequality. Specifically, we consider the square of \(x - 1\) and use this to derive the desired inequality.
  -/
  -- We start by noting that the square root of a positive number is positive.
  have h : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr (by linarith)
  -- We use the fact that the square of any real number is non-negative to establish the inequality.
  nlinarith [sq_sqrt (by linarith : 0 ≤ 1 + x), sq_nonneg (x - 1)]
