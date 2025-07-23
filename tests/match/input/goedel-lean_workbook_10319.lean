import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $\left(x^2-yz-1\right)^2+\left(y^2-zx-1\right)^2+\left(z^2-xy-1\right)^2\ge0$ -/
theorem lean_workbook_10319 (x y z : ℝ) : (x^2 - y * z - 1)^2 + (y^2 - z * x - 1)^2 + (z^2 - x * y - 1)^2 ≥ 0  := by
  /-
  We need to prove that for any real numbers \( x \), \( y \), and \( z \), the expression \(\left(x^2 - yz - 1\right)^2 + \left(y^2 - zx - 1\right)^2 + \left(z^2 - xy - 1\right)^2\) is non-negative. This can be shown by demonstrating that each term in the sum is a square of a real number, hence non-negative, and their sum is therefore non-negative.
  -/
  -- Apply the fact that the sum of non-negative numbers is non-negative.
  apply le_of_sub_nonneg
  -- Use non-linear arithmetic to show that the expression is non-negative.
  -- Each term (x^2 - y * z - 1)^2, (y^2 - z * x - 1)^2, and (z^2 - x * y - 1)^2 is a square, hence non-negative.
  nlinarith [sq_nonneg (x^2 - y * z - 1), sq_nonneg (y^2 - z * x - 1), sq_nonneg (z^2 - x * y - 1),
    sq_nonneg (x^2 - y * z), sq_nonneg (y^2 - z * x), sq_nonneg (z^2 - x * y),
    sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1)]
