import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $\sum_{cyc}(a-b)^4 + \sum_{cyc}ab(a-b)^2 \ge 0$. -/
theorem lean_workbook_10088 (a b c : ℝ) :
  (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 + a * b * (a - b) ^ 2 + b * c * (b - c) ^ 2 + c * a * (c - a) ^ 2 ≥ 0  := by
  /-
  To prove that \(\sum_{cyc}(a-b)^4 + \sum_{cyc}ab(a-b)^2 \ge 0\), we can use the fact that the square of any real number is non-negative. Specifically, we consider the squares of the differences \(a - b\), \(b - c\), and \(c - a\), and the squares of the expressions \(a * b * (a - b)^2\), \(b * c * (b - c)^2\), and \(c * a * (c - a)^2\). Each of these squares is non-negative, and their sum is also non-negative.
  -/
  -- Use `nlinarith` to handle the non-linear arithmetic.
  -- We provide the non-negativity of the squares of the differences and the expressions.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
