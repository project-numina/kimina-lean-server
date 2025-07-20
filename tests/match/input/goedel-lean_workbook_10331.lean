import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- We just have to prove that $6(a^2+b^2) \ge (3a^2+3b^2+(a+b)^2+2ab)$ which is equivalent to $2a^2+2b^2 \ge 4ab$ which is true. -/
theorem lean_workbook_10331  (a b : ℝ) :
  2 * a^2 + 2 * b^2 ≥ 4 * a * b  := by
  /-
  To prove the inequality \(6(a^2 + b^2) \ge 3a^2 + 3b^2 + (a + b)^2 + 2ab\), we start by simplifying the inequality. We can rewrite the inequality as \(2a^2 + 2b^2 \ge 4ab\). This inequality is equivalent to \((a - b)^2 \ge 0\), which is always true since the square of any real number is non-negative.
  -/
  -- We start by proving a simpler inequality equivalent to the original.
  have h : 0 ≤ (a - b)^2 := by
    -- The square of any real number is non-negative.
    apply sq_nonneg
  -- Using the non-negativity of (a - b)^2, we can conclude the original inequality.
  linarith [sq_nonneg (a - b)]
