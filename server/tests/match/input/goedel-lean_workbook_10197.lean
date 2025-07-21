import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $x$ be positive real number , Prove that $(1+x)^3(1+\frac{16}{x^3})\ge 81.$ -/
theorem lean_workbook_10197 (x : ℝ) (hx : x > 0) : (1 + x) ^ 3 * (1 + 16 / x ^ 3) ≥ 81  := by
  /-
  To prove that for a positive real number \( x \), \((1 + x)^3 \left(1 + \frac{16}{x^3}\right) \ge 81\), we start by simplifying the expression. We use the fact that \( x > 0 \) to handle the division and powers. We then apply algebraic manipulations and inequalities to show that the expression is indeed greater than or equal to 81.
  -/
  -- Simplify the expression by clearing denominators and handling powers.
  field_simp [hx]
  -- Rewrite the expression in a more manageable form.
  rw [le_div_iff (by positivity)]
  -- Normalize the expression by expanding and simplifying it.
  ring_nf
  -- Use non-linear arithmetic to prove the inequality.
  nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 4)]
