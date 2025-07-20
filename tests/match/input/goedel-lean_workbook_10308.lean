import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $a^2+b^2+c^2+4+36a^2b^2c^2\ge 19abc(a+b+c)$ given $a,b,c>0$ and $ab+bc+ca=1$. -/
theorem lean_workbook_10308 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a * b + b * c + c * a = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 4 + 36 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 19 * a * b * c * (a + b + c)  := by
  /-
  Given \(a, b, c > 0\) and \(ab + bc + ca = 1\), we need to prove that:
  \[ a^2 + b^2 + c^2 + 4 + 36a^2b^2c^2 \ge 19abc(a + b + c). \]
  We use the non-linear arithmetic (nlinarith) tactic, which automatically handles inequalities involving squares and products of real numbers. The tactic checks the non-negativity of various squared terms and combines them to derive the desired inequality.
  -/
  -- Use nlinarith to handle the non-linear arithmetic inequality.
  -- We provide several non-negative terms to help nlinarith derive the inequality.
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos hab.1 hab.2.1, mul_pos hab.2.1 hab.2.2, mul_pos hab.2.2 hab.1,
    sq_nonneg (a * b - 1 / 3), sq_nonneg (b * c - 1 / 3), sq_nonneg (c * a - 1 / 3),
    sq_nonneg (a * b + b * c + c * a - 1)]
