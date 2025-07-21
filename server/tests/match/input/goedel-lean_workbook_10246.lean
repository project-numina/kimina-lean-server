import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $a,b,c$ are non-negative numbers such that $a^2+b^2+c^2=a+b+c$, then $ab+bc+ca \geq a^2b^2+b^2c^2+c^2a^2$. -/
theorem lean_workbook_10246 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = a^2 + b^2 + c^2) : a * b + b * c + c * a ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2  := by
  /-
  Given non-negative real numbers \(a\), \(b\), and \(c\) such that \(a^2 + b^2 + c^2 = a + b + c\), we need to show that \(ab + bc + ca \geq a^2 b^2 + b^2 c^2 + c^2 a^2\).
  To prove this, we use the non-negativity of squares. Specifically, we consider the squares of the differences \(a - b\), \(b - c\), and \(c - a\). Since these differences are non-negative, their squares are also non-negative. By expanding these squares and summing them up, we can derive the desired inequality.
  -/
  -- Use non-linear arithmetic to prove the inequality.
  -- We use the non-negativity of squares of differences (a - b), (b - c), and (c - a).
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha,
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
