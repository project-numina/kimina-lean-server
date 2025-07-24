import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- For $ a,b,c\geq 0$ prove that $8+2(a^2+b^2+c^2)+abc\geq 5(a+b+c) $ . -/
theorem lean_workbook_10303 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 8 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 5 * (a + b + c)  := by
  /-
  We need to prove that for non-negative real numbers \(a\), \(b\), and \(c\), the inequality \(8 + 2(a^2 + b^2 + c^2) + abc \geq 5(a + b + c)\) holds. This can be shown using non-linear arithmetic by considering the non-negativity of squares and other expressions.
  -/
  -- Use non-linear arithmetic to prove the inequality by considering the non-negativity of squares and other expressions.
  nlinarith [sq_nonneg (a + b + c - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (c - a), sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1)]
