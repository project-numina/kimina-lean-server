import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that for positive reals a, b, and c, the following inequality holds: \n\n $(a^2b+b^2c+c^2a)^2\geq abc(a+b+c)(ab+ac+bc)$ -/
theorem lean_workbook_10113 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a)^2 ≥ a * b * c * (a + b + c) * (a * b + b * c + c * a)  := by
  /-
  We need to prove the inequality \((a^2b + b^2c + c^2a)^2 \geq abc(a + b + c)(ab + ac + bc)\) for positive reals \(a\), \(b\), and \(c\). This can be shown using non-linear arithmetic by considering the non-negativity of squares and other expressions involving sums and products of \(a\), \(b\), and \(c\).
  -/
  -- Use non-linear arithmetic to prove the inequality.
  -- We consider the non-negativity of various expressions involving sums and products of a, b, and c.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_nonneg ha.le hb.le, mul_nonneg hb.le hc.le, mul_nonneg hc.le ha.le,
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    mul_nonneg (sq_nonneg (a + b)) (sq_nonneg (b + c)), mul_nonneg (sq_nonneg (b + c)) (sq_nonneg (c + a)),
    mul_nonneg (sq_nonneg (c + a)) (sq_nonneg (a + b))]
