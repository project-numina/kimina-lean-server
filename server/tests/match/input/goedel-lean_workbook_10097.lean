import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Is this true for any reals $ a, b, c \ge 0 $ ?\n\n$ 3(a^4 + b^4 + c^4) + 2abc(a+b+c) \ge 5( a^2b^2+b^2c^2+c^2a^2 ) \ \ ; $\n -/
theorem lean_workbook_10097 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 2 * a * b * c * (a + b + c) ≥ 5 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  := by
  /-
  We need to show that for any non-negative real numbers \(a, b, c\), the inequality \(3(a^4 + b^4 + c^4) + 2abc(a+b+c) \geq 5(a^2b^2 + b^2c^2 + c^2a^2)\) holds. This can be proven using non-linear arithmetic (nlinarith) by considering the non-negativity of squares and other expressions involving non-negative numbers.
  -/
  -- Use non-linear arithmetic to prove the inequality by considering the non-negativity of squares and other expressions.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha,
    sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a),
    mul_self_nonneg (a - b + c), mul_self_nonneg (b - c + a), mul_self_nonneg (c - a + b)]
