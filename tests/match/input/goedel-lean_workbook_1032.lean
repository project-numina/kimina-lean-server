import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- By Vasc's inequality we have \n $\frac53(a^2+b^2+c^2)^2 \ge 2\sum a^3b+3\sum ab^3$ -/
theorem lean_workbook_1032 (a b c : ℝ) : (5 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)  := by
  /-
  We need to show that for real numbers \(a\), \(b\), and \(c\), the inequality \(\frac{5}{3}(a^2 + b^2 + c^2)^2 \geq 2(a^3b + b^3c + c^3a) + 3(ab^3 + bc^3 + ca^3)\) holds. This can be verified using non-linear arithmetic (nlinarith) by considering the non-negativity of squares and applying basic algebraic inequalities.
  -/
  -- Use non-linear arithmetic to verify the inequality by considering the non-negativity of squares and applying basic algebraic inequalities.
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b)]
