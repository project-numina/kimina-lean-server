import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $ a,b,c>0 $ and $ a+b+c=3 $, then $ 2(a^2+b^2+c^2-2)^2+(a^2b^2+b^2c^2+c^2a^2)[2+3(a^2+b^2+c^2)] \geq 35 $ -/
theorem lean_workbook_1016 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 2 * (a^2 + b^2 + c^2 - 2)^2 + (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) * (2 + 3 * (a^2 + b^2 + c^2)) ≥ 35  := by
  /-
  Given \( a, b, c > 0 \) and \( a + b + c = 3 \), we need to show that:
  \[ 2(a^2 + b^2 + c^2 - 2)^2 + (a^2b^2 + b^2c^2 + c^2a^2)(2 + 3(a^2 + b^2 + c^2)) \geq 35 \]
  First, we express \( a^2 + b^2 + c^2 \) in terms of \( a + b + c \) and \( ab + bc + ca \):
  \[ a^2 + b^2 + c^2 = (a + b + c)^2 - 2(ab + bc + ca) \]
  Given \( a + b + c = 3 \), we substitute:
  \[ a^2 + b^2 + c^2 = 3^2 - 2(ab + bc + ca) = 9 - 2(ab + bc + ca) \]
  Next, we substitute \( a^2 + b^2 + c^2 \) into the inequality:
  \[ 2(9 - 2(ab + bc + ca) - 2)^2 + (ab + bc + ca)(2 + 3(9 - 2(ab + bc + ca))) \]
  Simplify the terms:
  \[ 2(7 - 2(ab + bc + ca))^2 + (ab + bc + ca)(2 + 3(7 - 2(ab + bc + ca))) \]
  We need to show that this expression is at least 35. Using non-negativity of squares and some algebraic manipulations, we can verify this inequality.
  -/
  -- Express a^2 + b^2 + c^2 in terms of a + b + c and ab + bc + ca
  have h₀ : a^2 + b^2 + c^2 = (a + b + c)^2 - 2 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- Substitute a + b + c = 3 into the expression
  simp_all only [sq, mul_assoc]
  -- Use non-negativity of squares to verify the inequality
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
