import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- For a,b,c positive and a+b+c=1 prove that $ 2+9abc \ge 7(ab+bc+ac)$ -/
theorem lean_workbook_10390 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : 2 + 9 * a * b * c ≥ 7 * (a * b + b * c + a * c)  := by
  /-
  We need to prove that for positive real numbers \(a\), \(b\), and \(c\) such that \(a + b + c = 1\), the inequality \(2 + 9abc \ge 7(ab + bc + ac)\) holds.
  To prove this, we use the non-linear arithmetic (nlinarith) tactic, which automatically handles inequalities involving polynomials. Specifically, we use the fact that the squares of real numbers are non-negative to derive the desired inequality.
  -/
  -- Use non-linear arithmetic to handle the inequality.
  -- We provide the non-negativity of the squares of various expressions to help the tactic derive the inequality.
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
