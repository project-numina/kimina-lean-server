import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If a,b,c are side lengths of triangle , prove that $(a+b)(a+c)(b+c) \geq 8(a+b-c)(a+c-b)(b+c-a)$ -/
theorem lean_workbook_10187 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (a + c) * (b + c) ≥ 8 * (a + b - c) * (a + c - b) * (b + c - a)  := by
  /-
  Given that \(a\), \(b\), and \(c\) are the side lengths of a triangle, we need to prove that:
  \[
  (a + b)(a + c)(b + c) \geq 8(a + b - c)(a + c - b)(b + c - a)
  \]
  To prove this inequality, we can use the non-linear arithmetic (nlinarith) tactic, which automatically handles inequalities involving polynomials. The tactic will use the given conditions to derive the desired inequality.
  -/
  -- Use the non-linear arithmetic tactic to handle the inequality.
  -- The tactic will use the given conditions to derive the desired inequality.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_self_nonneg (a + b - c), mul_self_nonneg (b + c - a), mul_self_nonneg (c + a - b)]
