import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- For all real $x$ , $x^{6}+2\ge x^{3}+x^{2}+x.$ -/
theorem lean_workbook_10135 (x : ℝ) : x^6 + 2 ≥ x^3 + x^2 + x  := by
  /-
  To prove that for all real \( x \), \( x^6 + 2 \geq x^3 + x^2 + x \), we can use the non-linear arithmetic (nlinarith) tactic in Lean4. This tactic is designed to handle inequalities involving polynomials and can automatically deduce the required inequality by considering the non-negativity of certain expressions.
  -/
  -- Use the nlinarith tactic to prove the inequality.
  -- The tactic will consider the non-negativity of the expressions (x^3 - 1), (x^2 - 1), and (x - 1) to deduce the required inequality.
  nlinarith [sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x - 1),
    sq_nonneg (x^3 - x), sq_nonneg (x^2 - x), sq_nonneg (x - x^2),
    sq_nonneg (x - x^3), sq_nonneg (x - x), sq_nonneg (x^2 - x^3)]
