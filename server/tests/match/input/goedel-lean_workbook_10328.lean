import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove $4a^3-9a^2+9a+4\geqq 0$ for $a \geq 1$. -/
theorem lean_workbook_10328 (a : ℝ) (h : a ≥ 1) : 4 * a ^ 3 - 9 * a ^ 2 + 9 * a + 4 ≥ 0  := by
  /-
  To prove that \(4a^3 - 9a^2 + 9a + 4 \geq 0\) for \(a \geq 1\), we can use the non-linear arithmetic (nlinarith) tactic in Lean4. This tactic is designed to handle inequalities involving polynomials and other non-linear expressions. By providing specific squares that are non-negative, we can establish the desired inequality.
  -/
  -- Use nlinarith to handle the inequality. We provide specific non-negative expressions to help nlinarith prove the inequality.
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2 / 3), sq_nonneg (a - 1 / 3),
    sq_nonneg (a + 1 / 3), sq_nonneg (a + 2 / 3)]
