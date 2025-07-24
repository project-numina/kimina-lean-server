import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $(x + 1)(y + 2)(z + 3) \geq 8$ for non-negative real numbers $x, y, z$ with $x + y + z = 1$. -/
theorem lean_workbook_10204 (x y z : ℝ) (hx : x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0) (h : x + y + z = 1) : (x + 1) * (y + 2) * (z + 3) ≥ 8  := by
  /-
  To prove that \((x + 1)(y + 2)(z + 3) \geq 8\) for non-negative real numbers \(x, y, z\) with \(x + y + z = 1\), we can use the non-linear arithmetic (nlinarith) tactic in Lean4. This tactic is designed to handle inequalities involving polynomials and can automatically deduce the required inequality by considering the non-negativity of the variables and the given sum constraint.
  -/
  -- Use nlinarith to handle the inequality. This tactic will consider the non-negativity of the variables and the given sum constraint to deduce the required inequality.
  nlinarith [mul_nonneg hx.1 hx.2.1, mul_nonneg hx.1 hx.2.2, mul_nonneg hx.2.1 hx.2.2,
    mul_self_nonneg (x - 1 / 3), mul_self_nonneg (y - 1 / 3), mul_self_nonneg (z - 1 / 3),
    mul_self_nonneg (x - y), mul_self_nonneg (y - z), mul_self_nonneg (z - x)]
