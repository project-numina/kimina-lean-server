import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $x,y,z\ge0$ such that $x+y+z\le1,$ prove that $x^2+y^2+z^2-(xy)^2-(yz)^2-(zx)^2+2(xyz)^2\le1.$ -/
theorem lean_workbook_1034 : ∀ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z ≤ 1 → x ^ 2 + y ^ 2 + z ^ 2 - x * y ^ 2 - y * z ^ 2 - z * x ^ 2 + 2 * x * y * z ≤ 1  := by
  /-
  Given \( x, y, z \ge 0 \) such that \( x + y + z \le 1 \), we need to prove that:
  \[ x^2 + y^2 + z^2 - xy^2 - yz^2 - zx^2 + 2xyz \le 1. \]
  To prove this, we use the non-linear arithmetic (nlinarith) tactic, which automatically handles inequalities involving polynomials. We provide specific non-negativity conditions to ensure that the terms involved in the inequality are valid.
  -/
  -- Introduce the variables x, y, z and the hypothesis h
  intro x y z h
  -- Use the nlinarith tactic to handle the inequality
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_nonneg h.1 h.2.1, mul_nonneg h.2.1 h.2.2.1, mul_nonneg h.2.2.1 h.1,
    mul_nonneg (sq_nonneg x) (sq_nonneg y), mul_nonneg (sq_nonneg y) (sq_nonneg z),
    mul_nonneg (sq_nonneg z) (sq_nonneg x), mul_self_nonneg (x - y + z),
    mul_self_nonneg (y - z + x), mul_self_nonneg (z - x + y)]
