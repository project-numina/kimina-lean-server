import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Solve the equation $\left \lfloor x \right \rfloor^3+2x^2=x^3+2\left \lfloor x\right \rfloor^2$ -/
theorem lean_workbook_1024 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2  := by
  /-
  Given the equation \(\left \lfloor x \right \rfloor^3 + 2x^2 = x^3 + 2\left \lfloor x \right \rfloor^2\), we need to show that this equation holds for any real number \(x\) such that \(x = z\) for some integer \(z\). The proof involves substituting \(x = z\) into the equation and verifying that both sides are equal.
  -/
  -- Substitute x = z into the equation
  cases' hx with z hz
  rw [hz]
  -- Simplify the equation using the fact that x = z
  simp [Int.floor_eq_iff, pow_three]
