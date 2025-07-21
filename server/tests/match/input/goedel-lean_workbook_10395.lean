import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that for $a, b, c > 0$ and $a + b + c = 1$, $\frac{xy}{z} + \frac{yz}{x} + \frac{zx}{y} \geq x + y + z$. -/
theorem lean_workbook_10395 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : (x * y / z + y * z / x + z * x / y) ≥ x + y + z  := by
  /-
  Given \( a, b, c > 0 \) and \( a + b + c = 1 \), we need to prove that:
  \[
  \frac{xy}{z} + \frac{yz}{x} + \frac{zx}{y} \geq x + y + z
  \]
  First, we establish that \( x, y, z \) are positive. Then, we use the fact that the sum of these positive numbers is 1. We apply algebraic manipulation and inequalities to show that the left-hand side is greater than or equal to the right-hand side. Specifically, we use the non-negativity of squares and linear arithmetic to derive the desired inequality.
  -/
  -- Establish that x, y, z are positive.
  have h₁ : 0 < x * y := by positivity
  have h₂ : 0 < y * z := by positivity
  have h₃ : 0 < z * x := by positivity
  have h₄ : 0 < x * y * z := by positivity
  -- Use linear arithmetic to derive the inequality.
  field_simp [h₁, h₂, h₃, h₄]
  rw [le_div_iff (by positivity)]
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
