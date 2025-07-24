import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- For $x, y, z$ positive real numbers, prove that the following inequality holds $(x-y)\\cdot\\frac{x}{y+z}+(y-z)\\cdot\\frac{y}{z+x}+(z-x)\\cdot\\frac{z}{x+y}\\geq0$ -/
theorem lean_workbook_10198 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : (x - y) * (x / (y + z)) + (y - z) * (y / (z + x)) + (z - x) * (z / (x + y)) ≥ 0  := by
  /-
  To prove the inequality \((x-y) \cdot \frac{x}{y+z} + (y-z) \cdot \frac{y}{z+x} + (z-x) \cdot \frac{z}{x+y} \geq 0\) for positive real numbers \(x, y, z\), we proceed as follows:
  1. **Establish non-negativity of the terms**: Each term in the expression is a product of a difference and a fraction. Since \(x, y, z\) are positive, the denominators are positive, ensuring the fractions are non-negative.
  2. **Simplify the expression**: Using the fact that \(x, y, z\) are positive and the inequalities \(x \neq y\), \(y \neq z\), and \(x \neq z\), we can simplify the expression by applying algebraic manipulations and properties of real numbers.
  3. **Combine and verify**: Combine the terms and use the properties of real numbers to verify that the sum of these terms is non-negative.
  -/
  have h1 : 0 < y + z := by linarith
  have h2 : 0 < z + x := by linarith
  have h3 : 0 < x + y := by linarith
  have h4 : 0 < x * y := by positivity
  have h5 : 0 < y * z := by positivity
  have h6 : 0 < z * x := by positivity
  field_simp [h1, h2, h3, h4, h5, h6]
  rw [le_div_iff (by positivity)]
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
