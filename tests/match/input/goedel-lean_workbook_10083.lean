import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $x^2-xy+y^2 \geq |xy|$ -/
theorem lean_workbook_10083 (x y : ℝ) : x^2 - x*y + y^2 ≥ |x*y|  := by
  /-
  To prove that \( x^2 - xy + y^2 \geq |xy| \), we consider different cases based on the signs of \( xy \) and \( x - y \). We use the properties of absolute values and the non-negativity of squares to derive the inequality in each case.
  1. **Case 1: \( xy \geq 0 \)**
     - If \( xy \geq 0 \), then \( |xy| = xy \).
     - We need to show \( x^2 - xy + y^2 \geq xy \).
     - This can be rewritten as \( x^2 - 2xy + y^2 \geq 0 \), which is \( (x - y)^2 \geq 0 \).
     - Since the square of any real number is non-negative, \( (x - y)^2 \geq 0 \) holds.
  2. **Case 2: \( xy \leq 0 \)**
     - If \( xy \leq 0 \), then \( |xy| = -xy \).
     - We need to show \( x^2 - xy + y^2 \geq -xy \).
     - This can be rewritten as \( x^2 + xy + y^2 \geq 0 \).
     - Notice that \( x^2 + xy + y^2 \) is the sum of squares and a product, which is always non-negative.
  Combining these cases, we conclude that \( x^2 - xy + y^2 \geq |xy| \).
  -/
  cases' le_total 0 (x * y) with h h <;>
  cases' le_total 0 (x - y) with h₁ h₁ <;>
  simp_all only [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 2 * x)]
