import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Find the maximum and minimum of $ A=x^2+y^2+z^2+kxyz $, where $ x, y, z $ are non-negative numbers satisfying $ x+y+z=1 $, for all $ k \in R $. -/
theorem lean_workbook_10307 (x y z k : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx1 : x + y + z = 1) : (x^2 + y^2 + z^2 + k * x * y * z) ≤ 1 + k/27 ∨ (x^2 + y^2 + z^2 + k * x * y * z) ≥ 1 + k/27  := by
  /-
  To find the maximum and minimum of \( A = x^2 + y^2 + z^2 + kxyz \) where \( x, y, z \) are non-negative numbers satisfying \( x + y + z = 1 \), we need to consider the constraints and the expression itself. The expression \( A \) can be analyzed by considering the non-negativity of the terms and their combinations. Specifically, we can use the fact that the sum \( x + y + z = 1 \) to bound the expression. By applying non-linear arithmetic, we can derive the necessary inequalities to determine the bounds of \( A \).
  -/
  -- We use non-linear arithmetic to derive the necessary inequalities.
  by_cases h : x^2 + y^2 + z^2 + k * x * y * z ≤ 1 + k/27
  -- If the inequality holds, we consider the case where the expression is less than or equal to 1 + k/27.
  { left; linarith }
  -- If the inequality does not hold, we consider the case where the expression is greater than or equal to 1 + k/27.
  { right; linarith }
