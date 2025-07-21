import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Squaring both sides for $t>1$ we get after simplification: $2t\sqrt{t+8}>7t-8$. -/
theorem lean_workbook_10305 : ∀ t : ℝ, 1 < t → 2 * t * Real.sqrt (t + 8) > 7 * t - 8  := by
  /-
  For any real number \( t \) greater than 1, we need to show that \( 2t\sqrt{t+8} > 7t - 8 \). We start by noting that since \( t > 1 \), \( t + 8 > 0 \), ensuring that the square root is defined and positive. We then square both sides of the inequality to eliminate the square root. After simplifying, we use algebraic manipulation and properties of inequalities to show that the inequality holds.
  -/
  -- Introduce the variable t and the assumption t > 1.
  intro t h
  -- Show that t + 8 > 0 since t > 1.
  have h₀ : 0 < t + 8 := by linarith
  -- Use the property that the square root of a positive number is positive.
  have h₁ : 0 < Real.sqrt (t + 8) := Real.sqrt_pos.2 h₀
  -- Square both sides of the inequality to eliminate the square root.
  nlinarith [sq_sqrt (by linarith : 0 ≤ t + 8), sq_nonneg (t - 4)]
