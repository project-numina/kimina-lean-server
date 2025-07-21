import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Plugging that into the the top gives $\frac{3 - (4p+3)}{8p^2-8p-3} = \frac{-4p}{8p^2-8p-3}.$ -/
theorem lean_workbook_102  (p : ℝ)
  (h₀ : 8 * p^2 - 8 * p - 3 ≠ 0)
  (h₁ : 3 - (4 * p + 3) ≠ 0) :
  (3 - (4 * p + 3)) / (8 * p^2 - 8 * p - 3) = (-4 * p) / (8 * p^2 - 8 * p - 3)  := by
  /-
  We need to show that for a real number \( p \), given the conditions \( 8p^2 - 8p - 3 \neq 0 \) and \( 3 - (4p + 3) \neq 0 \), the equation \(\frac{3 - (4p + 3)}{8p^2 - 8p - 3} = \frac{-4p}{8p^2 - 8p - 3}\) holds. This can be achieved by simplifying the numerator on the left-hand side.
  First, we simplify the numerator \( 3 - (4p + 3) \):
  \[ 3 - (4p + 3) = 3 - 4p - 3 = -4p \]
  Thus, the left-hand side of the equation becomes:
  \[ \frac{3 - (4p + 3)}{8p^2 - 8p - 3} = \frac{-4p}{8p^2 - 8p - 3} \]
  This directly matches the right-hand side of the equation, confirming the equality.
  -/
  -- Simplify the numerator 3 - (4 * p + 3) to -4 * p
  field_simp [h₀, h₁, sub_eq_zero, add_left_neg, add_right_neg, sub_add_cancel, sub_self, zero_add,
    mul_comm]
  -- Use linarith to confirm the equality
  <;> linarith
