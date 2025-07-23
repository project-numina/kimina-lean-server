import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $ a,b,c > 0$ be such that $ a + b + c = 1$ . Find min. value of $ \frac {2 - a^2}{1 - a} + \frac {2 - b^2}{1 - b} + \frac {2 - c^2}{1 - c}$ . -/
theorem lean_workbook_10358 (a b c : ℝ) (ha : a > 0 ∧ a + b + c = 1) (hb : b > 0 ∧ a + b + c = 1) (hc : c > 0 ∧ a + b + c = 1): (17/2 : ℝ) ≤  (2 - a^2)/(1 - a) + (2 - b^2)/(1 - b) + (2 - c^2)/(1 - c)  := by
  /-
  Given \( a, b, c > 0 \) such that \( a + b + c = 1 \), we aim to find the minimum value of the expression \( \frac{2 - a^2}{1 - a} + \frac{2 - b^2}{1 - b} + \frac{2 - c^2}{1 - c} \).
  1. **Non-negativity of the denominators**: Since \( a, b, c > 0 \) and \( a + b + c = 1 \), it follows that \( 1 - a, 1 - b, 1 - c > 0 \).
  2. **Simplifying the expression**: Each term \( \frac{2 - a^2}{1 - a} \), \( \frac{2 - b^2}{1 - b} \), and \( \frac{2 - c^2}{1 - c} \) can be rewritten using the fact that \( a + b + c = 1 \).
  3. **Combining the terms**: By combining these terms, we can derive a lower bound for the sum.
  4. **Using algebraic manipulation and inequalities**: Utilize algebraic manipulation and inequalities to show that the sum of these terms is at least \( \frac{17}{2} \).
  -/
  -- Show that the denominators are positive.
  have h₀ : 0 < 1 - a := by linarith
  have h₁ : 0 < 1 - b := by linarith
  have h₂ : 0 < 1 - c := by linarith
  -- Use the fact that the denominators are positive to simplify the expression.
  have h₃ : 0 < (1 - a) * (1 - b) := by positivity
  have h₄ : 0 < (1 - a) * (1 - b) * (1 - c) := by positivity
  -- Use algebraic manipulation and inequalities to derive the lower bound.
  field_simp [h₀, h₁, h₂]
  rw [div_le_div_iff] <;>
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
