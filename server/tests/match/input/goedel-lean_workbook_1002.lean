import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Explain why $|y| > |2y^2|$ when $-\frac{1}{2} < y < 0$. -/
theorem lean_workbook_1002 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2|  := by
  /-
  To prove that \( |y| > |2y^2| \) given \( -\frac{1}{2} < y < 0 \), we analyze the properties of the absolute values and the inequalities involving \( y \) and \( 2y^2 \).
  1. **Case Analysis on Absolute Values**:
     - We consider the cases where \( y \) and \( 2y^2 \) are either non-negative or non-positive.
     - For each combination of these cases, we simplify the expressions using the properties of absolute values.
  2. **Simplification and Inequality Verification**:
     - After simplifying the expressions, we use the given inequalities \( -\frac{1}{2} < y < 0 \) to verify the inequality \( |y| > |2y^2| \).
  -/
  -- Consider the cases where y and 2y^2 are either non-negative or non-positive.
  cases' abs_cases y with h₀ h₀ <;>
  cases' abs_cases (2 * y ^ 2) with h₁ h₁ <;>
  -- Simplify the expressions using the properties of absolute values.
  simp_all only [abs_of_nonneg, abs_of_nonpos, neg_mul, neg_neg, mul_neg, neg_add_rev] <;>
  -- Use the given inequalities to verify the inequality |y| > |2y^2|.
  nlinarith
