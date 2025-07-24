import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that for $a, b, c > 0$,\n\n $\frac{a^3 + b^3 + c^3}{3abc} - 1 \geq \frac{3(a^2 + b^2 + c^2)}{ab + bc + ca} - 3$ -/
theorem lean_workbook_10065 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (3 * a * b * c) - 1 ≥ (3 * (a^2 + b^2 + c^2)) / (a * b + b * c + a * c) - 3  := by
  /-
  To prove the inequality \(\frac{a^3 + b^3 + c^3}{3abc} - 1 \geq \frac{3(a^2 + b^2 + c^2)}{ab + bc + ca} - 3\) for \(a, b, c > 0\), we start by simplifying the expressions involved. We use algebraic manipulations and properties of real numbers to show that the left-hand side is indeed greater than or equal to the right-hand side. Specifically, we clear the denominators by multiplying through by the common denominator, simplify the resulting expressions, and then use basic algebraic properties and inequalities to establish the desired result.
  -/
  have h₁ : 0 < a * b * c := by
    -- Since a, b, and c are positive, their product is also positive.
    exact mul_pos (mul_pos ha hb) hc
  have h₂ : 0 < a * b + b * c + a * c := by
    -- Since a, b, and c are positive, the sum of their pairwise products is positive.
    nlinarith [ha, hb, hc]
  -- Clear the denominators by multiplying through by the common denominator.
  field_simp
  -- Simplify the expressions using algebraic properties.
  rw [div_le_div_iff]
  -- Use basic algebraic properties and inequalities to establish the result.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  -- Additional arithmetic simplifications.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  -- Final arithmetic simplification.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
