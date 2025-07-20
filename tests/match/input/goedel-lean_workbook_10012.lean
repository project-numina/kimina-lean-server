import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a$ , $b$ be real positive numbers such that $a\geq 2b$ Prove that $\frac{a^2}{b} + \frac{b^2}{a}$ $\geq$ $\frac{9a}{4}$ -/
theorem lean_workbook_10012 (a b : ℝ) (h₁ : 0 < a ∧ 0 < b) (h₂ : a ≥ 2 * b) : (a ^ 2 / b + b ^ 2 / a) ≥ 9 * a / 4  := by
  /-
  Given positive real numbers \(a\) and \(b\) such that \(a \geq 2b\), we need to prove that \(\frac{a^2}{b} + \frac{b^2}{a} \geq \frac{9a}{4}\).
  1. Start by simplifying the expression \(\frac{a^2}{b} + \frac{b^2}{a}\).
  2. Use the fact that \(a \geq 2b\) to apply algebraic manipulations and inequalities.
  3. Utilize the non-negativity of squares and arithmetic operations to derive the desired inequality.
  -/
  -- Simplify the expression by clearing denominators using field_simp.
  field_simp [h₁.1.ne', h₁.2.ne']
  -- Use the fact that a ≥ 2b to apply algebraic inequalities.
  rw [div_le_div_iff] <;>
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a + 2 * b), sq_nonneg (a - b), sq_nonneg (a + b)]
