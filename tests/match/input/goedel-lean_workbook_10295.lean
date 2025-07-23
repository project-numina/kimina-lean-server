import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $ a,b,c$ are positive real number such that $a+b+c=3$ , prove that $\frac{1}{11+a^{2}}+\frac{1}{11+b^{2}}+\frac{1}{11+c^{2}}\leqslant \frac{1}{4}.$ -/
theorem lean_workbook_10295 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (11 + a^2) + 1 / (11 + b^2) + 1 / (11 + c^2) ≤ 1 / 4  := by
  /-
  We need to prove that for positive real numbers \(a\), \(b\), and \(c\) such that \(a + b + c = 3\), the inequality \(\frac{1}{11 + a^2} + \frac{1}{11 + b^2} + \frac{1}{11 + c^2} \leq \frac{1}{4}\) holds.
  To do this, we will show that the sum of the reciprocals of the expressions involving \(a\), \(b\), and \(c\) is less than or equal to \(\frac{1}{4}\). We will use algebraic manipulation and basic properties of inequalities to achieve this.
  -/
  have h₁ : 0 < a * b * c := by
    -- Since a, b, and c are positive, their product is also positive.
    exact mul_pos (mul_pos ha hb) hc
  have h₂ : a * b * c ≤ 1 := by
    -- Using the fact that a + b + c = 3, we can apply basic inequalities to show that a * b * c ≤ 1.
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h₃ : 1 / (11 + a^2) + 1 / (11 + b^2) + 1 / (11 + c^2) ≤ 1 / 4 := by
    -- Using the fact that a * b * c ≤ 1, we can apply basic inequalities to show the desired result.
    field_simp
    rw [div_le_div_iff]
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- The final inequality follows from the above steps.
  exact h₃
