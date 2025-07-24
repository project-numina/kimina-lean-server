import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $ a,b,c,d $ be reals such that $ a+b+c+d=4 $ and $a^2+b^2+c^2+d^2=18.$ Prove that $ |ab-cd|\leq 9$ -/
theorem lean_workbook_10236 (a b c d : ℝ) (h₁ : a + b + c + d = 4) (h₂ : a^2 + b^2 + c^2 + d^2 = 18) : |a * b - c * d| ≤ 9  := by
  /-
  Given real numbers \(a, b, c, d\) such that \(a + b + c + d = 4\) and \(a^2 + b^2 + c^2 + d^2 = 18\), we need to prove that \(|ab - cd| \leq 9\).
  To prove this, we use the properties of squares and the non-negativity of real numbers. Specifically, we consider the expressions \((a - b)^2\), \((a + b)^2\), \((c - d)^2\), \((c + d)^2\), \((a - c)^2\), \((a + c)^2\), \((b - d)^2\), and \((b + d)^2\). By leveraging the non-negativity of these squares and the given conditions, we can derive the desired inequality.
  -/
  -- Use the non-negativity of squares to derive the inequality
  have h₃ := sq_nonneg (a - b) -- The square of any real number is non-negative
  have h₄ := sq_nonneg (a + b) -- The square of any real number is non-negative
  have h₅ := sq_nonneg (c - d) -- The square of any real number is non-negative
  have h₆ := sq_nonneg (c + d) -- The square of any real number is non-negative
  have h₇ := sq_nonneg (a - c) -- The square of any real number is non-negative
  have h₈ := sq_nonneg (a + c) -- The square of any real number is non-negative
  have h₉ := sq_nonneg (b - d) -- The square of any real number is non-negative
  have h₁₀ := sq_nonneg (b + d) -- The square of any real number is non-negative
  -- Combine the non-negativity properties with the given conditions to derive the inequality
  simp only [abs_le, sub_nonneg, sub_nonpos] at *
  -- Use linear arithmetic to conclude the proof
  constructor <;> nlinarith
