import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,\ b,\ c$ be real numbers such that $|a-1|+|b-1|+|c-1|+|a+1|+|b+1|+|c+1|=12$ . Prove that : $a^2+b^2+c^2\geq 12$ . When does equality hold? -/
theorem lean_workbook_1036 (a b c : ℝ) (h : abs (a - 1) + abs (b - 1) + abs (c - 1) + abs (a + 1) + abs (b + 1) + abs (c + 1) = 12) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 12  := by
  /-
  Given real numbers \(a\), \(b\), and \(c\) such that \(|a-1| + |b-1| + |c-1| + |a+1| + |b+1| + |c+1| = 12\), we need to prove that \(a^2 + b^2 + c^2 \geq 12\).
  To prove this, we consider the cases where each of \(a-1\), \(b-1\), \(c-1\), \(a+1\), \(b+1\), and \(c+1\) are non-negative or non-positive. By analyzing these cases, we can simplify the absolute values and use algebraic manipulations to show that the sum of the squares of \(a\), \(b\), and \(c\) is at least 12.
  -/
  -- Consider the cases where each of the expressions is non-negative or non-positive.
  cases' le_total 0 (a - 1) with h₀ h₀ <;>
    cases' le_total 0 (b - 1) with h₁ h₁ <;>
      cases' le_total 0 (c - 1) with h₂ h₂ <;>
        cases' le_total 0 (a + 1) with h₃ h₃ <;>
          cases' le_total 0 (b + 1) with h₄ h₄ <;>
            cases' le_total 0 (c + 1) with h₅ h₅ <;>
              -- Simplify the absolute values based on the non-negativity or non-positivity.
              simp_all only [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
                -- Use algebraic manipulations and inequalities to show the desired result.
                nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]
