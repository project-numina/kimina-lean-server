import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c \geq 0$ and $a^3+b^3+c^3+3abc=6$ . Prove that: $ a^2+b^2+c^2 \geq 3 $ -/
theorem lean_workbook_10090 (a b c : ℝ) (h : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a^3+b^3+c^3+3*a*b*c=6) :
  a^2+b^2+c^2 ≥ 3  := by
  /-
  Given \(a, b, c \geq 0\) and \(a^3 + b^3 + c^3 + 3abc = 6\), we need to prove that \(a^2 + b^2 + c^2 \geq 3\).
  1. Consider the expressions \((a + b + c)^2\), \((a - b)^2\), \((a - c)^2\), \((b - c)^2\), \((a - 1)^2\), \((b - 1)^2\), and \((c - 1)^2\). Each of these expressions is a square, hence non-negative.
  2. Using the non-negativity of squares, we can derive inequalities that involve \(a, b, c\) and constants.
  3. By combining these inequalities, we can show that \(a^2 + b^2 + c^2 \geq 3\).
  -/
  -- Use non-linear arithmetic to handle the inequalities derived from the squares.
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
