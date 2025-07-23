import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let be $ a,b\in \mathbb{R}$ such that $ 16a^4+12a^2+9b^2+8a\le 3$ . Prove that : $ a(8a^2+b)\le 1$ -/
theorem lean_workbook_10364 (a b : ℝ) (h : 16 * a ^ 4 + 12 * a ^ 2 + 9 * b ^ 2 + 8 * a ≤ 3) :
  a * (8 * a ^ 2 + b) ≤ 1  := by
  /-
  Given \( a, b \in \mathbb{R} \) such that \( 16a^4 + 12a^2 + 9b^2 + 8a \leq 3 \), we need to prove that \( a(8a^2 + b) \leq 1 \).
  First, we use the non-negativity of squares to establish several inequalities. Specifically, we consider the squares of expressions involving \( a \) and \( b \). By leveraging these inequalities, we can derive the desired result using non-linear arithmetic.
  -/
  -- Use non-linear arithmetic to prove the inequality.
  -- We provide several non-negative expressions to help the arithmetic solver.
  nlinarith [sq_nonneg (4 * a ^ 2 + b / 4), sq_nonneg (4 * a ^ 2 - b / 4),
    sq_nonneg (2 * a - b / 2), sq_nonneg (2 * a + b / 2),
    sq_nonneg (2 * a ^ 2 - b / 2), sq_nonneg (2 * a ^ 2 + b / 2),
    sq_nonneg (b / 2 - 2 * a), sq_nonneg (b / 2 + 2 * a)]
