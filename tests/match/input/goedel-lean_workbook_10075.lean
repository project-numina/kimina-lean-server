import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let a; b; c be positive real numbers such that $abc$ = 1, Prove that $a^2 + b^2 + c^2 \geq a + b + c$ -/
theorem lean_workbook_10075 (a b c : ℝ) (h : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c  := by
  /-
  Given positive real numbers \(a\), \(b\), and \(c\) such that \(abc = 1\), we need to prove that \(a^2 + b^2 + c^2 \geq a + b + c\).
  To prove this, we use the non-linear arithmetic (nlinarith) tactic, which automatically handles inequalities involving squares and sums. Specifically, we consider the squares of the differences \(a - 1\), \(b - 1\), and \(c - 1\), and use the fact that these squares are non-negative to derive the desired inequality.
  -/
  -- Use non-linear arithmetic to handle the inequality involving squares and sums.
  -- We consider the squares of the differences (a - 1), (b - 1), and (c - 1), and use the fact that these squares are non-negative.
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
