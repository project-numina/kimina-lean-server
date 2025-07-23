import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c,d\in \mathbb{R}$ such that $ab=1$ and $ac+bd=2$ . Prove: $1-cd\ge 0$ -/
theorem lean_workbook_10144 (a b c d : ℝ) (hab : a * b = 1) (h : a * c + b * d = 2) : 1 - c * d ≥ 0  := by
  /-
  Given \(a, b, c, d \in \mathbb{R}\) such that \(ab = 1\) and \(ac + bd = 2\), we need to prove that \(1 - cd \geq 0\).
  1. Start by considering the expression \(1 - cd\).
  2. Use the given conditions \(ab = 1\) and \(ac + bd = 2\).
  3. Apply the non-negativity of squares to derive the desired inequality.
  -/
  -- Use the non-negativity of squares to derive the inequality.
  -- Specifically, consider the squares of the differences (a * c - b * d) and (a * d + b * c).
  nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c), sq_nonneg (a * c + b * d)]
