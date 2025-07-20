import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove $(a-b)^{2}+(b-c)^{2}+(c-a)^{2}\ge 0$ -/
theorem lean_workbook_10087 (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0  := by
  /-
  To prove that \((a - b)^2 + (b - c)^2 + (c - a)^2 \geq 0\) for any real numbers \(a\), \(b\), and \(c\), we can use the fact that the square of any real number is non-negative. Specifically, each term \((a - b)^2\), \((b - c)^2\), and \((c - a)^2\) is a square of a real number, hence non-negative. The sum of non-negative numbers is also non-negative. Therefore, the sum \((a - b)^2 + (b - c)^2 + (c - a)^2\) is non-negative.
  -/
  -- Use the `nlinarith` tactic to handle non-linear arithmetic expressions.
  -- This tactic will automatically apply known facts about non-negative numbers, such as squares, and sums of non-negative numbers.
  nlinarith
