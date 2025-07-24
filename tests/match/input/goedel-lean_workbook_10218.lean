import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-  $(x^2+y^2+z^2)(1+1+1)\geq (x+y+z)^{2}$ -/
theorem lean_workbook_10218 (x y z : ℝ) : (x ^ 2 + y ^ 2 + z ^ 2) * (1 + 1 + 1) ≥ (x + y + z) ^ 2  := by
  /-
  We need to show that for real numbers \( x \), \( y \), and \( z \), the inequality \((x^2 + y^2 + z^2)(1 + 1 + 1) \geq (x + y + z)^2\) holds. This can be derived using the non-negativity of squares and basic algebraic manipulations.
  -/
  -- Use non-linear arithmetic to prove the inequality.
  -- The `nlinarith` tactic will handle the proof by leveraging the non-negativity of squares.
  -- Specifically, it will use the fact that the square of any real number is non-negative.
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x + y), sq_nonneg (y + z), sq_nonneg (z + x)]
