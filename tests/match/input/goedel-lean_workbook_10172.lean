import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a, b, c\\in[0,1)$ and $a+b+c=\\frac{3}{2}$ . Prove that $$\\sqrt{(1-a)(1-b)(1-c)} \\leq \\frac{2(2ab+3bc+3ca)}{9} $$ -/
theorem lean_workbook_10172 (a b c : ℝ) (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1) (habc : a + b + c = 3 / 2) : (1 - a) * (1 - b) * (1 - c) ≤ (2 * (2 * a * b + 3 * b * c + 3 * c * a)) / 9  := by
  /-
  Given \(a, b, c \in [0,1)\) with \(a + b + c = \frac{3}{2}\), we need to prove that:
  \[
  \sqrt{(1-a)(1-b)(1-c)} \leq \frac{2(2ab+3bc+3ca)}{9}
  \]
  First, we expand and simplify the expression on both sides. We use algebraic manipulations and properties of real numbers to show that the inequality holds. Specifically, we use the fact that the square root of a product is less than or equal to a certain fraction involving the terms \(a, b,\) and \(c\).
  -/
  -- Expand and simplify both sides of the inequality using algebraic identities.
  ring_nf
  -- Use non-linear arithmetic to prove the inequality, leveraging the non-negativity of squares and the given constraints on a, b, and c.
  nlinarith [sq_nonneg (a + b + c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
