import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- prove that $a^{3}+b^{3}+c^{3}+{\frac {15\,abc}{4}} \geq \frac{1}{4}$ given $a, b, c,$ are non-negative reals such that $a+b+c=1$ -/
theorem lean_workbook_10009 (a b c: ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1): a^3 + b^3 + c^3 + (15 * a * b * c)/4 ≥ 1/4  := by
  /-
  Given non-negative real numbers \(a\), \(b\), and \(c\) such that \(a + b + c = 1\), we need to prove that \(a^3 + b^3 + c^3 + \frac{15abc}{4} \geq \frac{1}{4}\).
  1. **Case Analysis**: We analyze different cases based on the relationships between \(a\), \(b\), and \(c\).
  2. **Non-negativity and Bounds**: Utilize the non-negativity of \(a\), \(b\), and \(c\) and the fact that their sum is 1.
  3. **Simplification and Comparison**: Use algebraic simplification and numerical comparison to show the inequality holds.
  -/
  -- Consider different cases based on the relationships between a, b, and c
  cases' le_total a b with hab hab <;> cases' le_total b c with hbc hbc <;> cases' le_total c a with hac hac <;>
  -- Use non-negativity of a, b, and c and their sum to prove the inequality
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c)]
