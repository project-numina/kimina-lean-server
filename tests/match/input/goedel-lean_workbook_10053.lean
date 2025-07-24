import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c \geq 0 $ and $ ab+bc+ca+2abc=1$ . Prove that \n $$a^2+ 2b^4+ c^2\ge \frac{5}{8}$$ $$ 2a^4+b^2+ 2c^4\ge \frac{1}{2}$$ $$ 2a^3+3b^4+2c^3 \ge \frac{11}{16}$$ $$ 3a^4+ 2b^3+3c^4\ge \frac{5}{8}$$ -/
theorem lean_workbook_10053 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a * b + b * c + c * a + 2 * a * b * c = 1) : a^2 + 2 * b^4 + c^2 ≥ 5 / 8 ∧ 2 * a^4 + b^2 + 2 * c^4 ≥ 1 / 2 ∧ 2 * a^3 + 3 * b^4 + 2 * c^3 ≥ 11 / 16 ∧ 3 * a^4 + 2 * b^3 + 3 * c^4 ≥ 5 / 8  := by
  /-
  Given \(a, b, c \geq 0\) and \(ab + bc + ca + 2abc = 1\), we need to prove the following inequalities:
  1. \(a^2 + 2b^4 + c^2 \geq \frac{5}{8}\)
  2. \(2a^4 + b^2 + 2c^4 \geq \frac{1}{2}\)
  3. \(2a^3 + 3b^4 + 2c^3 \geq \frac{11}{16}\)
  4. \(3a^4 + 2b^3 + 3c^4 \geq \frac{5}{8}\)
  To prove these inequalities, we use algebraic manipulation and simplification, followed by numerical verification using `nlinarith`.
  -/
  constructor
  -- Prove the first inequality: a^2 + 2b^4 + c^2 ≥ 5/8
  -- Use nlinarith to verify the inequality after algebraic manipulation
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (c - a)]
  constructor
  -- Prove the second inequality: 2a^4 + b^2 + 2c^4 ≥ 1/2
  -- Use nlinarith to verify the inequality after algebraic manipulation
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (c - a)]
  constructor
  -- Prove the third inequality: 2a^3 + 3b^4 + 2c^3 ≥ 11/16
  -- Use nlinarith to verify the inequality after algebraic manipulation
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (c - a)]
  -- Prove the fourth inequality: 3a^4 + 2b^3 + 3c^4 ≥ 5/8
  -- Use nlinarith to verify the inequality after algebraic manipulation
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (c - a)]
