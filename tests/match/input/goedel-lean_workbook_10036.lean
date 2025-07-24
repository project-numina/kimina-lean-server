import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c$ be real numbers such that $a^{2}+b^{2}+c^{2}=3$ \nShow: $|a|+|b|+|c|-abc\leq 4$ -/
theorem lean_workbook_10036 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 3) : |a| + |b| + |c| - a * b * c ≤ 4  := by
  /-
  Given real numbers \(a, b, c\) such that \(a^2 + b^2 + c^2 = 3\), we need to show that \(|a| + |b| + |c| - abc \leq 4\). We will consider different cases based on the signs of \(a, b, c\) and use the given condition to derive the inequality.
  -/
  -- Consider different cases based on the signs of a, b, and c
  cases' le_total 0 a with ha ha <;>
  cases' le_total 0 b with hb hb <;>
  cases' le_total 0 c with hc hc <;>
  -- Simplify the absolute values based on the signs
  simp_all only [abs_of_nonneg, abs_of_nonpos, add_left_neg, add_right_neg, add_assoc] <;>
  -- Use linear arithmetic to prove the inequality in each case
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h, sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
