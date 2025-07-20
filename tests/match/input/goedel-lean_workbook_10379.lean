import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c$ be non negative reals such that $a+b+c+ab+bc+ca=6$. Prove that $4(a+b+c)+abc\ge\ 13.$ -/
theorem lean_workbook_10379 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c + a * b + b * c + c * a = 6) : 4 * (a + b + c) + a * b * c ≥ 13  := by
  /-
  Given non-negative real numbers \(a\), \(b\), and \(c\) such that \(a + b + c + ab + bc + ca = 6\), we need to prove that \(4(a + b + c) + abc \geq 13\).
  To prove this, we use the non-linear arithmetic (nlinarith) tactic, which automatically handles inequalities involving polynomials. We provide specific non-negativity conditions to ensure that the squares of the differences and the non-negativity of the variables are respected.
  -/
  -- Use non-linear arithmetic to handle the inequality.
  -- We provide specific non-negativity conditions to ensure the squares of the differences and the non-negativity of the variables are respected.
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha,
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
