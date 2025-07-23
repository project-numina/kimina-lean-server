import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- By C-S $\sum_{cyc}\frac{a}{b+c+4d}\geq\frac{(a+b+c+d)^2}{\sum\limits_{cyc}(ab+ac+4da)}=\frac{(a+b+c+d)^2}{5\sum\limits_{cyc}ab+2(ac+bd)}$ . \n Hence, it remains to prove that $3(a^2+b^2+c^2+d^2)-4(ab+bc+cd+da)+2(ac+bd)\geq0$ , which is \n $(a-b+c-d)^2+\sum_{cyc}(a-b)^2\geq0$ . Done! -/
theorem lean_workbook_1018  (a b c d : ℝ) :
  3 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) + 2 * (a * c + b * d) ≥ 0  := by
  /-
  We need to prove that for real numbers \(a, b, c, d\), the inequality \(3(a^2 + b^2 + c^2 + d^2) - 4(ab + bc + cd + da) + 2(ac + bd) \geq 0\) holds. This can be shown using the Cauchy-Schwarz inequality. Specifically, we can rewrite the inequality as:
  \[
  \sum_{\text{cyc}} \frac{a}{b + c + 4d} \geq \frac{(a + b + c + d)^2}{\sum_{\text{cyc}} (ab + ac + 4da)}
  \]
  which simplifies to:
  \[
  \frac{(a + b + c + d)^2}{5 \sum_{\text{cyc}} ab + 2(ac + bd)}
  \]
  Thus, it remains to prove that:
  \[
  3(a^2 + b^2 + c^2 + d^2) - 4(ab + bc + cd + da) + 2(ac + bd) \geq 0
  \]
  This can be further simplified to:
  \[
  (a - b + c - d)^2 + \sum_{\text{cyc}} (a - b)^2 \geq 0
  \]
  which is always non-negative since it is a sum of squares.
  -/
  -- Use the `nlinarith` tactic to handle the non-linear arithmetic.
  -- We provide specific non-negativity conditions for the terms involved.
  nlinarith [sq_nonneg (a - b + c - d), sq_nonneg (a + b - c - d), sq_nonneg (a - b - c + d),
    sq_nonneg (a + b + c - d), sq_nonneg (a + b + c + d), sq_nonneg (a - b + c + d),
    sq_nonneg (a - b - c - d), sq_nonneg (a + b - c + d)]
