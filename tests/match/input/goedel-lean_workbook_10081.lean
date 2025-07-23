import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- For $a, b, c>0, a^2+b^2+c^2=1$ prove that \n $abc\left(\frac{a}{a^4+a^2+bc}+\frac{b}{b^4+b^2+ca}+\frac{c}{c^4+c^2+ab}\right)\le\frac{3}{4+(\sqrt{ab}+\sqrt{bc}+\sqrt{ca})^2}$ -/
theorem lean_workbook_10081 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a * b * c * (a / (a^4 + a^2 + b * c) + b / (b^4 + b^2 + c * a) + c / (c^4 + c^2 + a * b)) ≤ 3 / (4 + (Real.sqrt (a * b) + Real.sqrt (b * c) + Real.sqrt (c * a))^2)  := by
  /-
  To prove the inequality \( abc \left( \frac{a}{a^4 + a^2 + b c} + \frac{b}{b^4 + b^2 + c a} + \frac{c}{c^4 + c^2 + a b} \right) \leq \frac{3}{4 + (\sqrt{a b} + \sqrt{b c} + \sqrt{c a})^2} \) given \( a, b, c > 0 \) and \( a^2 + b^2 + c^2 = 1 \), we start by simplifying the expression using algebraic manipulations and properties of real numbers. We then apply non-linear arithmetic to establish the inequality.
  -/
  -- Simplify the expression using algebraic manipulations.
  simp_all only [mul_add, mul_sub, mul_one, mul_div_cancel_left, mul_comm]
  -- Apply non-linear arithmetic to establish the inequality.
  nlinarith [sq_nonneg (a - b)]
