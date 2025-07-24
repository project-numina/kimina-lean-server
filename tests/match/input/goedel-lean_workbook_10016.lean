import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c\ge 0$ and $ a^2+b^2+c^2 =2.$ Prove that $\frac{\sqrt{b^2+c^2}}{3-a}+\frac{\sqrt{c^2+a^2}}{3-b}\le 2\sqrt{ \frac{2}{7}}$ -/
theorem lean_workbook_10016 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) (h : a^2 + b^2 + c^2 = 2) : (Real.sqrt (b^2 + c^2) / (3 - a) + Real.sqrt (c^2 + a^2) / (3 - b)) ≤ 2 * Real.sqrt (2 / 7)  := by
  /-
  Given \(a, b, c \ge 0\) and \(a^2 + b^2 + c^2 = 2\), we need to prove that:
  \[
  \frac{\sqrt{b^2 + c^2}}{3 - a} + \frac{\sqrt{c^2 + a^2}}{3 - b} \le 2 \sqrt{\frac{2}{7}}
  \]
  To prove this, we use the fact that the square root function is monotonic and that the inequality holds due to the properties of squares and the given conditions. Specifically, we use the non-negativity of squares and the given conditions to establish the inequality.
  -/
  -- Use non-linear arithmetic to handle the inequality.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_sqrt (show 0 ≤ 2 by norm_num),
    mul_self_nonneg (a + b + c - 3)]
