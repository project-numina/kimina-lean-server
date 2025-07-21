import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that \(\frac{a}{ab+3}+\frac{b}{bc+3}+\frac{c}{ca+3}\leq\frac{3}{4}\) given \(a,b,c>0\) and \(a^2+b^2+c^2=1\). -/
theorem lean_workbook_10393 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a^2 + b^2 + c^2 = 1) : a / (a * b + 3) + b / (b * c + 3) + c / (c * a + 3) ≤ 3 / 4  := by
  /-
  Given \(a, b, c > 0\) and \(a^2 + b^2 + c^2 = 1\), we need to prove that:
  \[
  \frac{a}{ab + 3} + \frac{b}{bc + 3} + \frac{c}{ca + 3} \leq \frac{3}{4}
  \]
  To do this, we will use the fact that \(a, b, c > 0\) and \(a^2 + b^2 + c^2 = 1\). We will also use the non-negativity of squares to bound the terms.
  -/
  -- Use the fact that \(a, b, c > 0\) and \(a^2 + b^2 + c^2 = 1\) to bound the terms.
  have h₀ : a / (a * b + 3) ≤ a / 3 := by
    -- Since \(a, b, c > 0\) and \(a^2 + b^2 + c^2 = 1\), we can use the non-negativity of squares to bound \(a / (a * b + 3)\).
    apply div_le_div_of_le_left ha.le (by nlinarith) (by nlinarith)
  have h₁ : b / (b * c + 3) ≤ b / 3 := by
    -- Similarly, bound \(b / (b * c + 3)\).
    apply div_le_div_of_le_left hb.le (by nlinarith) (by nlinarith)
  have h₂ : c / (c * a + 3) ≤ c / 3 := by
    -- Finally, bound \(c / (c * a + 3)\).
    apply div_le_div_of_le_left hc.le (by nlinarith) (by nlinarith)
  -- Combine the bounds to get the final inequality.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
