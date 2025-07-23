import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $(a-1)^2(85a^4-294a^3+506a^2-438a+213)\geq0$. -/
theorem lean_workbook_10290 (a : ℝ) : (a - 1) ^ 2 * (85 * a ^ 4 - 294 * a ^ 3 + 506 * a ^ 2 - 438 * a + 213) ≥ 0  := by
  /-
  To prove that \((a-1)^2(85a^4-294a^3+506a^2-438a+213) \geq 0\), we can use the properties of non-negative numbers. Specifically, we note that \((a-1)^2\) is always non-negative because it is a square of a real number. Additionally, the polynomial \(85a^4 - 294a^3 + 506a^2 - 438a + 213\) is non-negative for all real numbers \(a\). Therefore, the product of a non-negative number \((a-1)^2\) and a non-negative polynomial \(85a^4 - 294a^3 + 506a^2 - 438a + 213\) is also non-negative.
  -/
  -- Use the property that the product of a non-negative number and a non-negative polynomial is non-negative.
  apply mul_nonneg
  -- Show that \((a-1)^2\) is non-negative because it is a square.
  exact pow_two_nonneg (a - 1)
  -- Show that the polynomial \(85a^4 - 294a^3 + 506a^2 - 438a + 213\) is non-negative for all real numbers \(a\).
  nlinarith [sq_nonneg (a ^ 2 - a), sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 2 * a), sq_nonneg (a ^ 2 - 3 * a), sq_nonneg (a ^ 2 - 4 * a), sq_nonneg (a ^ 2 - 5 * a), sq_nonneg (a ^ 2 - 6 * a), sq_nonneg (a ^ 2 - 7 * a), sq_nonneg (a ^ 2 - 8 * a), sq_nonneg (a ^ 2 - 9 * a), sq_nonneg (a ^ 2 - 10 * a)]
