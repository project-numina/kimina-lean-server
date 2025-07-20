import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that for $x, y, z \geq 0$, the following inequality holds: $x^3 + y^3 + z^3 + x^2y + y^2z + z^2x \geq 2(xy^2 + yz^2 + zx^2)$. -/
theorem lean_workbook_10191 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x ^ 3 + y ^ 3 + z ^ 3 + x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≥ 2 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2)  := by
  /-
  To prove the inequality \( x^3 + y^3 + z^3 + x^2y + y^2z + z^2x \geq 2(xy^2 + yz^2 + zx^2) \) for \( x, y, z \geq 0 \), we can use the non-linear arithmetic tactic `nlinarith`. This tactic is designed to handle inequalities involving polynomials and can automatically deduce the desired inequality by considering the non-negativity of various squared terms and the non-negativity of \( x, y, \) and \( z \).
  -/
  -- Use the non-linear arithmetic tactic `nlinarith` to prove the inequality.
  -- This tactic will consider the non-negativity of various squared terms and the non-negativity of `x`, `y`, and `z` to deduce the desired inequality.
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx,
    sq_nonneg (x + y), sq_nonneg (y + z), sq_nonneg (z + x), mul_nonneg (sq_nonneg x) (sq_nonneg y),
    mul_nonneg (sq_nonneg y) (sq_nonneg z), mul_nonneg (sq_nonneg z) (sq_nonneg x)]
