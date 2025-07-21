import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- prove that \n $(x+y+z)^5-x^5-y^5-z^5\geq 60xyz(xy+yz+zx)$\nif $x,y,z$ are positive reals -/
theorem lean_workbook_10039 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 5 - x ^ 5 - y ^ 5 - z ^ 5 ≥ 60 * x * y * z * (x * y + y * z + z * x)  := by
  /-
  To prove the inequality \((x + y + z)^5 - x^5 - y^5 - z^5 \geq 60xyz(xy + yz + zx)\) for positive real numbers \(x, y, z\), we can use the non-linear arithmetic tactic (`nlinarith`). This tactic is designed to handle inequalities involving polynomials and can automatically deduce the desired inequality by considering the non-negativity of various squared and multiplied terms.
  -/
  -- Use the non-linear arithmetic tactic to prove the inequality.
  -- This tactic will consider the non-negativity of various squared and multiplied terms to deduce the desired inequality.
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
    sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2),
    sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    sq_nonneg (x * y + y * z), sq_nonneg (y * z + z * x), sq_nonneg (z * x + x * y)]
