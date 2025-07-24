import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $x, y, z \ge 0$, prove: $\frac{3}{2} (x+y+z)[3(x+y+z)^2+xy+yz+zx] \ge (3x+y+z)(3y+x+z)(3z+x+y)$ -/
theorem lean_workbook_10096 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (3 / 2) * (x + y + z) * (3 * (x + y + z) ^ 2 + x * y + x * z + y * z) ≥ (3 * x + y + z) * (3 * y + x + z) * (3 * z + x + y)  := by
  /-
  We need to prove that for non-negative real numbers \( x, y, z \), the inequality \(\frac{3}{2} (x+y+z)[3(x+y+z)^2+xy+yz+zx] \ge (3x+y+z)(3y+x+z)(3z+x+y)\) holds. This can be shown using non-linear arithmetic (nlinarith) which simplifies the inequality by leveraging the non-negativity of squares and other algebraic properties.
  -/
  -- Use non-linear arithmetic to prove the inequality.
  -- nlinarith will handle the non-linear parts of the inequality, leveraging the non-negativity of squares and other algebraic properties.
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx]
