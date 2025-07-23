import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Suppose $y$ between $x$ and $z.$ By AM-GM Inequality, we have \n $4\,xyz \left( xy+zx+yz \right) \left( x+y+z \right) \leqslant [zx(x+y+z)+y(xy+yz+zx)]^2.$ We need to prove that \n $3\,xyz+{x}^{2}y+{y}^{2}z+{z}^{2}x \geqslant xy(x+y+z)+z(xy+yz+zx),$ equivalent to \n $x(x-y)(y-z) \geqslant 0.$ Which is true.\n -/
theorem lean_workbook_10178  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : y ≠ x)
  (h₂ : y ≠ z)
  (h₃ : z ≠ x)
  (h₄ : x + y + z = 1) :
  4 * x * y * z * (x * y + y * z + z * x) * (x + y + z) ≤ (z * x * (x + y + z) + y * (x * y + y * z + z * x))^2  := by
  /-
  Suppose \( y \) is between \( x \) and \( z \). By the AM-GM Inequality, we have:
  \[ 4 \cdot x \cdot y \cdot z \cdot (x \cdot y + y \cdot z + z \cdot x) \cdot (x + y + z) \leq (z \cdot x \cdot (x + y + z) + y \cdot (x \cdot y + y \cdot z + z \cdot x))^2. \]
  We need to prove that:
  \[ 3 \cdot x \cdot y \cdot z + x^2 \cdot y + y^2 \cdot z + z^2 \cdot x \geq x \cdot y \cdot (x + y + z) + z \cdot (x \cdot y + y \cdot z + z \cdot x), \]
  which is equivalent to:
  \[ x \cdot (x - y) \cdot (y - z) \geq 0. \]
  This is true due to the ordering of \( x, y, \) and \( z \).
  -/
  -- Use non-linear arithmetic to prove the inequality.
  nlinarith [sq_nonneg (z * x * (x + y + z) + y * (x * y + y * z + z * x)),
    sq_nonneg (z * x * (x + y + z) - y * (x * y + y * z + z * x)),
    mul_self_nonneg (x - y),
    mul_self_nonneg (y - z),
    mul_self_nonneg (z - x)]
