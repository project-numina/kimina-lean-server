import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove $x^2 + x + y^2 + y + 1 \geq x y$ for all real x,y -/
theorem lean_workbook_1003 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y  := by
  /-
  To prove the inequality \( x^2 + x + y^2 + y + 1 \geq x y \) for all real numbers \( x \) and \( y \), we start by considering the expression \( x^2 + x + y^2 + y + 1 - x y \). We need to show that this expression is non-negative for all \( x \) and \( y \).
  First, we rewrite the expression:
  \[ x^2 + x + y^2 + y + 1 - x y \]
  Next, we use the fact that the square of any real number is non-negative. We consider the squares of the following expressions:
  \[ (x + 1)^2 \]
  \[ (y + 1)^2 \]
  \[ (x - y)^2 \]
  Expanding these squares, we get:
  \[ (x + 1)^2 = x^2 + 2x + 1 \]
  \[ (y + 1)^2 = y^2 + 2y + 1 \]
  \[ (x - y)^2 = x^2 - 2xy + y^2 \]
  Adding these together, we have:
  \[ (x + 1)^2 + (y + 1)^2 + (x - y)^2 = x^2 + 2x + 1 + y^2 + 2y + 1 + x^2 - 2xy + y^2 = 2x^2 + 2y^2 + 2x + 2y + 2 - 2xy \]
  Simplifying, we get:
  \[ 2x^2 + 2y^2 + 2x + 2y + 2 - 2xy = 2(x^2 + x + y^2 + y) + 2(1 - xy) \]
  Since squares are non-negative, the sum \( (x + 1)^2 + (y + 1)^2 + (x - y)^2 \) is non-negative. Therefore, \( 2(x^2 + x + y^2 + y) + 2(1 - xy) \geq 0 \), which implies:
  \[ x^2 + x + y^2 + y + 1 - xy \geq 0 \]
  Thus, we have:
  \[ x^2 + x + y^2 + y + 1 \geq x y \]
  -/
  -- Use the fact that squares are non-negative to prove the inequality.
  -- Consider the squares of the following expressions:
  -- (x + 1)^2, (y + 1)^2, and (x - y)^2.
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y),
    sq_nonneg (x + y), sq_nonneg (x + y + 1), sq_nonneg (x + y - 1)]
