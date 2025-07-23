import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that \n $\forall x,y,z \in \mathbb{R} ; (x+y+z=0) \Longrightarrow (x^3+y^3+z^3=3xyz)$ -/
theorem lean_workbook_10145 (x y z : ℝ) (h : x + y + z = 0) :
  x^3 + y^3 + z^3 = 3 * x * y * z  := by
  /-
  Given \( x, y, z \in \mathbb{R} \) such that \( x + y + z = 0 \), we need to show that \( x^3 + y^3 + z^3 = 3xyz \).
  1. From the given equation \( x + y + z = 0 \), we can express \( z \) as \( z = -x - y \).
  2. Substitute \( z = -x - y \) into the expression \( x^3 + y^3 + z^3 \).
  3. Simplify the resulting expression using algebraic identities and properties.
  4. Recognize that the simplified expression matches the form \( 3xyz \).
  -/
  -- From the given equation x + y + z = 0, express z in terms of x and y.
  have h₁ : z = -x - y := by linarith
  -- Substitute z = -x - y into the expression x^3 + y^3 + z^3.
  simp only [h₁, add_assoc, add_left_comm, add_right_comm, add_comm]
  -- Simplify the expression using algebraic identities.
  ring_nf
  -- Recognize that the simplified expression matches the form 3xyz.
  <;> linarith
