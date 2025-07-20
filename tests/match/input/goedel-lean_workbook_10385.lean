import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $ \frac{\cos\theta + \sqrt{3}\sin\theta}{2} = \cos\left(\theta - \frac{\pi}{3}\right)$ -/
theorem lean_workbook_10385 : ∀ θ : ℝ, (cos θ + Real.sqrt 3 * sin θ) / 2 = cos (θ - Real.pi / 3)  := by
  /-
  To prove that \( \frac{\cos\theta + \sqrt{3}\sin\theta}{2} = \cos\left(\theta - \frac{\pi}{3}\right) \), we start by using the angle subtraction formula for cosine. Specifically, we use the identity \( \cos(\theta - \phi) = \cos\theta\cos\phi + \sin\theta\sin\phi \). Here, \( \phi = \frac{\pi}{3} \). We know the values of \( \cos\frac{\pi}{3} \) and \( \sin\frac{\pi}{3} \), which are \( \frac{1}{2} \) and \( \frac{\sqrt{3}}{2} \), respectively. Substituting these values into the formula, we get:
  \[
  \cos\left(\theta - \frac{\pi}{3}\right) = \cos\theta \cdot \frac{1}{2} + \sin\theta \cdot \frac{\sqrt{3}}{2}
  \]
  Simplifying this expression, we obtain:
  \[
  \cos\left(\theta - \frac{\pi}{3}\right) = \frac{1}{2} \cos\theta + \frac{\sqrt{3}}{2} \sin\theta
  \]
  This matches the left-hand side of the original equation when multiplied by 2:
  \[
  2 \left( \frac{1}{2} \cos\theta + \frac{\sqrt{3}}{2} \sin\theta \right) = \cos\theta + \sqrt{3} \sin\theta
  \]
  Thus, we have shown that:
  \[
  \frac{\cos\theta + \sqrt{3} \sin\theta}{2} = \cos\left(\theta - \frac{\pi}{3}\right)
  \]
  -/
  intro θ
  -- Use the angle subtraction formula for cosine: cos(θ - φ) = cos(θ)cos(φ) + sin(θ)sin(φ)
  simp only [cos_sub, cos_pi_div_three, sin_pi_div_three, mul_one, mul_div_cancel_left, mul_comm]
  -- Simplify the expression to match the left-hand side of the original equation
  ring
  -- Normalize numerical values
  <;> norm_num
  -- Simplify using the square root properties
  <;> simp [Real.sqrt_eq_iff_sq_eq]
  -- Normalize the expression again
  <;> ring_nf
  -- Normalize numerical values again
  <;> norm_num
  -- Use the square root properties to finalize the proof
  <;> linarith [Real.sqrt_nonneg 3]
