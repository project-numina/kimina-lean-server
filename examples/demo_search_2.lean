import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c>0$ . Prove that: $\frac{a^{2}}{b+c}+\frac{b^{2}}{a+c}+\frac{16c^{2}}{a+b}\geq \frac{1}{9}(64c-a-b)$ -/
theorem lean_workbook_10058 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (a + c) + 16 * c^2 / (a + b)) ≥ (1 / 9) * (64 * c - a - b)  := by
  have h₁ : 0 < a + b + c := by linarith
  have h₂ : 0 < a * b := by positivity
  have h₃ : 0 < a * c := by positivity
  have h₄ : 0 < b * c := by positivity
  field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne']
  rw [div_le_div_iff]
  nlinarith [ha, hb, hc]