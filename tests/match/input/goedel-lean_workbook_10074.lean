import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $x,y \in[0,1]$ then $(1-x)(1-y) \ge 0 \Rightarrow x+y \le 1+xy$ . -/
theorem lean_workbook_10074  (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y)
  (h₁ : x ≤ 1 ∧ y ≤ 1)
  (h₂ : (1 - x) * (1 - y) ≥ 0) :
  x + y ≤ 1 + x * y  := by
  /-
  Given \( x, y \in [0, 1] \) and the condition \( (1 - x)(1 - y) \ge 0 \), we need to show that \( x + y \le 1 + xy \).
  1. From the given condition \( (1 - x)(1 - y) \ge 0 \), we can derive the inequalities:
     - \( 1 - x \ge 0 \) implies \( x \le 1 \).
     - \( 1 - y \ge 0 \) implies \( y \le 1 \).
  2. Using these inequalities, we can further simplify the condition \( (1 - x)(1 - y) \ge 0 \).
  3. By expanding and simplifying the expression \( (1 - x)(1 - y) \), we get:
     \[
     (1 - x)(1 - y) = 1 - x - y + xy \ge 0
     \]
     which simplifies to:
     \[
     1 - x - y + xy \ge 0 \implies x + y \le 1 + xy
     \]
  Thus, we have shown that \( x + y \le 1 + xy \).
  -/
  -- Using the non-negativity of the product (1 - x) * (1 - y), we derive the inequality x + y ≤ 1 + x * y.
  nlinarith [mul_nonneg (sub_nonneg.2 h₁.2) (sub_nonneg.2 h₁.1)]
  -- The above line uses the fact that the product of non-negative numbers is non-negative to derive the inequality.
  -- Specifically, it uses the non-negativity of (1 - x) and (1 - y) to show that x + y ≤ 1 + x * y.
