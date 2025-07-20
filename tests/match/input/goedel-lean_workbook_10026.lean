import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $ab \leq \frac{1}{4}$ given $a + b = 1$ and $a, b \geq 0$. -/
theorem lean_workbook_10026 (a b : ℝ) (h1 : a + b = 1) (h2 : a >= 0 ∧ b >= 0) : a * b <= 1 / 4  := by
  /-
  Given \( a + b = 1 \) and \( a, b \geq 0 \), we need to prove that \( ab \leq \frac{1}{4} \).
  1. Consider the expression \( (a - b)^2 \). Since the square of any real number is non-negative, \( (a - b)^2 \geq 0 \).
  2. Expanding \( (a - b)^2 \) gives \( a^2 - 2ab + b^2 \geq 0 \).
  3. Using the given condition \( a + b = 1 \), we can substitute \( b = 1 - a \).
  4. Substituting \( b = 1 - a \) into the inequality \( a^2 - 2ab + b^2 \geq 0 \) results in \( a^2 - 2a(1 - a) + (1 - a)^2 \geq 0 \).
  5. Simplifying the expression, we get \( a^2 - 2a + 2a^2 + 1 - 2a + a^2 = 4a^2 - 4a + 1 \geq 0 \).
  6. This can be rewritten as \( (2a - 1)^2 \geq 0 \), which is always true since the square of any real number is non-negative.
  7. From \( (2a - 1)^2 \geq 0 \), we derive \( 4a(1 - a) \leq 1 \), which simplifies to \( ab \leq \frac{1}{4} \).
  -/
  -- Use non-linear arithmetic to prove the inequality.
  -- Consider the expression (a - b)^2, which is non-negative.
  -- Expanding (a - b)^2 gives a^2 - 2ab + b^2 ≥ 0.
  -- Using a + b = 1, substitute b = 1 - a.
  -- Substituting b = 1 - a into the inequality results in a^2 - 2a(1 - a) + (1 - a)^2 ≥ 0.
  -- Simplifying, we get 4a^2 - 4a + 1 ≥ 0, which is always true.
  -- From 4a^2 - 4a + 1 ≥ 0, we derive 4a(1 - a) ≤ 1, which simplifies to ab ≤ 1/4.
  nlinarith [sq_nonneg (a - b)]
  -- Additional linear arithmetic simplifications to ensure the inequality holds.
  <;> simp_all only [add_left_inj, add_right_inj, mul_one, mul_zero, mul_neg, mul_comm]
  <;> nlinarith [sq_nonneg (a - b)]
