import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- $$2a^2+2b^2+c^2 \ge \frac{\sqrt{10}}{5}(a+3b)c$$ -/
theorem lean_workbook_10125 (a b c : ℝ) : 2 * a ^ 2 + 2 * b ^ 2 + c ^ 2 ≥ (Real.sqrt 10 / 5) * (a + 3 * b) * c  := by
  /-
  We need to show that for real numbers \(a\), \(b\), and \(c\), the inequality \(2a^2 + 2b^2 + c^2 \geq \frac{\sqrt{10}}{5}(a + 3b)c\) holds. To prove this, we will use the non-linear arithmetic (nlinarith) tactic, which can handle inequalities involving squares and square roots. Specifically, we will use the fact that the square of any real number is non-negative, and the non-negativity of the square root of a non-negative number.
  -/
  -- Use nlinarith to handle the inequality. We provide lemmas about the non-negativity of squares and the square root.
  nlinarith [
    -- The square of any real number is non-negative.
    sq_nonneg (a - Real.sqrt 10 / 5 * c), -- This ensures that the term involving a and c is non-negative.
    sq_nonneg (b - Real.sqrt 10 / 5 * c), -- Similarly, this ensures that the term involving b and c is non-negative.
    sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), -- This ensures that the square root of 10 is non-negative.
    sq_nonneg (a + 3 * b), -- This ensures that the term involving a and b is non-negative.
    sq_nonneg (a - 3 * b), -- This ensures that the term involving a and b is non-negative.
    sq_nonneg (c - a), -- This ensures that the term involving c and a is non-negative.
    sq_nonneg (c + a), -- This ensures that the term involving c and a is non-negative.
    sq_nonneg (c - b), -- This ensures that the term involving c and b is non-negative.
    sq_nonneg (c + b)  -- This ensures that the term involving c and b is non-negative.
  ]
