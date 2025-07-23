import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- $M(M+2kc^2)(1-k^2) \leq (M+(k-k^2)c^2)^2,$ -/
theorem lean_workbook_10230 (M c k : ℝ) : M * (M + 2 * k * c ^ 2) * (1 - k ^ 2) ≤ (M + (k - k ^ 2) * c ^ 2) ^ 2  := by
  /-
  We need to show that for real numbers \( M \), \( c \), and \( k \), the inequality \( M(M + 2kc^2)(1 - k^2) \leq (M + (k - k^2)c^2)^2 \) holds. To prove this, we use the non-linear arithmetic (nlinarith) tactic, which simplifies the inequality by applying a series of algebraic manipulations and inequalities. Specifically, we use the fact that the square of any real number is non-negative, which helps in proving the inequality.
  -/
  -- Use non-linear arithmetic to simplify and prove the inequality.
  -- We provide lemmas about the non-negativity of squares to help the tactic.
  nlinarith [sq_nonneg (M + (k - k ^ 2) * c ^ 2), sq_nonneg (M - (k - k ^ 2) * c ^ 2),
    sq_nonneg (M * k - (k - k ^ 2) * c ^ 2), sq_nonneg (M * k + (k - k ^ 2) * c ^ 2)]
