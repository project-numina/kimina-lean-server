import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove $(a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2)\ge (a^2b+b^2c+c^2a)(ab^2+bc^2+ca^2)$ -/
theorem lean_workbook_10352 (a b c : ℝ) : (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2)  := by
  /-
  To prove the inequality \((a^2 + b^2 + c^2)(a^2b^2 + b^2c^2 + c^2a^2) \geq (a^2b + b^2c + c^2a)(ab^2 + bc^2 + ca^2)\), we can use the non-linear arithmetic tactic `nlinarith` with the non-negativity of squares as a key property. Specifically, we will consider the non-negativity of various expressions involving \(a\), \(b\), and \(c\) to establish the inequality.
  -/
  -- Use the non-linear arithmetic tactic `nlinarith` with the non-negativity of squares as a key property.
  -- This tactic will consider the non-negativity of various expressions involving `a`, `b`, and `c` to establish the inequality.
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a * b + b * c), sq_nonneg (b * c + c * a), sq_nonneg (c * a + a * b),
    sq_nonneg (a * b * (a - b)), sq_nonneg (b * c * (b - c)), sq_nonneg (c * a * (c - a)),
    sq_nonneg (a * b * (b - a)), sq_nonneg (b * c * (c - b)), sq_nonneg (c * a * (a - c))]
