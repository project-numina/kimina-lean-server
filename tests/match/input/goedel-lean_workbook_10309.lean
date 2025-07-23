import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- it's $ 3a^{2}-12a\leq0 ,0\leq a\leq4 $ -/
theorem lean_workbook_10309 (a : ℝ) (h₁ : 3 * a ^ 2 - 12 * a ≤ 0) (h₂ : 0 ≤ a) (h₃ : a ≤ 4) : 0 ≤ a ∧ a ≤ 4  := by
  /-
  Given the inequalities \(3a^2 - 12a \leq 0\), \(0 \leq a\), and \(a \leq 4\), we need to show that \(0 \leq a \leq 4\).
  1. From \(3a^2 - 12a \leq 0\), we can factorize it as \(3a(a - 4) \leq 0\).
  2. Since \(0 \leq a\), we know that \(a\) is non-negative.
  3. Combining \(3a(a - 4) \leq 0\) with \(0 \leq a\), we deduce that \(a\) must be less than or equal to 4.
  Thus, combining these results, we conclude that \(0 \leq a \leq 4\).
  -/
  -- We need to show that 0 ≤ a and a ≤ 4.
  refine' ⟨h₂, _⟩
  -- We already know 0 ≤ a from h₂.
  -- Now, we need to show a ≤ 4.
  -- From h₁: 3a^2 - 12a ≤ 0, we can factorize it as 3a(a - 4) ≤ 0.
  -- Since 0 ≤ a, we know a is non-negative.
  -- Combining 3a(a - 4) ≤ 0 with 0 ≤ a, we deduce a ≤ 4.
  nlinarith
