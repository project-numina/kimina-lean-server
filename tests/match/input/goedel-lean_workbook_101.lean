import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- solution $2^9+1=512+1=\boxed{513}$ -/
theorem lean_workbook_101 (x : ℕ) (hx : x = 2^9 + 1) : x = 513  := by
  /-
  We need to show that \( x = 513 \) given \( x = 2^9 + 1 \). First, we substitute \( 2^9 + 1 \) for \( x \). Then, we compute \( 2^9 \) to be 512. Adding 1 to 512 gives us 513. Thus, \( x = 513 \).
  -/
  -- Substitute the given expression for x.
  rw [hx]
  -- Compute the value of 2^9 to be 512.
  norm_num
  -- Add 1 to 512 to get 513.
  <;> rfl
