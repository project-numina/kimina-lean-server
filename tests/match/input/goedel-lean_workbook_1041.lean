import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Show that $13$ is a factor of $2^{30}+3^{60}$ . -/
theorem lean_workbook_1041 : 13 ∣ 2^30 + 3^60  := by
  /-
  To show that 13 is a factor of \(2^{30} + 3^{60}\), we will use the property that if a number modulo 13 is zero, then 13 divides that number. We will compute the value of \(2^{30} + 3^{60}\) modulo 13 and show that it is zero.
  -/
  -- Use the property that if a number modulo 13 is zero, then 13 divides that number.
  apply Nat.dvd_of_mod_eq_zero
  -- Compute the value of 2^30 + 3^60 modulo 13 and show that it is zero.
  norm_num
  -- Apply reflexivity to confirm the result.
  <;> apply Eq.refl
