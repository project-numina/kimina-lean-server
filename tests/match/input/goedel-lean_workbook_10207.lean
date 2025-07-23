import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Using congruence properties, prove that $2^{mn}-1$ is divisible by $2^{m}-1$ for all integers $m, n\ge 1$ . -/
theorem lean_workbook_10207 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : (2 ^ m - 1) ∣ (2 ^ (m * n) - 1)  := by
  /-
  We need to prove that for any integers \( m \) and \( n \) both greater than or equal to 1, \( 2^{mn} - 1 \) is divisible by \( 2^m - 1 \). This can be shown using the property of exponents and the fact that \( 2^m - 1 \) divides \( 2^{mn} - 1 \).
  -/
  -- Use the property that \( 2^m - 1 \) divides \( 2^{mn} - 1 \) for natural numbers \( m \) and \( n \).
  simpa only [one_pow, pow_mul] using nat_sub_dvd_pow_sub_pow _ 1 n
