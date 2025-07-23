import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $2^{21} \equiv 1 \pmod 7$ without a calculator. -/
theorem lean_workbook_10202 : 2^21 ≡ 1 [ZMOD 7]  := by
  /-
  To prove that \(2^{21} \equiv 1 \pmod{7}\), we can use properties of modular arithmetic and exponentiation. Specifically, we will show that \(2^{21} \mod 7 = 1\).
  1. First, observe that \(2^3 = 8 \equiv 1 \pmod{7}\).
  2. This implies that \(2^3 \equiv 1 \pmod{7}\).
  3. Using this result, we can express \(2^{21}\) as \((2^3)^7\).
  4. Since \(2^3 \equiv 1 \pmod{7}\), we have \((2^3)^7 \equiv 1^7 \pmod{7}\).
  5. Simplifying, we get \(1^7 = 1\), thus \(2^{21} \equiv 1 \pmod{7}\).
  -/
  -- Use norm_num to simplify the expression involving powers and modular arithmetic.
  norm_num [Int.ModEq, pow_succ, Int.mul_emod]
  -- Each `rfl` confirms the equivalence step-by-step, ensuring the final result is correct.
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
