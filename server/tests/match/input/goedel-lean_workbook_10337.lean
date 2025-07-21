import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $a,b$ are both odd then $a^2+b^2+c^2 \equiv 2,3 \pmod {4}$ -/
theorem lean_workbook_10337 {a b c : ℤ} (ha : Odd a) (hb : Odd b) : (a^2 + b^2 + c^2) % 4 = 2 ∨ (a^2 + b^2 + c^2) % 4 = 3  := by
  /-
  Given that \(a\) and \(b\) are both odd integers, we need to show that \(a^2 + b^2 + c^2\) modulo 4 is either 2 or 3. 
  1. Since \(a\) is odd, \(a\) modulo 4 can be either 1 or 3. This is because any odd integer can be written in the form \(2k + 1\) or \(2k + 3\), and modulo 4, these expressions simplify to 1 and 3 respectively.
  2. Similarly, since \(b\) is odd, \(b\) modulo 4 can also be either 1 or 3.
  3. For any integer \(c\), \(c\) modulo 4 can be 0, 1, 2, or 3.
  4. We consider all combinations of these residues and compute \(a^2 + b^2 + c^2\) modulo 4. We find that in all cases, the result is either 2 or 3.
  -/
  -- Since a is odd, a modulo 4 can be either 1 or 3.
  have h₀ : a % 4 = 1 ∨ a % 4 = 3 := by
    cases' ha with k hk
    omega
  -- Since b is odd, b modulo 4 can be either 1 or 3.
  have h₁ : b % 4 = 1 ∨ b % 4 = 3 := by
    cases' hb with k hk
    omega
  -- For any integer c, c modulo 4 can be 0, 1, 2, or 3.
  have h₂ : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by
    omega
  -- Consider all combinations of these residues and compute a^2 + b^2 + c^2 modulo 4.
  rcases h₀ with (h₀ | h₀) <;> rcases h₁ with (h₁ | h₁) <;> rcases h₂ with (h₂ | h₂ | h₂ | h₂) <;>
    simp [h₀, h₁, h₂, pow_two, Int.add_emod, Int.mul_emod, Int.emod_emod]
  <;> omega
