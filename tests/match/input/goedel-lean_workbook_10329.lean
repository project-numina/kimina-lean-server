import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-  $$2 | \binom{n}{2} \implies 4 | n(n-1) \implies n \equiv 0, 1 \mod 4.$$ -/
theorem lean_workbook_10329 : ∀ n : ℕ, 2 ∣ n.choose 2 → 4 ∣ n * (n - 1) → n ≡ 0 [ZMOD 4] ∨ n ≡ 1 [ZMOD 4]  := by
  /-
  For any natural number \( n \), if \( 2 \) divides \( \binom{n}{2} \) and \( 4 \) divides \( n(n-1) \), then \( n \equiv 0 \mod 4 \) or \( n \equiv 1 \mod 4 \).
  1. **Assumption and Setup**:
     - \( 2 \) divides \( \binom{n}{2} \) implies \( n \equiv 0 \mod 2 \) or \( n \equiv 1 \mod 2 \).
     - \( 4 \) divides \( n(n-1) \) implies \( n \equiv 0 \mod 4 \) or \( n \equiv 1 \mod 4 \).
  2. **Case Analysis**:
     - If \( n \equiv 0 \mod 2 \), then \( n = 2k \) for some integer \( k \).
     - If \( n \equiv 1 \mod 2 \), then \( n = 2k + 1 \) for some integer \( k \).
     - Similarly, for \( 4 \), we consider \( n \equiv 0 \mod 4 \) or \( n \equiv 1 \mod 4 \).
  3. **Verification**:
     - Check the conditions under which \( n \equiv 0 \mod 4 \) and \( n \equiv 1 \mod 4 \).
  4. **Conclusion**:
     - By analyzing the conditions, we conclude that \( n \equiv 0 \mod 4 \) or \( n \equiv 1 \mod 4 \).
  -/
  intro n h₀ h₁
  -- Normalize the expressions involving divisibility and modular arithmetic.
  norm_num [Nat.choose_two_right, Nat.dvd_iff_mod_eq_zero, Int.ModEq] at h₀ h₁ ⊢
  -- Perform case analysis on the possible values of n modulo 4.
  have h₂ : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h₂ with (h₂ | h₂ | h₂ | h₂) <;> simp [h₂, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₀ h₁ ⊢
  -- Use omega to solve the resulting equations and conclude the proof.
  <;> omega
