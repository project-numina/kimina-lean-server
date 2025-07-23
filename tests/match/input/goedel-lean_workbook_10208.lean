import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $2S=k(k+1)$ where $S=k+(k-1)+\cdots+1$. -/
theorem lean_workbook_10208 (k : ℕ) : 2 * (k * (k + 1) / 2) = k * (k + 1)  := by
  /-
  To prove that \(2S = k(k+1)\) where \(S = k + (k-1) + \cdots + 1\), we start by expressing \(S\) as a sum of the first \(k\) natural numbers. The sum of the first \(k\) natural numbers is given by the formula \(\frac{k(k+1)}{2}\). We then multiply this sum by 2 to get \(2S\). Simplifying the expression, we find that \(2S = k(k+1)\).
  -/
  -- Use induction on k to prove the statement for all natural numbers.
  induction k with
  | zero =>
    -- Base case: when k = 0, the statement is trivially true.
    simp
  | succ k ih =>
    -- Inductive step: assume the statement holds for k, prove it for k+1.
    -- Simplify the expression using the induction hypothesis and algebraic manipulation.
    simp_all [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_comm,
      Nat.mul_left_comm]
    -- Use the omega tactic to solve the resulting linear arithmetic problem.
    omega
