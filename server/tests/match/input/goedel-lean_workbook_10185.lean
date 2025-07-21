import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that for every positive integer n the inequality is hold: $1+\dfrac{1}{4}+\dfrac{1}{9} +\cdots+\dfrac{1}{n^2}\le \dfrac{5}{3}-\dfrac{2}{2n+1}$ -/
theorem lean_workbook_10185 (n:ℕ) : (∑ k in Finset.range n, (1/(k + 1)^2)) ≤ (5/3) - (2/(2 * n + 1))  := by
  /-
  We aim to prove that for every positive integer \( n \), the inequality \( 1 + \frac{1}{4} + \frac{1}{9} + \cdots + \frac{1}{n^2} \leq \frac{5}{3} - \frac{2}{2n+1} \) holds.
  -/
  induction n with
  | zero =>
    -- Base case: When n = 0, the left-hand side is 0 and the right-hand side is 5/3.
    norm_num
  | succ n ih =>
    -- Inductive step: Assume the inequality holds for n, prove it for n + 1.
    cases n with
    | zero =>
      -- Base case for the inductive step: When n = 0, the left-hand side is 1 and the right-hand side is 5/3 - 2/3 = 1.
      norm_num
    | succ n =>
      -- Use the inductive hypothesis and simplify the expressions.
      simp_all [Finset.sum_range_succ, Nat.div_eq_of_lt, Nat.succ_le_iff, Nat.lt_succ_iff]
      -- Normalize the numerical expressions.
      <;> norm_num
      -- Use linear arithmetic to conclude the proof.
      <;> linarith
