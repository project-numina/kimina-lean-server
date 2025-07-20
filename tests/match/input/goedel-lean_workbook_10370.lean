import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Note that $f(x)=\sum_{k=1}^nkx^k=x\frac{nx^{n+1}-(n+1)x^n+1}{(x-1)^2}$ $\forall x\ne 1$ -/
theorem lean_workbook_10370 {n : ℕ} (hn : 0 < n) (x : ℝ) (hx : x ≠ 1) : ∑ k in Finset.Icc 1 n, (k * x ^ k) = x * (n * x ^ (n + 1) - (n + 1) * x ^ n + 1) / (x - 1) ^ 2  := by
  /-
  We need to show that for a given natural number \( n \) greater than 0 and a real number \( x \) not equal to 1, the sum of \( k \cdot x^k \) from \( k = 1 \) to \( n \) equals \( x \cdot \frac{n \cdot x^{n+1} - (n+1) \cdot x^n + 1}{(x-1)^2} \).
  1. **Base Case (n = 1):**
     - The sum for \( n = 1 \) is \( 1 \cdot x^1 = x \).
     - The right-hand side simplifies to \( x \cdot \frac{1 \cdot x^2 - 2 \cdot x + 1}{(x-1)^2} = x \cdot \frac{x^2 - 2x + 1}{(x-1)^2} \).
     - Since \( x \neq 1 \), the denominator \( (x-1)^2 \) is non-zero, and the expression simplifies correctly.
  2. **Inductive Step:**
     - Assume the statement holds for \( n \), i.e., \( \sum_{k=1}^n k \cdot x^k = x \cdot \frac{n \cdot x^{n+1} - (n+1) \cdot x^n + 1}{(x-1)^2} \).
     - For \( n+1 \), the sum becomes:
       \[
       \sum_{k=1}^{n+1} k \cdot x^k = \sum_{k=1}^n k \cdot x^k + (n+1) \cdot x^{n+1}
       \]
     - Using the inductive hypothesis:
       \[
       \sum_{k=1}^{n+1} k \cdot x^k = x \cdot \frac{n \cdot x^{n+1} - (n+1) \cdot x^n + 1}{(x-1)^2} + (n+1) \cdot x^{n+1}
       \]
     - Simplify the expression using algebraic manipulations to match the form for \( n+1 \).
  -/
  induction n with
  | zero =>
    -- This case is impossible because hn : 0 < n
    contradiction
  | succ n ih =>
    -- Base case: n = 1
    cases n with
    | zero =>
      -- When n = 1, the sum is 1 * x^1 = x
      simp [Finset.sum_Icc_succ_top, mul_add, mul_comm, mul_left_comm]
      -- Simplify the right-hand side to match the left-hand side
      field_simp [sub_ne_zero.mpr hx]
      ring
    | succ n =>
      -- Inductive step: assume the statement holds for n, prove for n+1
      simp_all [Finset.sum_Icc_succ_top, mul_add, mul_comm, mul_left_comm]
      -- Simplify the expression using algebraic manipulations
      field_simp [sub_ne_zero.mpr hx]
      ring
