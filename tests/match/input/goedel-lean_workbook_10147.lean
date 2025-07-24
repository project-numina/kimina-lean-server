import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that for any positive integer n, there exist a Fibonacci Number $F_m$ such that $n \; | \; F_m$ and $m \le n^2-1$ -/
theorem lean_workbook_10147 (n : ℕ) : ∃ m ≤ n^2-1, n ∣ fib m  := by
  /-
  For any positive integer \( n \), we need to show that there exists a Fibonacci number \( F_m \) such that \( n \) divides \( F_m \) and \( m \leq n^2 - 1 \). We will use the fact that the Fibonacci sequence modulo any positive integer \( n \) is periodic with a period that can be expressed in terms of \( n \). Specifically, we will show that \( m = 0 \) satisfies the conditions, as \( F_0 = 0 \) and \( 0 \leq n^2 - 1 \).
  -/
  -- We claim that m = 0 satisfies the conditions.
  use 0
  -- We need to show that 0 ≤ n^2 - 1 and n ∣ fib 0.
  constructor
  -- Since n^2 is a positive integer, n^2 - 1 is non-negative.
  exact by omega
  -- We know that fib 0 = 0, and any number divides 0.
  simp
