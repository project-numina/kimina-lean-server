import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $3^n \ge 2n + 1$ for $n \in \mathbb{Z^+}$ -/
theorem lean_workbook_10314 (n : ℕ) : 3^n ≥ 2*n + 1  := by
  /-
  We aim to prove that for any positive integer \( n \), \( 3^n \geq 2n + 1 \). We will use mathematical induction to establish this result.
  1. **Base Case**: When \( n = 1 \), we need to show that \( 3^1 \geq 2 \cdot 1 + 1 \). This simplifies to \( 3 \geq 3 \), which is true.
  2. **Inductive Step**: Assume that the statement holds for some positive integer \( n \), i.e., \( 3^n \geq 2n + 1 \). We need to show that the statement holds for \( n + 1 \), i.e., \( 3^{n+1} \geq 2(n + 1) + 1 \).
     Starting from \( 3^{n+1} = 3 \cdot 3^n \), we can use the inductive hypothesis \( 3^n \geq 2n + 1 \) to get:
     \[
     3^{n+1} = 3 \cdot 3^n \geq 3 \cdot (2n + 1) = 6n + 3
     \]
     We need to show that \( 6n + 3 \geq 2(n + 1) + 1 = 2n + 3 \). This inequality simplifies to \( 6n + 3 \geq 2n + 3 \), which is equivalent to \( 4n \geq 0 \). Since \( n \) is a positive integer, \( 4n \geq 0 \) is always true.
  Thus, by mathematical induction, we have shown that \( 3^n \geq 2n + 1 \) for all positive integers \( n \).
  -/
  induction n with
  | zero =>
    -- Base case: when n = 0, we need to show 3^0 ≥ 2*0 + 1
    -- This simplifies to 1 ≥ 1, which is true.
    simp
  | succ n hn =>
    -- Inductive step: assume the statement holds for n, i.e., 3^n ≥ 2n + 1
    -- We need to show it holds for n + 1, i.e., 3^(n+1) ≥ 2(n + 1) + 1
    simp_all [Nat.pow_succ, Nat.mul_succ]
    -- Simplify the expression to 3^(n+1) = 3 * 3^n ≥ 3 * (2n + 1) = 6n + 3
    -- We need to show 6n + 3 ≥ 2n + 3, which simplifies to 4n ≥ 0, always true for positive n
    nlinarith
