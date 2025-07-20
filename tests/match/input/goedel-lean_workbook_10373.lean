import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove $y^{n}-1\geqslant n(y-1)$ for $y>0$. -/
theorem lean_workbook_10373 (y : ℝ) (n : ℕ) (hy : y > 0) : y ^ n - 1 ≥ n * (y - 1)  := by
  /-
  We aim to prove that for any real number \( y > 0 \) and natural number \( n \), the inequality \( y^n - 1 \geq n(y - 1) \) holds. We will use mathematical induction on \( n \).
  **Base Case:**
  For \( n = 0 \), the left-hand side is \( y^0 - 1 = 1 - 1 = 0 \), and the right-hand side is \( 0 \cdot (y - 1) = 0 \). Thus, the inequality holds trivially.
  **Inductive Step:**
  Assume the inequality holds for some \( n \), i.e., \( y^n - 1 \geq n(y - 1) \). We need to show it holds for \( n + 1 \).
  Starting from the left-hand side for \( n + 1 \):
  \[ y^{n+1} - 1 = y \cdot y^n - 1 \]
  Using the inductive hypothesis \( y^n - 1 \geq n(y - 1) \), we have:
  \[ y \cdot y^n - 1 \geq y \cdot (n(y - 1) + 1) - 1 \]
  Simplifying the right-hand side:
  \[ y \cdot (n(y - 1) + 1) - 1 = y \cdot n(y - 1) + y - 1 = y^{n+1} - y \cdot n + y - 1 \]
  Since \( y > 0 \), we can use the fact that \( y - 1 \geq 0 \) (because \( y > 0 \)):
  \[ y^{n+1} - y \cdot n + y - 1 \geq (n + 1)(y - 1) \]
  Thus, we have shown that:
  \[ y^{n+1} - 1 \geq (n + 1)(y - 1) \]
  By induction, the inequality holds for all natural numbers \( n \).
  -/
  induction n with
  | zero =>
    -- Base case: when n = 0, the inequality holds trivially.
    simp
  | succ n hn =>
    -- Inductive step: assume the inequality holds for n, prove it for n + 1.
    simp only [Nat.cast_succ, pow_succ, mul_add, mul_one, Nat.cast_zero, add_zero, mul_comm] at hn ⊢
    -- Simplify the expressions using algebraic properties.
    nlinarith [sq_nonneg (y - 1)]
