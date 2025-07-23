import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Find the sequence $\{x_1, x_2, x_3, \ldots\}$ where $x_1=r$ and $x_k=2^{k-1} \cdot x_1$ for some real number $r$ -/
theorem lean_workbook_1021 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1  := by
  /-
  We need to find a sequence \(\{x_1, x_2, x_3, \ldots\}\) where \(x_1 = r\) and \(x_k = 2^{k-1} \cdot x_1\) for some real number \(r\). To define such a sequence, we can use a function \(f : \mathbb{N} \to \mathbb{R}\) where \(f(k) = 2^{k-1} \cdot r\). This function clearly satisfies the given conditions:
  1. \(f(1) = r\)
  2. For all \(k\), \(f(k) = 2^{k-1} \cdot r\)
  -/
  -- We define the function f(k) = 2^(k-1) * r
  use fun k => (2 : ℝ)^(k-1) * r
  -- We need to prove two conditions: f(1) = r and f(k) = 2^(k-1) * f(1) for all k
  constructor
  -- First, we prove f(1) = r
  -- By definition, f(1) = 2^(1-1) * r = 2^0 * r = 1 * r = r
  simp
  -- Second, we prove f(k) = 2^(k-1) * f(1) for all k
  -- By definition, f(k) = 2^(k-1) * r
  intro k
  simp [mul_comm]
