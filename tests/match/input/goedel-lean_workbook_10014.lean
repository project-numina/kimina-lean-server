import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $b \ge 1$ then $a \le 2b$ which implies $(a-b)(a-2b) \le 0$ -/
theorem lean_workbook_10014 : 1 ≤ b → a ≤ 2 * b → (a - b) * (a - 2 * b) ≤ 0  := by
  /-
  Given \( b \ge 1 \), we need to show that \( a \le 2b \) implies \( (a - b)(a - 2b) \le 0 \). This can be derived by analyzing the signs of the factors \( a - b \) and \( a - 2b \). Since \( b \ge 1 \), we have \( a \le 2b \). Therefore, \( a - b \le b \le 2b \) and \( a - 2b \le 0 \). The product of a non-positive number and a non-positive number is non-positive.
  -/
  -- Introduce the assumptions \( b \ge 1 \) and \( a \le 2b \)
  intro h₀ h₁
  -- Consider the cases where \( a \le 2b \) and \( b \ge 1 \)
  cases' le_total a (2 * b) with h₂ h₂ <;>
  cases' le_total b 1 with h₃ h₃ <;>
  -- Simplify the expressions using the assumptions and properties of multiplication
  simp_all [mul_comm, mul_left_comm, mul_assoc]
  <;>
  -- Use linear arithmetic to conclude the proof
  nlinarith
