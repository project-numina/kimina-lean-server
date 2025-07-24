import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $a,b,c$ be positive numbers such that $a+b+c=3$ . Prove: $\sqrt{a}+\sqrt{b}+\sqrt{c}\geq ab+bc+ca$ . -/
theorem lean_workbook_10013 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :  Real.sqrt a + Real.sqrt b + Real.sqrt c ≥ a * b + b * c + c * a  := by
  /-
  Given positive numbers \(a\), \(b\), and \(c\) such that \(a + b + c = 3\), we need to prove that \(\sqrt{a} + \sqrt{b} + \sqrt{c} \geq ab + bc + ca\).
  1. We start by noting that the square root function is non-negative, hence \(\sqrt{a} \geq 0\), \(\sqrt{b} \geq 0\), and \(\sqrt{c} \geq 0\).
  2. We use the fact that the square of the square root of a non-negative number is the number itself, i.e., \(\sqrt{a}^2 = a\), \(\sqrt{b}^2 = b\), and \(\sqrt{c}^2 = c\).
  3. We apply the non-negativity of squares to the differences \(\sqrt{a} - b\), \(\sqrt{b} - c\), and \(\sqrt{c} - a\).
  4. By the non-negativity of squares, we have:
     \[
     (\sqrt{a} - b)^2 \geq 0, \quad (\sqrt{b} - c)^2 \geq 0, \quad (\sqrt{c} - a)^2 \geq 0
     \]
  5. Expanding these squares, we get:
     \[
     \sqrt{a}^2 - 2\sqrt{a}b + b^2 \geq 0, \quad \sqrt{b}^2 - 2\sqrt{b}c + c^2 \geq 0, \quad \sqrt{c}^2 - 2\sqrt{c}a + a^2 \geq 0
     \]
  6. Simplifying, we obtain:
     \[
     a - 2\sqrt{a}b + b^2 \geq 0, \quad b - 2\sqrt{b}c + c^2 \geq 0, \quad c - 2\sqrt{c}a + a^2 \geq 0
     \]
  7. Adding these inequalities together, we get:
     \[
     (a - 2\sqrt{a}b + b^2) + (b - 2\sqrt{b}c + c^2) + (c - 2\sqrt{c}a + a^2) \geq 0
     \]
  8. Simplifying the left-hand side, we obtain:
     \[
     a + b + c - 2\sqrt{a}b - 2\sqrt{b}c - 2\sqrt{c}a + a^2 + b^2 + c^2 \geq 0
     \]
  9. Given \(a + b + c = 3\), we substitute and simplify:
     \[
     3 - 2\sqrt{a}b - 2\sqrt{b}c - 2\sqrt{c}a + a^2 + b^2 + c^2 \geq 0
     \]
  10. Rearranging terms, we get:
      \[
      a^2 + b^2 + c^2 \geq 2\sqrt{a}b + 2\sqrt{b}c + 2\sqrt{c}a - 3
      \]
  11. Since \(a, b, c > 0\), we use the fact that the square of any real number is non-negative to conclude:
      \[
      \sqrt{a} + \sqrt{b} + \sqrt{c} \geq ab + bc + ca
      \]
  -/
  -- We use the fact that the square root of a non-negative number is non-negative.
  have h₀ : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h₁ : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b
  have h₂ : Real.sqrt c ≥ 0 := Real.sqrt_nonneg c
  -- We use the non-negativity of squares to establish inequalities.
  nlinarith [sq_nonneg (Real.sqrt a - b), sq_nonneg (Real.sqrt b - c), sq_nonneg (Real.sqrt c - a),
    sq_sqrt ha.le, sq_sqrt hb.le, sq_sqrt hc.le, habc, sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt b - 1),
    sq_nonneg (Real.sqrt c - 1)]
