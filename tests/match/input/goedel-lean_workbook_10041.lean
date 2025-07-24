import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Prove that $ \sum \frac{a}{b+c}=\sum(\frac{a}{b+c}+1)-3=\sum\frac{a+b+c}{b+c} -3$ -/
theorem lean_workbook_10041 (a b c: ℝ) : a / (b + c) + b / (a + c) + c / (a + b) = (a / (b + c) + 1 + b / (a + c) + 1 + c / (a + b) + 1) - 3  := by
  /-
  To prove the given equation, we start by simplifying the left-hand side and the right-hand side separately. We use algebraic manipulations to show that both sides are equivalent.
  1. **Simplify the left-hand side:**
     \[
     \frac{a}{b+c} + \frac{b}{a+c} + \frac{c}{a+b}
     \]
  2. **Simplify the right-hand side:**
     \[
     \left( \frac{a}{b+c} + 1 \right) + \left( \frac{b}{a+c} + 1 \right) + \left( \frac{c}{a+b} + 1 \right) - 3
     \]
     Expanding and combining like terms:
     \[
     \frac{a}{b+c} + \frac{b}{a+c} + \frac{c}{a+b} + 3 - 3 = \frac{a}{b+c} + \frac{b}{a+c} + \frac{c}{a+b}
     \]
  3. **Equivalence:**
     Since both sides simplify to the same expression, we have shown that the left-hand side equals the right-hand side.
  -/
  -- Simplify the left-hand side and the right-hand side using algebraic manipulations.
  ring_nf
  -- Use the `linarith` tactic to verify that the simplified expressions are equal.
  <;> linarith
