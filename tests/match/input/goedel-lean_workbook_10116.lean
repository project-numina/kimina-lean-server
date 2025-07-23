import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- If $f(x)$ is injective, show that $f(x+yf(x))=f(x)f(y)$ and $f(y+xf(y))=f(x)f(y)$, which implies $x+yf(x)=y+xf(y)$. -/
theorem lean_workbook_10116 (f : ℝ → ℝ) (hf: Function.Injective f) : ∀ x y : ℝ, f (x + y * f x) = f x * f y ∧ f (y + x * f y) = f x * f y → x + y * f x = y + x * f y  := by
  /-
  Given an injective function \( f : \mathbb{R} \to \mathbb{R} \), we need to show that for any real numbers \( x \) and \( y \), if \( f(x + yf(x)) = f(x)f(y) \) and \( f(y + xf(y)) = f(x)f(y) \), then \( x + yf(x) = y + xf(y) \).
  1. Assume \( x \) and \( y \) are real numbers such that \( f(x + yf(x)) = f(x)f(y) \) and \( f(y + xf(y)) = f(x)f(y) \).
  2. Since \( f \) is injective, we can use the given equations to deduce that \( x + yf(x) = y + xf(y) \).
  3. The proof involves leveraging the injectivity of \( f \) to show that the expressions \( x + yf(x) \) and \( y + xf(y) \) must be equal.
  -/
  intro x y
  intro h
  have h1 := h.1
  have h2 := h.2
  -- Since f is injective, we can use the given equations to deduce that x + yf(x) = y + xf(y).
  apply Eq.symm
  apply Eq.symm
  apply hf
  -- Using the injectivity of f, we can deduce the equality.
  linarith
