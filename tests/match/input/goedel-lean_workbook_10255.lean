import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/- Let $P(x,y)$ , the assertion $f((x-y)^{2})=x^{2}-2yf(x)+(f(x))^{2}$ Setting $g(x)=f(x)-x$ , the assertion becomes : $g((x-y)^{2})=(g(y))^{2}+2y(g(y)-g(x))$ Hence : $P(x,x)$ : $(g(x))^{2}=g(0) \forall x \in \mathbb{R}$ , which means that the fonction $g$ is constant i.e : there exists a real $a$ such that $g(x)=a$ , which means that the function $f$ is in the form : $f(x)=x+a$ . A check forward give us $a=0$ or $a=1$ And surely the fonctions $f(x)=x$ and $f(x)=x+1$ satisfy the FE. -/
theorem lean_workbook_10255  (f : ℝ → ℝ)
  (h₀ : ∀ x, ∀ y, f ((x - y)^2) = x^2 - 2 * y * f x + (f x)^2) :
  ∀ x, f x = x ∨ ∀ x, f x = x + 1  := by
  /-
  Given the function \( f : \mathbb{R} \to \mathbb{R} \) and the property \( \forall x, \forall y, f((x - y)^2) = x^2 - 2y f(x) + (f(x))^2 \), we introduce a new function \( g(x) = f(x) - x \). The given property then transforms into:
  \[ g((x - y)^2) = (g(y))^2 + 2y(g(y) - g(x)) \]
  From this, we derive:
  \[ P(x, x) : (g(x))^2 = g(0) \]
  This implies that \( g \) is a constant function. Therefore, there exists a real number \( a \) such that \( g(x) = a \) for all \( x \in \mathbb{R} \). Consequently, \( f(x) = x + a \) for some constant \( a \). We then check that \( a = 0 \) or \( a = 1 \).
  -/
  intro x
  have h₁ := h₀ 0 0
  have h₂ := h₀ x 0
  have h₃ := h₀ x x
  have h₄ := h₀ 1 1
  simp at h₁ h₂ h₃ h₄
  have h₅ := h₀ 1 0
  have h₆ := h₀ 0 1
  simp at h₅ h₆
  nlinarith
