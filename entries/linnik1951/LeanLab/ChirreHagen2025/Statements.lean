module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0075, A. Chirre and M. V. Hagen, On Goldbach numbers in short intervals, arXiv 2512.23534v1,
HTML read 2026-10-16. Definitions; the cited, unproved statements were removed from this copy.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The paper's Goldbach number: a positive integer that is the sum of two odd primes. -/
def IsGoldbachNumber (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = n

/-- Equation 1.1, `J_θ(x, δ) = ∫_1^x (θ((1+δ)y) - θ(y) - δy)^2 dy`. -/
noncomputable def Jtheta (x δ : ℝ) : ℝ :=
  ∫ y in (1 : ℝ)..x, (θ ((1 + δ) * y) - θ y - δ * y) ^ 2

/-- Equation 1.2, `J_ψ(x, δ)`. -/
noncomputable def Jpsi (x δ : ℝ) : ℝ :=
  ∫ y in (1 : ℝ)..x, (ψ ((1 + δ) * y) - ψ y - δ * y) ^ 2

/-- The same integrand over `[a x, x]`, as Section 5 uses it. -/
noncomputable def JthetaFrom (a x δ : ℝ) : ℝ :=
  ∫ y in a * x..x, (θ ((1 + δ) * y) - θ y - δ * y) ^ 2

/-- The first display of Section 5: for `a ∈ [10^-13, 1)`, Theorem 3 bounds the integral over
`[a x, x]`. Cited; it follows from Theorem 3 because the integrand is nonnegative and
`1 ≤ a x`, which the lab has not yet proved for want of integrability lemmas. -/
def Section5Upper : Prop :=
  ∀ a x δ : ℝ, (1 / 10 ^ 13 : ℝ) ≤ a → a < 1 → 10 ^ 13 ≤ x → 0 < δ → δ ≤ (1 / 10 ^ 13 : ℝ) →
    JthetaFrom a x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2

/-- Section 5, following Cully-Hugill and Dudek Section 4 verbatim, for `a ∈ [10^-13, 1)`,
`x ≥ 10^13`, `δ ∈ (0, 10^-13]`, and, a lab addition so that every prime used is odd,
`a x ≥ 2`: if no Goldbach number lies in `(x, x + h]` with `1 ≤ h ≤ x`,
and `δ ≤ h / (2x)`, the integral over `[a x, x]` is at least `δ² x³ / 3 · (1/8 - a³)`.
The paper states it strictly; the lab uses the weaker `≤`. Cited. Whether the cited argument
uses RH is a QUESTION until Cully-Hugill and Dudek Section 4 is read. -/
def NoGoldbachLower : Prop :=
  ∀ a x h δ : ℝ, 1 / 10 ^ 13 ≤ a → a < 1 → 2 ≤ a * x → 10 ^ 13 ≤ x → 1 ≤ h → h ≤ x → 0 < δ →
    δ ≤ 1 / 10 ^ 13 → δ ≤ h / (2 * x) →
    (¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) →
    δ ^ 2 * x ^ 3 / 3 * (1 / 8 - a ^ 3) ≤ JthetaFrom a x δ

end LeanLab.ChirreHagen2025
