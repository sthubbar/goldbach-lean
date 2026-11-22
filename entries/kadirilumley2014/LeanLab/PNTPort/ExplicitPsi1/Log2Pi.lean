module

public import LeanLab.PNTPort.ExplicitPsi1.Nontrivial

/-!
# The constant term is `log 2π`

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input: `ζ'(0)/ζ(0) = log 2π` from Mathlib's `deriv_riemannZeta_zero` and
`riemannZeta_zero`, so the explicit formula reads, for every `x > 0`,
`|Σ Λ(n) max(0, 1 - n/x) - x/2 + log 2π + Σ_ρ m(ρ) x^ρ/(ρ(ρ + 1))| ≤ K x^{-1/2}`,
the sum over the nontrivial zeros.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex
open scoped Real

theorem logDeriv_zeta_zero : deriv riemannZeta 0 / riemannZeta 0 = Real.log (2 * π) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  rw [show (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity)]
  field_simp

/-- **The explicit formula for `ψ₁(x)/x`** with the constant `log 2π`, over the zeros in the
open critical strip. -/
theorem explicit_formula_psi1_log2pi : ∃ K : ℝ, ∀ x : ℝ, 0 < x →
    ‖∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / x) -
      (x / 2 - Real.log (2 * π) -
        ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}, zterm x ρ.1)‖ ≤
      K * x ^ (-1 / 2 : ℝ) := by
  obtain ⟨K, hK⟩ := explicit_formula_psi1_bound
  refine ⟨K, fun x hx => ?_⟩
  have e : (∑' ρ : Zall, zterm x ρ) =
      ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}, zterm x ρ.1 := by
    rw [Zall_eq]; rfl
  have := hK x hx
  rwa [e, logDeriv_zeta_zero] at this

end LeanLab.PNTPort.ExplicitPsi1

