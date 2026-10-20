module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! Ported to LeanLab from PrimeNumberTheoremAnd commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
   Apache License 2.0, original authors the PrimeNumberTheoremAnd project contributors.
   Changes: blueprint attributes and comments removed, import paths renamed, small fixes for
   Mathlib v4.35.0 listed in LeanLab/PNTPort/PLAN.md. This is reuse, not lab work. -/

@[expose] public section

open scoped Complex ComplexConjugate


theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

set_option backward.isDefEq.respectTransparency false in
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
