module

public import LeanLab.PNTPort.DirichletZF.SiegelPair
public import LeanLab.PNTPort.DirichletZF.RealZero

/-!
# Signs on the real segment below `1`

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input. Inputs for the
case of Siegel's theorem with no exceptional zero, Davenport chapter 21.

* `riemannZeta_real_neg`: for real `0 < σ < 1`, `ζ(σ)` is real and negative, from the ported
  StrongPNT formula `ζ(s) = 1 + 1/(s - 1) - s ∫₁^∞ {u} u^{-s-1} du`, Apache-2.0, the
  PrimeNumberTheoremAnd contributors;
* `LFunction_real_axis_im`: `L(σ, χ)` is real for real `σ` and real non-principal `χ`;
* `LFunction_nonneg_of_no_zero`: a real non-principal `L(s, χ)` with no zero on `[σ₀, 1)` is
  a nonnegative real at `σ₀`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter MeasureTheory
open scoped ComplexConjugate ComplexOrder

theorem riemannZeta_real_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).im = 0 ∧ (riemannZeta σ).re < 0 := by
  have hre : 0 < (σ : ℂ).re := by simpa using h0
  have hne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hconj : conj (riemannZeta σ) = riemannZeta σ := by
    rw [← riemannZeta_conj, Complex.conj_ofReal]
  have him : (riemannZeta σ).im = 0 := by
    have := congrArg Complex.im hconj
    rw [Complex.conj_im] at this; linarith
  refine ⟨him, ?_⟩
  rw [ZetaAltFormula hre hne, riemannZeta1]
  -- the integral is a nonnegative real
  have hint : (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-(σ : ℂ) - 1)) =
      ((∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-σ - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans zero_lt_one hu)
    rw [show (-(σ : ℂ) - 1) = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hu0]
    push_cast; ring
  have hnn : 0 ≤ ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-σ - 1) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu ↦
      mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hu)) _)
  rw [hint]
  set I := ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-σ - 1)
  have e : (1 + 1 / ((σ : ℂ) - 1) - (σ : ℂ) * (I : ℂ)) = ((1 + 1 / (σ - 1) - σ * I : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_re]
  have hσ1 : σ - 1 < 0 := by linarith
  have : 1 + 1 / (σ - 1) = σ / (σ - 1) := by
    have : σ - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [this]
  have : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg h0 hσ1
  nlinarith

lemma LFunction_real_axis_im {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (h2 : χ ^ 2 = 1) (σ : ℝ) : (DirichletCharacter.LFunction χ σ).im = 0 := by
  have := LFunction_conj hχ h2 (σ : ℂ)
  rw [Complex.conj_ofReal] at this
  have := congrArg Complex.im this
  rw [Complex.conj_im] at this; linarith

theorem LFunction_nonneg_of_no_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (h2 : χ ^ 2 = 1) {σ₀ : ℝ} (hσ₀ : σ₀ < 1)
    (hnz : ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) :
    0 ≤ DirichletCharacter.LFunction χ σ₀ := by
  set f : ℝ → ℝ := fun σ ↦ (DirichletCharacter.LFunction χ σ).re
  have hf : Continuous f :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hreal : ∀ σ : ℝ, DirichletCharacter.LFunction χ σ = (f σ : ℂ) := fun σ ↦ by
    apply Complex.ext <;> simp [f, LFunction_real_axis_im hχ h2 σ]
  have hnz' : ∀ σ : ℝ, σ₀ ≤ σ → f σ ≠ 0 := by
    intro σ hσ h
    have hz : DirichletCharacter.LFunction χ σ = 0 := by rw [hreal σ, h]; simp
    rcases lt_or_ge σ 1 with hl | hl
    · exact hnz σ hσ hl hz
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using hl) hz
  have h2pos : 0 ≤ f 2 := by
    have := LFunction_real_nonneg h2 (show (1 : ℝ) < 2 by norm_num)
    have : 0 ≤ (DirichletCharacter.LFunction χ (2 : ℝ)).re := (Complex.nonneg_iff.mp this).1
    simpa [f] using this
  have hf0 : 0 ≤ f σ₀ := by
    by_contra hneg
    push Not at hneg
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc (show σ₀ ≤ 2 by linarith) hf.continuousOn
      ⟨hneg.le, h2pos⟩
    exact hnz' c hc.1 hc0
  rw [hreal σ₀]
  exact Complex.zero_le_real.mpr hf0

end LeanLab.PNTPort.DirichletZF

