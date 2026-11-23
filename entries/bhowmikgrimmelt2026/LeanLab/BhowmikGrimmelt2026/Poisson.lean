module

public import LeanLab.BhowmikGrimmelt2026.Eq74
public import Mathlib.Analysis.Fourier.PoissonSummation

/-!
Poisson summation for the weight in Lemma 7.2, page 26.
Mathlib v4.35 calls its Poisson theorem Real.tsum_eq_tsum_fourier.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

/-- Compact support survives the dilation used in Definition 7.1. -/
theorem GT_hasCompactSupport {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (GT G T) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-2 * T) (2 * T))
    isCompact_Icc
  intro x hx
  have h : |x| ≤ 2 * T := by
    by_contra hn
    exact hx (GT_eq_zero hsupp hT (lt_of_not_ge hn))
  exact ⟨by linarith [(abs_le.mp h).1], (abs_le.mp h).2⟩

/-- Smoothness survives dilation, including the totalized value T zero. -/
theorem GT_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (T : ℝ) :
    ContDiff ℝ ∞ (GT G T) := by
  unfold GT
  exact contDiff_const.mul (hG.comp (contDiff_id.div_const T))

/-- The additive exponential is smooth as a function of its real argument. -/
theorem ee_contDiff : ContDiff ℝ ∞ ee := by
  unfold ee
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- Poisson summation for the modulated scaled weight, before evaluating the Fourier integral. -/
theorem GThat_poisson_raw {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (hsmooth : ContDiff ℝ ∞ G) {T : ℝ} (hT : 0 < T) (β : ℝ) :
    GThat G T β = ∑' m : ℤ,
      𝓕 (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) (m : ℝ) := by
  have hreal := GT_hasCompactSupport hsupp hT
  have hcomplex : HasCompactSupport (fun x : ℝ => (GT G T x : ℂ)) :=
    hreal.comp_left (g := Complex.ofReal) rfl
  have hc : HasCompactSupport (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) :=
    hcomplex.mul_right
  have hs : ContDiff ℝ ∞ (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) := by
    exact (Complex.ofRealCLM.contDiff.comp (GT_contDiff hsmooth T)).mul
      (ee_contDiff.comp (contDiff_const.mul contDiff_id))
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hs
  have hp := f.tsum_eq_tsum_fourier 0
  simp only [SchwartzMap.fourier_coe] at hp
  change (∑' n : ℤ, (GT G T (0 + n) : ℂ) * ee (β * (0 + n))) =
    ∑' n : ℤ, 𝓕 (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) (n : ℝ) *
      fourier n (0 : UnitAddCircle) at hp
  simpa [GThat] using hp

/-- Mathlib's real Fourier integral uses the negative sign in ee notation. -/
theorem fourier_eq_integral_ee (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, f x * ee (-ξ * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  have he : Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) =
      ee (-ξ * x) := by
    unfold ee
    congr 1
    push_cast
    ring
  rw [he, mul_comm]

/-- The Fourier transform of a modulated dilation is a shifted dilation of the transform. -/
theorem fourier_modulated_GT (G : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (β ξ : ℝ) :
    𝓕 (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) ξ =
      𝓕 (fun x : ℝ => (G x : ℂ)) (T * (ξ - β)) := by
  rw [fourier_eq_integral_ee, fourier_eq_integral_ee]
  let f : ℝ → ℂ := fun y => (G y : ℂ) * ee (-(T * (ξ - β)) * y)
  have hphase (x : ℝ) : β * x + -ξ * x = -(T * (ξ - β)) * (x / T) := by
    field_simp
    <;> ring
  calc
    (∫ x : ℝ, ((GT G T x : ℂ) * ee (β * x)) * ee (-ξ * x)) =
        ∫ x : ℝ, (T⁻¹ : ℂ) * f (x / T) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [GT, Complex.ofReal_mul, Complex.ofReal_inv, f]
      rw [mul_assoc, mul_assoc, ee_mul, hphase]
    _ = (T⁻¹ : ℂ) * (T • ∫ y : ℝ, f y) := by
      rw [integral_const_mul, Measure.integral_comp_div, abs_of_pos hT]
    _ = ∫ y : ℝ, f y := by
      rw [Complex.real_smul]
      simp [hT.ne']

/-- The exact Poisson identity behind Lemma 7.2. -/
theorem GThat_poisson {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (hsmooth : ContDiff ℝ ∞ G) {T : ℝ} (hT : 0 < T) (β : ℝ) :
    GThat G T β = ∑' m : ℤ,
      𝓕 (fun x : ℝ => (G x : ℂ)) (T * ((m : ℝ) - β)) := by
  rw [GThat_poisson_raw hsupp hsmooth hT]
  apply tsum_congr
  intro m
  exact fourier_modulated_GT G hT β m

end LeanLab.BhowmikGrimmelt2026
