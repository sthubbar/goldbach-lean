module

public import LeanLab.KadiriLumley2014.ZeroDefinitions259
public import LeanLab.KadiriLumley2014.OmegaIntegral
public import LeanLab.KadiriLumley2014.LogRemainder92

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equations 2.16 to 2.19.
The psi estimate below is conditional on the explicit formula identity.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64 Task92

/-- The complex zero contribution whose norm is the absolute summand in equation 2.19. -/
noncomputable def complexZeroSummand (m : ℕ) (δ u X : ℝ)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) : ℂ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * smoothingG m δ u ρ *
    (X : ℂ) ^ ((ρ : ℂ) - 1)

/-- Positive real X gives exactly the absolute summand used by the paper. -/
theorem norm_complexZeroSummand (m : ℕ) (δ u : ℝ) {X : ℝ} (hX : 0 < X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ‖complexZeroSummand m δ u X ρ‖ = zeroSummand m δ u X ρ := by
  simp [complexZeroSummand, zeroSummand,
    Complex.norm_cpow_eq_rpow_re_of_pos hX]

/-- Summability of the absolute family gives convergence of the actual complex family. -/
theorem complexZeroSummand_summable (m : ℕ) (δ u : ℝ) {X : ℝ} (hX : 0 < X)
    (hs : Summable (zeroSummand m δ u X)) :
    Summable (complexZeroSummand m δ u X) := by
  apply Summable.of_norm
  simpa only [norm_complexZeroSummand m δ u hX] using hs

/-- The triangle inequality for the convergent complex zero sum. -/
theorem norm_complexZeroSum_le (m : ℕ) (δ u : ℝ) {X : ℝ} (hX : 0 < X)
    (hs : Summable (zeroSummand m δ u X)) :
    ‖∑' ρ, complexZeroSummand m δ u X ρ‖ ≤ zeroError m δ u X := by
  have hn : Summable (fun ρ => ‖complexZeroSummand m δ u X ρ‖) := by
    simpa only [norm_complexZeroSummand m δ u hX] using hs
  simpa only [norm_complexZeroSummand m δ u hX, zeroError] using norm_tsum_le_tsum_norm hn

/-- The real part of the complex zero sum is bounded by Sigma. -/
theorem re_complexZeroSum_le (m : ℕ) (δ u : ℝ) {X : ℝ} (hX : 0 < X)
    (hs : Summable (zeroSummand m δ u X)) :
    (∑' ρ, complexZeroSummand m δ u X ρ).re ≤ zeroError m δ u X :=
  (Complex.re_le_norm _).trans (norm_complexZeroSum_le m δ u hX hs)

/-- Page 4 equations 2.16 to 2.19, conditional on the displayed explicit formula identity.
Summability and the logarithmic remainder estimate supply all remaining steps. -/
theorem psi_lower_of_explicit_identity (m : ℕ) {δ u X : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hX : 3 ≤ X)
    (hs : Summable (zeroSummand m δ u X))
    (hformula : psiAverage m δ u X =
      (Real.exp u - 1) * X * (1 + δ / 2 - (∑' ρ, complexZeroSummand m δ u X ρ).re) -
        (∫ t in (0 : ℝ)..1,
          (Real.log (1 - Real.exp (-2 * u) / (X * (1 + δ * t)) ^ 2) -
            Real.log (1 - 1 / (X * (1 + δ * t)) ^ 2)) * weight m t) /
          (2 * (∫ t in (0 : ℝ)..1, weight m t))) :
    (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
      psiAverage m δ u X := by
  have hX0 : 0 < X := by linarith
  have hz := re_complexZeroSum_le m δ u hX0 hs
  have hr := weighted_log_remainder_bound m hu hδ hX
  rw [neg_div] at hr
  have hC : 0 ≤ (Real.exp u - 1) * X :=
    mul_nonneg (sub_nonneg.mpr (Real.one_le_exp hu)) hX0.le
  rw [hformula]
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hz)]

/-- The positive real scaling factor X can be taken outside the weighted power integral. -/
theorem integral_cpow_scale (m : ℕ) {δ X : ℝ} (hδ : 0 ≤ δ) (hX : 0 < X) (s : ℂ) :
    (∫ t in (0 : ℝ)..1, ((X * (1 + δ * t) : ℝ) : ℂ) ^ s * (weight m t : ℂ)) =
      (X : ℂ) ^ s * (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hb : 0 ≤ 1 + δ * t := by nlinarith [mul_nonneg hδ ht.1]
  dsimp only
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX.le hb]
  ring

/-- Clearing the normalization in G recovers the raw complex zero contribution. -/
theorem complexZeroSummand_scaled (m : ℕ) (δ : ℝ) {u X : ℝ} (hu : 0 < u) (hX : 0 < X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    (((Real.exp u - 1) * X : ℝ) : ℂ) * complexZeroSummand m δ u X ρ =
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) *
        ((Complex.exp ((ρ : ℂ) * u) - 1) / (ρ : ℂ)) *
        (X : ℂ) ^ (ρ : ℂ) * weightTransform m δ ρ := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have he : Real.exp u - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)).ne'
  have hec : ((Real.exp u - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast he
  have hec' : Complex.exp (u : ℂ) - 1 ≠ 0 := by
    rw [← Complex.ofReal_exp]
    exact_mod_cast he
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have hr := ρ.property.2.1
    rw [h] at hr
    simp at hr
  unfold complexZeroSummand smoothingG
  rw [Complex.cpow_sub _ _ hXc, Complex.cpow_one]
  push_cast
  field_simp [hec']

end LeanLab.KadiriLumley2014.Task301
