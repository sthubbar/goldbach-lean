module

public import LeanLab.KadiriLumley2014.Kernel259
public import LeanLab.KadiriLumley2014.PsiFormula259

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4, the display before equation 2.16.
The exact polynomial-smoothed explicit formula.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Real Set MeasureTheory
open Task64 Task92 Task301
open LeanLab.PNTPort.ExplicitPsi1

/-- The upper logarithm is the exponential form used in the paper's remainder bound. -/
theorem inverse_square_exp (u y : ℝ) :
    1 / (Real.exp u * y) ^ 2 = Real.exp (-2 * u) / y ^ 2 := by
  have he : Real.exp (-2 * u) = (Real.exp u ^ 2)⁻¹ := by
    have hexp : Real.exp (2 * u) = Real.exp u ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [show -2 * u = -(2 * u) by ring, Real.exp_neg, hexp]
  rw [he, mul_pow]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual smoothed psi difference equals its polynomial main term, signed zero sum
and logarithmic remainder. No numerical zero theorem is assumed. -/
theorem psiAverage_explicit {m : ℕ} (hm : 0 < m) {δ u X : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hX : 2 < X) :
    psiAverage m δ u X =
      (Real.exp u - 1) * X * (1 + δ / 2 - (∑' ρ, complexZeroSummand m δ u X ρ).re) -
        (∫ t in (0 : ℝ)..1,
          (Real.log (1 - Real.exp (-2 * u) / (X * (1 + δ * t)) ^ 2) -
            Real.log (1 - 1 / (X * (1 + δ * t)) ^ 2)) * weight m t) /
          (2 * (∫ t in (0 : ℝ)..1, weight m t)) := by
  have hX0 : 0 < X := by linarith
  have he : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hUX : 2 < Real.exp u * X := by nlinarith
  have hL := integral_psi_explicit hm hX (mul_pos hX0 hδ)
  have hU := integral_psi_explicit hm hUX (mul_pos (mul_pos (Real.exp_pos u) hX0) hδ)
  have hlin : ∀ Y t : ℝ, Y + Y * δ * t = Y * (1 + δ * t) := by intro Y t; ring
  simp_rw [hlin] at hL hU
  rw [Zall_eq] at hL hU
  let K := fun (Y : ℝ) (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) =>
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
      (∫ t in (0 : ℝ)..1, ((Y * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ) * (weight m t : ℂ))
  change _ = _ - (∑' ρ, K X ρ).re - _ at hL
  change _ = _ - (∑' ρ, K (Real.exp u * X) ρ).re - _ at hU
  have hKU : Summable (K (Real.exp u * X)) :=
    summable_scaled_psi_kernel hm hδ (mul_pos (Real.exp_pos u) hX0)
  have hKL : Summable (K X) := summable_scaled_psi_kernel hm hδ hX0
  have hK : (∑' ρ, K (Real.exp u * X) ρ) - (∑' ρ, K X ρ) =
      (((Real.exp u - 1) * X * (∫ t in (0 : ℝ)..1, weight m t) : ℝ) : ℂ) *
        (∑' ρ, complexZeroSummand m δ u X ρ) := by
    rw [← hKU.tsum_sub hKL, ← tsum_mul_left]
    exact tsum_congr (fun ρ => psi_kernel_difference m hδ.le hu hX0 ρ)
  have hKr := congrArg Complex.re hK
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hKr
  let L : ℝ → ℝ := fun t => X * (1 + δ * t)
  let U : ℝ → ℝ := fun t => Real.exp u * X * (1 + δ * t)
  have hLic : IntervalIntegrable (fun t : ℝ => (L t - Real.log (2 * π)) * weight m t) volume 0 1 :=
    (by unfold L weight; fun_prop : Continuous (fun t : ℝ => (L t - Real.log (2 * π)) * weight m t)).intervalIntegrable _ _
  have hUic : IntervalIntegrable (fun t : ℝ => (U t - Real.log (2 * π)) * weight m t) volume 0 1 :=
    (by unfold U weight; fun_prop : Continuous (fun t : ℝ => (U t - Real.log (2 * π)) * weight m t)).intervalIntegrable _ _
  have hmain : (∫ t in (0 : ℝ)..1, (U t - Real.log (2 * π)) * weight m t) -
      (∫ t in (0 : ℝ)..1, (L t - Real.log (2 * π)) * weight m t) =
      (Real.exp u - 1) * X * (∫ t in (0 : ℝ)..1, (1 + δ * t) * weight m t) := by
    rw [← intervalIntegral.integral_sub hUic hLic, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [L, U]
    ring
  have hRLc := trivial_log_continuousOn hX (mul_nonneg hX0.le hδ.le)
  have hRUc := trivial_log_continuousOn hUX
    (mul_nonneg (mul_nonneg (Real.exp_nonneg u) hX0.le) hδ.le)
  simp_rw [hlin] at hRLc hRUc
  have hRLi : IntervalIntegrable (fun t : ℝ => Real.log (1 - 1 / (L t) ^ 2) * weight m t) volume 0 1 :=
    (hRLc.mul (weight_continuous m).continuousOn).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hRUi : IntervalIntegrable (fun t : ℝ => Real.log (1 - 1 / (U t) ^ 2) * weight m t) volume 0 1 :=
    (hRUc.mul (weight_continuous m).continuousOn).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hrem : (∫ t in (0 : ℝ)..1,
      (Real.log (1 - Real.exp (-2 * u) / (L t) ^ 2) - Real.log (1 - 1 / (L t) ^ 2)) * weight m t) =
      (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (U t) ^ 2) * weight m t) -
      (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (L t) ^ 2) * weight m t) := by
    rw [← intervalIntegral.integral_sub hRUi hRLi]
    apply intervalIntegral.integral_congr
    intro t _
    have hUL : U t = Real.exp u * L t := by dsimp [U, L]; ring
    dsimp only
    rw [hUL, inverse_square_exp]
    ring
  have hLmono : Monotone L := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hδ.le)) hX0.le
  have hUmono : Monotone U := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hδ.le))
      (mul_nonneg (Real.exp_nonneg u) hX0.le)
  have hLi := ((Chebyshev.psi_mono.comp hLmono).intervalIntegrable (μ := volume) (a := 0) (b := 1)).mul_continuousOn
    (weight_continuous m).continuousOn
  have hUi := ((Chebyshev.psi_mono.comp hUmono).intervalIntegrable (μ := volume) (a := 0) (b := 1)).mul_continuousOn
    (weight_continuous m).continuousOn
  simp only [Function.comp_def] at hLi hUi
  have hsplit : (∫ t in (0 : ℝ)..1, (Chebyshev.psi (U t) - Chebyshev.psi (L t)) * weight m t) =
      (∫ t in (0 : ℝ)..1, Chebyshev.psi (U t) * weight m t) -
      (∫ t in (0 : ℝ)..1, Chebyshev.psi (L t) * weight m t) := by
    rw [← intervalIntegral.integral_sub hUi hLi]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hmass := (weight_mass_pos m).ne'
  have hF := (div_eq_iff hmass).mp (weight_F0_exact m δ)
  unfold psiAverage
  simp_rw [← mul_assoc (Real.exp u) X]
  change (∫ t in (0 : ℝ)..1, (Chebyshev.psi (U t) - Chebyshev.psi (L t)) * weight m t) /
    (∫ t in (0 : ℝ)..1, weight m t) = _
  rw [hsplit, hU, hL]
  change _ = (Real.exp u - 1) * X * (1 + δ / 2 - (∑' ρ, complexZeroSummand m δ u X ρ).re) -
    (∫ t in (0 : ℝ)..1,
      (Real.log (1 - Real.exp (-2 * u) / (L t) ^ 2) - Real.log (1 - 1 / (L t) ^ 2)) * weight m t) /
      (2 * (∫ t in (0 : ℝ)..1, weight m t))
  rw [hrem]
  apply (div_eq_iff hmass).mpr
  rw [sub_mul, ← div_div, div_mul_cancel₀ _ hmass]
  dsimp only [L, U, K] at hmain hKr ⊢
  linear_combination hmain - hKr + ((Real.exp u - 1) * X) * hF

end LeanLab.KadiriLumley2014.Task259
