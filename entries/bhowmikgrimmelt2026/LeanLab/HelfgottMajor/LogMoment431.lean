module

public import LeanLab.HelfgottMajor.Gamma431
public import Mathlib
public import LeanLab.HelfgottMajor.Sec45

/-!
The scalar log squared Gaussian moment from P0014 page 43 display 4.42.
Differentiate the Gamma integral twice and substitute t squared.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.LogMoment431
open MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- The second Gamma derivative is its log squared integral at one half.
Source P0014 page 43 display 4.42, symbolic scalar integration.
-/
theorem gamma_second_log_integral :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) *
      ((Real.log t ^ 2 * Real.exp (-t) : ℝ) : ℂ)) =
      deriv (deriv Complex.Gamma) (1 / 2 : ℂ) := by
  let f : ℝ → ℂ := fun t => ((Real.log t * Real.exp (-t) : ℝ) : ℂ)
  have hc : ContinuousOn f (Ioi (0 : ℝ)) := by
    intro t ht
    unfold f
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (ne_of_gt ht)).mul
        (Real.continuous_exp.comp continuous_neg).continuousAt)).continuousWithinAt
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(1 : ℝ))) := by
    have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).isBigO
    have he : (fun t : ℝ => Real.exp (-t)) =O[atTop] (fun t : ℝ => t ^ (-2 : ℝ)) := by
      simpa only [one_mul, neg_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-2)).isBigO
    have hh := hl.mul he
    have hh' : (fun t : ℝ => Real.log t * Real.exp (-t)) =O[atTop]
        (fun t : ℝ => t ^ (-(1 : ℝ))) := by
      apply hh.congr' (Filter.Eventually.of_forall fun _ => rfl)
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
      norm_num
    rw [← isBigO_norm_left]
    simpa only [f, Complex.norm_real, isBigO_norm_left] using hh'
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(1 / 4 : ℝ))) := by
    have hl := (isLittleO_log_rpow_nhdsGT_zero (by norm_num : (-(1 / 4 : ℝ)) < 0)).isBigO
    have hexp : ContinuousWithinAt (fun t : ℝ => Real.exp (-t)) (Ioi 0) 0 :=
      (Real.continuous_exp.comp continuous_neg).continuousWithinAt
    have he : (fun t : ℝ => Real.exp (-t)) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
      isBigO_const_of_tendsto (by simpa using! hexp) one_ne_zero
    have hh := hl.mul he
    rw [← isBigO_norm_left]
    simpa only [f, Complex.norm_real, isBigO_norm_left, mul_one] using hh
  have hd := (mellin_hasDerivAt_of_isBigO_rpow
    (hc.locallyIntegrableOn measurableSet_Ioi) htop (by norm_num : (1 / 2 : ℂ).re < 1)
    hbot (by norm_num : (1 / 4 : ℝ) < (1 / 2 : ℂ).re)).2
  have hfirst (s : ℂ) (hs : 0 < s.re) : deriv Complex.Gamma s = mellin f s := by
    simpa only [mellin, f, smul_eq_mul, Complex.ofReal_mul] using
      (Complex.hasDerivAt_Gamma_of_re_pos hs).deriv
  have heq : deriv Complex.Gamma =ᶠ[𝓝 (1 / 2 : ℂ)] mellin f := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 / 2 : ℂ).re by norm_num)] with z hz
    exact hfirst z hz
  have hres := (hd.congr_of_eventuallyEq heq).deriv
  rw [hres]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [f, smul_eq_mul, RCLike.real_smul_eq_coe_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [show (1 / 2 : ℂ) - 1 = ((-(1 / 2 : ℝ)) : ℂ) by norm_num]
  change (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) * ((Real.log t : ℂ) ^ 2 * (Real.exp (-t) : ℂ)) =
    (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) *
      ((Real.log t : ℂ) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)))
  ring

/-- The scalar Gamma log squared integral has the explicit special function value.
Source P0014 page 43 display 4.42 before the square substitution.
-/
theorem scalar_gamma_log_square_integral :
    (∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (Real.log t ^ 2 * Real.exp (-t))) =
      Real.sqrt Real.pi * ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) := by
  apply Complex.ofRealLI.injective
  have hh := gamma_second_log_integral
  rw [Gamma431.deriv2_Gamma_one_half] at hh
  calc
    _ = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) *
        ((Real.log t ^ 2 * Real.exp (-t) : ℝ) : ℂ) := by
      rw [← LinearIsometry.integral_comp_comm]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have hpow := Complex.ofReal_cpow ht.le (-(1 / 2 : ℝ))
      simp only [Complex.ofReal_neg] at hpow
      rw [← hpow]
      simp only [Complex.ofRealLI_apply, Complex.ofReal_mul]
    _ = _ := hh
    _ = _ := by
      simp only [Complex.ofRealLI_apply, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofNat_log]

/-- The square substitution multiplies the Gaussian log squared moment by eight.
Source P0014 page 43 display 4.42, symbolic integration.
-/
theorem gaussian_log_square_substitution :
    (∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (Real.log t ^ 2 * Real.exp (-t))) =
      8 * ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) * Real.log t ^ 2 := by
  rw [← integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ)) (by norm_num), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpow : (t ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) = t⁻¹ := by
    rw [← Real.rpow_mul ht.le]
    norm_num
    exact Real.rpow_neg_one t
  dsimp only
  rw [hpow, Real.log_rpow ht]
  norm_num only [Real.rpow_two, Real.rpow_one, smul_eq_mul]
  field_simp
  <;> ring

/-- The exact scalar Gaussian log squared moment from P0014 page 43 display 4.42.
No Fourier, character or zero input is used.
-/
theorem gaussian_log_square_integral :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) * Real.log t ^ 2) = Sec45.nLog := by
  have h1 := scalar_gamma_log_square_integral
  rw [gaussian_log_square_substitution] at h1
  unfold Sec45.nLog
  linear_combination (1 / 8 : ℝ) * h1

end LeanLab.HelfgottMajor.LogMoment431
