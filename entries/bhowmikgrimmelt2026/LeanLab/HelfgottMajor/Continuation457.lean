module

public import LeanLab.HelfgottMajor.Gaussian269
public import LeanLab.HelfgottMajor.Contour457
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The Gaussian integration by parts used on P0014 pages 32 and 35.
The first moment fixes the regularized Mellin value at zero for every shift.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Continuation457
open Real Complex MeasureTheory Filter Set Asymptotics
open LeanLab.HelfgottArcs Decomp269a
open scoped Topology

/-- The differentiated Mellin numerator on the positive half line.
Source P0014 page 32 integration by parts and page 35 display 4.14.
-/
theorem power_gaussian_hasDerivAt (δ : ℝ) (s : ℂ) (hs : 0 < s.re) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ s * (Real.exp (-u ^ 2 / 2) : ℂ) * e (δ * u))
      (s * (t : ℂ) ^ (s - 1) * (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t) -
        (t : ℂ) ^ (s + 1) * (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t) +
        (2 * Real.pi * Complex.I * δ) * (t : ℂ) ^ s *
          (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) t := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hp := hasDerivAt_ofReal_cpow_const ht.ne' hs0
  have hgauss : HasDerivAt (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ))
      ((-t * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) t := by
    convert (((((hasDerivAt_id t).pow 2).neg.div_const 2).exp).ofReal_comp) using 1 <;>
      simp <;> ring
  have hphase : HasDerivAt (fun u : ℝ => e (δ * u))
      ((2 * Real.pi * Complex.I * δ) * e (δ * t)) t := by
    have hh := (((hasDerivAt_id t).ofReal_comp.const_mul
      (2 * (Real.pi : ℂ) * Complex.I * δ)).cexp)
    convert hh using 1
    · funext u
      simp only [e, id_eq]
      congr 1
      push_cast
      ring
    · simp only [e, id_eq]
      push_cast
      ring
  have hpow : (t : ℂ) ^ (s + 1) = (t : ℂ) ^ s * t := by
    rw [Complex.cpow_add _ _ (by exact_mod_cast ht.ne'), Complex.cpow_one]
  convert (hp.mul hgauss).mul hphase using 1 <;>
    simp only [Pi.mul_apply, hpow] <;> push_cast <;> ring

/-- The regularized Gaussian numerator has value one at zero for every shift.
Source P0014 page 32 before display 4.6 and page 35 display 4.14.
This is an actual moment identity and has no cited analytic hypothesis.
-/
theorem shifted_first_moment (δ : ℝ) :
    gaussianMellin δ 2 - (2 * Real.pi * Complex.I * δ) * gaussianMellin δ 1 = 1 := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  let c : ℂ := 2 * Real.pi * Complex.I * δ
  have hf (t : ℝ) : HasDerivAt f (-(t : ℂ) * f t + c * f t) t := by
    have hgauss : HasDerivAt (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ))
        ((-t * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) t := by
      convert (((((hasDerivAt_id t).pow 2).neg.div_const 2).exp).ofReal_comp) using 1 <;>
        simp <;> ring
    have hphase : HasDerivAt (fun u : ℝ => e (δ * u)) (c * e (δ * t)) t := by
      have hh := (((hasDerivAt_id t).ofReal_comp.const_mul c).cexp)
      convert hh using 1
      · funext u
        simp only [e, id_eq, c]
        congr 1
        push_cast
        ring
      · simp only [e, id_eq, c]
        push_cast
        ring
    convert hgauss.mul hphase using 1 <;> dsimp only [f, c] <;> push_cast <;> ring
  have hi1 : IntegrableOn f (Ioi 0) := by
    simpa only [smul_eq_mul, sub_self, Complex.cpow_zero, one_mul] using
      LeanLab.HelfgottMajor.Gaussian269.mellin_integrable δ 1 (by norm_num)
  have hi2 : IntegrableOn (fun t : ℝ => (t : ℂ) * f t) (Ioi 0) := by
    simpa only [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one, smul_eq_mul] using
      LeanLab.HelfgottMajor.Gaussian269.mellin_integrable δ 2 (by norm_num)
  have hdi : IntegrableOn (fun t : ℝ => -(t : ℂ) * f t + c * f t) (Ioi 0) := by
    simpa only [Pi.add_apply, Pi.neg_apply, neg_mul] using! hi2.neg.add (hi1.const_mul c)
  have hnorm (t : ℝ) : ‖f t‖ = Real.exp (-t ^ 2 / 2) := by
    have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    dsimp only [f]
    rw [norm_mul, he, mul_one, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have ht : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp_rw [hnorm]
    have hh := Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-1 / 2 : ℝ) < 0))
    convert hh using 1
    funext t
    congr 1
    ring
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have hc : Continuous f := by unfold f e; fun_prop
    exact hc.continuousAt.continuousWithinAt
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t _ => hf t) hdi ht
  have h2 : gaussianMellin δ 2 = ∫ t in Ioi (0 : ℝ), (t : ℂ) * f t := by
    norm_num [gaussianMellin, mellin, f, smul_eq_mul]
  have h1 : gaussianMellin δ 1 = ∫ t in Ioi (0 : ℝ), f t := by
    norm_num [gaussianMellin, mellin, f, smul_eq_mul]
  simp_rw [neg_mul] at hh
  have hadd : (∫ t in Ioi (0 : ℝ), -((t : ℂ) * f t) + c * f t) =
      (∫ t in Ioi (0 : ℝ), -((t : ℂ) * f t)) + (∫ t in Ioi (0 : ℝ), c * f t) := by
    simpa only [Pi.neg_apply, Pi.add_apply] using!
      integral_add hi2.neg (hi1.const_mul c)
  rw [hadd, integral_neg, integral_const_mul] at hh
  have hf0 : f 0 = 1 := by simp [f, e]
  rw [hf0, zero_sub] at hh
  rw [h2, h1]
  dsimp only [c] at hh
  linear_combination -hh

/-- The shifted Gaussian Mellin transform is holomorphic in its positive half plane.
Source P0014 page 32, the strip of definition in the written integration by parts argument.
-/
theorem gaussian_mellin_differentiable (δ : ℝ) (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ (gaussianMellin δ) s := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  have hn (t : ℝ) : ‖f t‖ = Real.exp (-t ^ 2 / 2) := by
    have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    dsimp only [f]
    rw [norm_mul, he, mul_one, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hc : Continuous f := by unfold f e; fun_prop
  have htop : f =O[atTop] (fun t : ℝ => Real.exp (-1 * t)) := by
    rw [← isBigO_norm_left]
    simp_rw [hn]
    simpa only [one_mul, mul_one, neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using
      (exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)).isBigO
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    simp only [hn, neg_zero, rpow_zero, norm_one, mul_one]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1)
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop hbot hs

/-- The continued Gaussian numerator is continuous at zero for every shift.
Source P0014 page 32 before display 4.6 and page 35 display 4.14.
-/
theorem regular_numerator_continuous (δ : ℝ) :
    ContinuousAt (fun s : ℂ => gaussianMellin δ (s + 2) -
      (2 * Real.pi * Complex.I * δ) * gaussianMellin δ (s + 1)) 0 := by
  have h2 := ContinuousAt.comp (f := fun s : ℂ => s + 2)
    (gaussian_mellin_differentiable δ ((0 : ℂ) + 2) (by norm_num)).continuousAt
    (by fun_prop)
  have h1 := ContinuousAt.comp (f := fun s : ℂ => s + 1)
    (gaussian_mellin_differentiable δ ((0 : ℂ) + 1) (by norm_num)).continuousAt
    (by fun_prop)
  exact h2.sub (h1.const_mul _)

/-- Integration by parts gives the shifted Gaussian Mellin recurrence.
Source P0014 page 32 and page 35 display 4.14.
-/
theorem gaussian_mellin_recurrence (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    s * gaussianMellin δ s = gaussianMellin δ (s + 2) -
      (2 * Real.pi * Complex.I * δ) * gaussianMellin δ (s + 1) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ s * f t
  let A : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) * f t
  let c : ℂ := 2 * Real.pi * Complex.I * δ
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hA (z : ℂ) (hz : 0 < z.re) : IntegrableOn (A z) (Ioi 0) := by
    simpa only [smul_eq_mul] using Gaussian269.mellin_integrable δ z hz
  have h0 := hA s hs
  have h1 := hA (s + 1) (by simp; linarith)
  have h2 := hA (s + 2) (by simp; linarith)
  have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt F
      (s * A s t - A (s + 2) t + c * A (s + 1) t) t := by
    simpa only [F, A, f, c, show (s + 2) - 1 = s + 1 by ring,
      add_sub_cancel_right, mul_assoc] using power_gaussian_hasDerivAt δ s hs t ht
  have hi : IntegrableOn (fun t => s * A s t - A (s + 2) t + c * A (s + 1) t) (Ioi 0) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using!
      ((h0.const_mul s).sub h2).add (h1.const_mul c)
  have hc : Continuous F := by
    exact (Complex.continuous_ofReal_cpow_const hs).mul (by unfold f e; fun_prop)
  have ht : Tendsto F atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
    have hh := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 1 / 2) s.re).tendsto_zero_of_tendsto hexp
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [F, f]
    have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, norm_mul, he, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_of_nonneg (Real.exp_pos _).le]
    congr 2
    ring
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousAt.continuousWithinAt
    (fun t ht => hderiv t ht) hi ht
  have hF0 : F 0 = 0 := by simp [F, hs0]
  rw [hF0, sub_self] at hh
  have hadd : (∫ t in Ioi (0 : ℝ), s * A s t - A (s + 2) t + c * A (s + 1) t) =
      (∫ t in Ioi (0 : ℝ), s * A s t - A (s + 2) t) +
        (∫ t in Ioi (0 : ℝ), c * A (s + 1) t) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using!
      integral_add ((h0.const_mul s).sub h2) (h1.const_mul c)
  have hsub : (∫ t in Ioi (0 : ℝ), s * A s t - A (s + 2) t) =
      (∫ t in Ioi (0 : ℝ), s * A s t) - (∫ t in Ioi (0 : ℝ), A (s + 2) t) := by
    simpa only [Pi.sub_apply] using! integral_sub (h0.const_mul s) h2
  rw [hadd, hsub, integral_const_mul, integral_const_mul] at hh
  have hM (z : ℂ) : gaussianMellin δ z = ∫ t in Ioi (0 : ℝ), A z t := by
    simp only [gaussianMellin, mellin, A, f, smul_eq_mul]
  rw [← hM s, ← hM (s + 2), ← hM (s + 1)] at hh
  dsimp only [c] at hh
  linear_combination hh

/-- The continued expression agrees with the defining Mellin integral in its original half plane.
Source P0014 page 32 integration by parts and page 35 display 4.14.
-/
theorem continuedGaussian_eq (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    Contour457.continuedGaussian δ s = gaussianMellin δ s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [Contour457.continuedGaussian, ← gaussian_mellin_recurrence δ s hs]
  exact mul_div_cancel_left₀ _ hs0

end LeanLab.HelfgottMajor.Continuation457
