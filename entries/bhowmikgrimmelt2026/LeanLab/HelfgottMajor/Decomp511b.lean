module

public import LeanLab.HelfgottMajor.Gamma503
public import LeanLab.HelfgottMajor.Ray640
public import Mathlib

/-!
P0014 displays 3.66 and 3.67, pages 26 and 27.
Independent integration by parts for the shared Gaussian Mellin transform.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Decomp511b
open Real MeasureTheory Filter Set
open LeanLab.HelfgottArcs SplitGaussian123
open scoped Topology

/-- The twisted Mellin integrand is integrable for positive real part.
P0014 Section 2.3 on page 8 and the convergent raised integrals of display 3.67 on page 26. -/
theorem twisted_mellin_integrable (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * exp (-t ^ 2 / 2))
      (Set.Ioi 0) := by
    apply (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
      (by norm_num) (s := s.re - 1) (by linarith)).congr_fun _ measurableSet_Ioi
    intro t _
    dsimp only
    congr 1
    congr 1
    ring
  apply hg.mono'
  · have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.cpow_const
        (fun t ht => Complex.ofReal_mem_slitPlane.mpr ht)
    have he : Continuous (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) := by
      unfold e
      fun_prop
    have hf : ContinuousOn (fun t : ℝ =>
        (t : ℂ) ^ (s - 1) • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) (Set.Ioi 0) := by
      intro t ht
      exact (hc t ht).smul he.continuousAt.continuousWithinAt
    exact hf.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    simp only [norm_smul, norm_mul, he, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (exp_pos _), Complex.sub_re, Complex.one_re, le_refl]

/-- The product derivative underlying integration by parts.
P0014 display 3.67 on page 26 and display 4.14 on page 35, on the positive real ray. -/
theorem twisted_power_derivative (δ : ℝ) (s : ℂ) (hs : 0 < s.re) (t : ℝ) (ht : 0 < t) :
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

/-- The exact shared Mellin recurrence from integration by parts.
P0014 display 3.67 on page 26 and display 4.14 on page 35.
The real part is positive, so every displayed raw Mellin integral converges. -/
theorem twisted_mellin_recurrence (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    s * gaussianMellin δ s = gaussianMellin δ (s + 2) -
      (2 * Real.pi * Complex.I * δ) * gaussianMellin δ (s + 1) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ s * f t
  let A : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) * f t
  let c : ℂ := 2 * Real.pi * Complex.I * δ
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hA (z : ℂ) (hz : 0 < z.re) : IntegrableOn (A z) (Ioi 0) := by
    simpa only [smul_eq_mul] using twisted_mellin_integrable δ z hz
  have h0 := hA s hs
  have h1 := hA (s + 1) (by simp; linarith)
  have h2 := hA (s + 2) (by simp; linarith)
  have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt F
      (s * A s t - A (s + 2) t + c * A (s + 1) t) t := by
    simpa only [F, A, f, c, show (s + 2) - 1 = s + 1 by ring,
      add_sub_cancel_right, mul_assoc] using twisted_power_derivative δ s hs t ht
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

/-- The unconditional norm consequence of integration by parts.
P0014 display 3.67 on page 26 and the first bound on page 27.
No contour estimate is assumed in this step. -/
theorem twisted_recurrence_norm (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) :
    ‖gaussianMellin δ s‖ ≤
      (‖gaussianMellin δ (s + 2)‖ + (2 * π * |δ|) * ‖gaussianMellin δ (s + 1)‖) / ‖s‖ := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hσ
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : ‖(2 * (π : ℂ) * Complex.I * δ)‖ = 2 * π * |δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  apply (le_div_iff₀ hnorm).mpr
  calc
    _ = ‖s * gaussianMellin δ s‖ := by rw [norm_mul, mul_comm]
    _ = ‖gaussianMellin δ (s + 2) -
        (2 * (π : ℂ) * Complex.I * δ) * gaussianMellin δ (s + 1)‖ := by
      rw [twisted_mellin_recurrence δ s hσ]
    _ ≤ ‖gaussianMellin δ (s + 2)‖ +
        ‖(2 * (π : ℂ) * Complex.I * δ) * gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul, hc]

/-- The rotated ray kernel with its Jacobian factor left outside.
P0014 page 26 before display 3.66, with ray angle theta equal to pi over four minus alpha. -/
noncomputable def rotatedKernel (δ θ : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * Complex.exp
    (((-x ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) +
      ((2 * π * δ * x : ℝ) : ℂ) * Complex.I * Complex.exp ((θ : ℂ) * Complex.I))

/-- The exact modulus of the rotated kernel.
P0014 page 26, the first real integral estimate before display 3.66. -/
theorem rotatedKernel_norm (δ θ : ℝ) (s : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖rotatedKernel δ θ s x‖ = x ^ (s.re - 1) *
      exp (-cos (2 * θ) * x ^ 2 / 2 - 2 * π * δ * sin θ * x) := by
  unfold rotatedKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.one_re]
  congr 2
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, pow_two]
  ring

/-- The real Gaussian power moment used on the rotated ray.
P0014 page 26 before display 3.66, the change of variable to the Gamma integral. -/
theorem gaussian_power_moment (σ b : ℝ) (hσ : 0 < σ) (hb : 0 < b) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * exp (-(b * t ^ 2))) =
      (1 / 2 : ℝ) * (1 / b) ^ (σ / 2) * Gamma (σ / 2) := by
  have hg := integral_rpow_mul_exp_neg_mul_Ioi (a := σ / 2) (r := b)
    (by positivity) hb
  rw [← integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ)) (by norm_num)] at hg
  have hi : (∫ t in Set.Ioi (0 : ℝ),
      (2 * t ^ ((2 : ℝ) - 1)) •
        ((t ^ (2 : ℝ)) ^ (σ / 2 - 1) * exp (-(b * t ^ (2 : ℝ))))) =
      2 * ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * exp (-(b * t ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have hm : t * (t ^ (2 : ℝ)) ^ (σ / 2 - 1) = t ^ (σ - 1) := by
      calc
        _ = t ^ (1 : ℝ) * t ^ (2 * (σ / 2 - 1)) := by
          rw [rpow_one, rpow_mul ht.le]
        _ = t ^ (1 + 2 * (σ / 2 - 1)) := (rpow_add ht _ _).symm
        _ = _ := by congr 1; ring
    norm_num only [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one]
    calc
      _ = 2 * (t * (t ^ (2 : ℝ)) ^ (σ / 2 - 1)) *
          exp (-(b * t ^ (2 : ℝ))) := by ring
      _ = _ := by rw [hm, rpow_two]; ring
  rw [hi] at hg
  linarith

/-- The angle choice of display 3.66.
P0014 page 26 chooses alpha equal to half arcsin of two over the height.
The resulting ray has positive angle below pi over four and the stated exponential cost. -/
theorem rotation_angle_choice (t : ℝ) (ht : 100 ≤ t) :
    ∃ θ : ℝ, 0 < θ ∧ θ < π / 4 ∧ cos (2 * θ) = 2 / t ∧
      (π / 4 - θ) * t ≤ π / 2 := by
  have htpos : 0 < t := by linarith
  have hx : 0 < 2 / t := div_pos (by norm_num) htpos
  have hx1 : 2 / t < 1 := (div_lt_one htpos).mpr (by linarith)
  have ha0 : 0 < arcsin (2 / t) := arcsin_pos.mpr hx
  have ha1 : arcsin (2 / t) < π / 2 := arcsin_lt_pi_div_two.mpr hx1
  let θ := π / 4 - arcsin (2 / t) / 2
  refine ⟨θ, by dsimp [θ]; linarith, by dsimp [θ]; linarith, ?_, ?_⟩
  · dsimp [θ]
    rw [show 2 * (π / 4 - arcsin (2 / t) / 2) = π / 2 - arcsin (2 / t) by ring,
      cos_pi_div_two_sub, sin_arcsin (by linarith : -1 ≤ 2 / t) hx1.le]
  · have hJ := mul_le_sin ha0.le ha1.le
    rw [sin_arcsin (by linarith : -1 ≤ 2 / t) hx1.le] at hJ
    have hA : arcsin (2 / t) * t ≤ π := by
      calc
        _ = (π / 2) * ((2 / π * arcsin (2 / t)) * t) := by field_simp
        _ ≤ (π / 2) * 2 := mul_le_mul_of_nonneg_left
          ((le_div_iff₀ htpos).mp hJ) (by positivity)
        _ = _ := by ring
    dsimp [θ]
    nlinarith only [hA]

/-- The real Gaussian majorant of the rotated kernel.
P0014 page 26 before display 3.66. The nonnegative phase damping may be dropped. -/
theorem rotatedKernel_majorant (δ θ : ℝ) (s : ℂ) (x : ℝ) (hx : 0 < x)
    (hphase : 0 ≤ δ * sin θ) :
    ‖rotatedKernel δ θ s x‖ ≤
      x ^ (s.re - 1) * exp (-((cos (2 * θ) / 2) * x ^ 2)) := by
  rw [rotatedKernel_norm δ θ s x hx]
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hx.le _)
  apply exp_le_exp.mpr
  have h : 0 ≤ (2 * π * x) * (δ * sin θ) := mul_nonneg (by positivity) hphase
  nlinarith only [h]

/-- The rotated ray is integrable and its norm has the exact Gamma majorant.
P0014 page 26 before display 3.66. No contour deformation is assumed here. -/
theorem rotated_ray_majorant (δ θ : ℝ) (s : ℂ) (hσ : 0 < s.re)
    (hcos : 0 < cos (2 * θ)) (hphase : 0 ≤ δ * sin θ) :
    IntegrableOn (rotatedKernel δ θ s) (Ioi 0) ∧
      ‖∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x‖ ≤
        (1 / 2 : ℝ) * (1 / (cos (2 * θ) / 2)) ^ (s.re / 2) * Gamma (s.re / 2) := by
  have hg : IntegrableOn (fun x : ℝ =>
      x ^ (s.re - 1) * exp (-((cos (2 * θ) / 2) * x ^ 2))) (Ioi 0) := by
    apply (integrableOn_rpow_mul_exp_neg_mul_sq (b := cos (2 * θ) / 2)
      (by positivity) (s := s.re - 1) (by linarith)).congr_fun _ measurableSet_Ioi
    intro x _
    dsimp only
    congr 1
    congr 1
    ring
  have hpoint : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ‖rotatedKernel δ θ s x‖ ≤ x ^ (s.re - 1) * exp (-((cos (2 * θ) / 2) * x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact rotatedKernel_majorant δ θ s x hx hphase
  have hi : IntegrableOn (rotatedKernel δ θ s) (Ioi 0) := by
    apply hg.mono' _ hpoint
    have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.cpow_const
        (fun x hx => Complex.ofReal_mem_slitPlane.mpr hx)
    have he : Continuous (fun x : ℝ => Complex.exp
      (((-x ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) +
        ((2 * π * δ * x : ℝ) : ℂ) * Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) := by
      fun_prop
    exact (hc.mul he.continuousOn).aestronglyMeasurable measurableSet_Ioi
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
        x ^ (s.re - 1) * exp (-((cos (2 * θ) / 2) * x ^ 2)) :=
      norm_integral_le_of_norm_le hg hpoint
    _ = _ := gaussian_power_moment s.re (cos (2 * θ) / 2) hσ (by positivity)

/-- The norm factor of the rotated Mellin ray.
P0014 page 26 before display 3.66, the factor exp of minus theta times the height. -/
theorem rotated_prefactor_norm (θ : ℝ) (s : ℂ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I * s)‖ = exp (-θ * s.im) := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Conjugation reflects both the twist and the Mellin argument.
P0014 page 27 at the conclusion of Theorem 3.1. The twist changes sign as well. -/
theorem twisted_mellin_conjugate (δ : ℝ) (s : ℂ) :
    starRingEnd ℂ (gaussianMellin δ s) =
      gaussianMellin (-δ) (starRingEnd ℂ s) := by
  unfold gaussianMellin mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul, map_mul]
  have hp : starRingEnd ℂ ((x : ℂ) ^ (s - 1)) =
      (x : ℂ) ^ (starRingEnd ℂ s - 1) := by
    simpa only [map_sub, map_one, Complex.conj_ofReal] using
      (Complex.cpow_conj (x : ℂ) (s - 1)
        (by simpa only [Complex.arg_ofReal_of_nonneg hx.le] using pi_ne_zero.symm)).symm
  have he : starRingEnd ℂ (e (δ * x)) = e (-δ * x) := by
    unfold e
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hp, he, Complex.conj_ofReal]

/-- The optimized rotated ray estimate before identifying it with the original Mellin integral.
P0014 page 26, display 3.66. All real integration and angle costs are proved here. -/
theorem optimized_rotated_ray_bound (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) :
    ∃ θ : ℝ, 0 < θ ∧ θ < π / 4 ∧ IntegrableOn (rotatedKernel δ θ s) (Ioi 0) ∧
      ‖Complex.exp ((θ : ℂ) * Complex.I * s) *
        (∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x)‖ ≤
          exp (π / 2) / 2 * s.im ^ (s.re / 2) * Gamma (s.re / 2) *
            exp (-(π / 4) * s.im) := by
  have htpos : 0 < s.im := by linarith
  obtain ⟨θ, hθ0, hθ1, hc, hcost⟩ := rotation_angle_choice s.im ht
  have hcos : 0 < cos (2 * θ) := by rw [hc]; positivity
  have hphase : 0 ≤ δ * sin θ := mul_nonneg hδ.le
    (sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith [pi_pos]))
  have hr := rotated_ray_majorant δ θ s hσ hcos hphase
  have hi : 1 / (cos (2 * θ) / 2) = s.im := by
    rw [hc]
    field_simp [htpos.ne']
  have he : exp (-θ * s.im) ≤ exp (π / 2) * exp (-(π / 4) * s.im) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith only [hcost]
  have hΓ : 0 ≤ Gamma (s.re / 2) := (Gamma_pos_of_pos (by linarith)).le
  refine ⟨θ, hθ0, hθ1, hr.1, ?_⟩
  rw [norm_mul, rotated_prefactor_norm]
  calc
    _ ≤ exp (-θ * s.im) *
        ((1 / 2 : ℝ) * (1 / (cos (2 * θ) / 2)) ^ (s.re / 2) * Gamma (s.re / 2)) :=
      mul_le_mul_of_nonneg_left hr.2 (exp_nonneg _)
    _ = exp (-θ * s.im) * ((1 / 2 : ℝ) * s.im ^ (s.re / 2) * Gamma (s.re / 2)) := by rw [hi]
    _ ≤ (exp (π / 2) * exp (-(π / 4) * s.im)) *
        ((1 / 2 : ℝ) * s.im ^ (s.re / 2) * Gamma (s.re / 2)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by ring

/-- LEAF: Exact contour identity. P0014 page 26, the replacement of the positive real ray
by C prime before displays 3.65 and 3.66, parametrized by x times exp of i theta.
Positive real part makes the small arc vanish. The ray angle is below pi over four.
The actual rotated kernel integrability and every real norm estimate are proved separately. -/
theorem positive_ray_rotation (δ θ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    gaussianMellin δ s = Complex.exp ((θ : ℂ) * Complex.I * s) *
      (∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x) := by
  have hcos : 0 < cos (2 * θ) :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hphase : 0 ≤ δ * sin θ := mul_nonneg hδ.le
    (sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith [pi_pos]))
  have hp (x : ℝ) : Ray640.logKernel δ s (x + (θ : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I * s) *
        (exp x • rotatedKernel δ θ s (exp x)) := by
    simpa only [rotatedKernel, Complex.real_smul, smul_eq_mul, mul_assoc] using
      Ray640.logarithmic_ray_pullback δ θ x s
  have hreal : Integrable (fun x : ℝ => Ray640.logKernel δ s x) := by
    simp_rw [Ray640.logarithmic_real_pullback]
    exact (integrable_comp_exp _).mpr (twisted_mellin_integrable δ s hσ)
  have hrotated : Integrable (fun x : ℝ =>
      Ray640.logKernel δ s (x + (θ : ℂ) * Complex.I)) := by
    simp_rw [hp]
    exact ((integrable_comp_exp _).mpr
      (rotated_ray_majorant δ θ s hσ hcos hphase).1).const_mul _
  have h := Ray640.logarithmic_rotation δ θ s hσ hδ.le (by linarith) hθ0.le hθ1
    hreal hrotated
  simp_rw [Ray640.logarithmic_real_pullback, hp] at h
  rw [integral_const_mul, integral_comp_exp] at h
  rw [integral_comp_exp (fun t : ℝ => (t : ℂ) ^ (s - 1) •
    ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t)))] at h
  simpa only [gaussianMellin, mellin] using h

/-- The positive height case of display 3.66, from the contour identity and the proved ray bound.
P0014 page 26. The contour identity and the ray bound are proved. -/
theorem positive_raised_of_rotation (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) :
    ‖gaussianMellin δ s‖ ≤ exp (π / 2) / 2 *
      s.im ^ (s.re / 2) * Gamma (s.re / 2) * exp (-(π / 4) * s.im) := by
  obtain ⟨θ, hθ0, hθ1, hi, hb⟩ := optimized_rotated_ray_bound δ s hδ hσ ht
  rw [positive_ray_rotation δ θ s hδ hσ ht hθ0 hθ1]
  exact hb

/-- Raised contour bound from the exact contour identity. P0014 page 26, display 3.66.
This is the general positive real part estimate, before the integration by parts reduction.
It retains the exact Gamma factor and the printed exponential coefficient.
The contour identity, real ray estimate and reflection are proved. -/
theorem same_raised_contour (δ : ℝ) (s : ℂ) (hσ : 0 < s.re)
    (ht : 100 ≤ |s.im|) (hsign : 0 < δ * s.im) :
    ‖gaussianMellin δ s‖ ≤ exp (π / 2) / 2 *
      |s.im| ^ (s.re / 2) * Gamma (s.re / 2) * exp (-(π / 4) * |s.im|) := by
  by_cases htpos : 0 < s.im
  · have hdpos : 0 < δ := by
      by_contra h
      have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) htpos.le
      linarith
    have hheight : 100 ≤ s.im := by simpa only [abs_of_pos htpos] using ht
    simpa only [abs_of_pos htpos] using positive_raised_of_rotation δ s hdpos hσ hheight
  · have hheight : 100 ≤ -s.im := by
      simpa only [abs_of_nonpos (le_of_not_gt htpos)] using ht
    have htneg : s.im < 0 := by linarith
    have hdneg : δ < 0 := by
      by_contra h
      have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt h) htneg.le
      linarith
    have hsconj : 0 < (starRingEnd ℂ s).re := by simpa using hσ
    have hheightconj : 100 ≤ (starRingEnd ℂ s).im := by simpa using hheight
    have hb := positive_raised_of_rotation (-δ) (starRingEnd ℂ s)
      (by linarith) hsconj hheightconj
    have heq : ‖gaussianMellin δ s‖ = ‖gaussianMellin (-δ) (starRingEnd ℂ s)‖ := by
      simpa using congrArg norm (twisted_mellin_conjugate δ s)
    rw [heq]
    simpa [abs_of_neg htneg] using hb

end LeanLab.HelfgottMajor.Decomp511b
