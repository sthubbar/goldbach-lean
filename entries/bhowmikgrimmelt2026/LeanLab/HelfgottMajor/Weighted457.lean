module

public import LeanLab.HelfgottMajor.Mellin389
public import LeanLab.HelfgottMajor.Fourier431

/-!
The Gaussian derivative profile in P0014 page 35 display 4.14.
The additional factor t moves the Mellin line from one half to three halves.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Weighted457
open Real MeasureTheory Set LeanLab.HelfgottArcs Decomp269a Mellin389
open scoped FourierTransform

/-- The logarithmic Fourier profile for t times the shifted Gaussian, display 4.14. -/
noncomputable def weightedProfile (δ u : ℝ) : ℂ := exp (-u) • logGaussian δ u

/-- The input square energy density for the three halves Mellin line, page 35. -/
theorem weightedProfile_norm_sq (δ u : ℝ) :
    ‖weightedProfile δ u‖ ^ 2 =
      exp (-u) ^ 2 * (exp (-u) * exp (-(exp (-u)) ^ 2)) := by
  rw [weightedProfile, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_pos (exp_pos _), logGaussian_norm_sq]

/-- The weighted Gaussian profile is square integrable, for display 4.15 on page 35. -/
theorem weightedProfile_memLp_two (δ : ℝ) : MemLp (weightedProfile δ) 2 := by
  have hg : IntegrableOn (fun t : ℝ => t ^ 2 * exp (-t ^ 2)) (Ioi 0) := by
    simpa only [rpow_two, neg_mul, one_mul] using integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 : ℝ)) (s := (2 : ℝ)) (by norm_num) (by norm_num)
  have hi := ((integrable_comp_exp (fun t : ℝ => t ^ 2 * exp (-t ^ 2))).mpr hg).comp_neg
  apply (memLp_two_iff_integrable_sq_norm
    (by unfold weightedProfile logGaussian e; fun_prop)).mpr
  apply hi.congr
  filter_upwards [] with u
  rw [weightedProfile_norm_sq]
  simp only [smul_eq_mul]
  ring

/-- The weighted Gaussian profile is integrable, for Fourier Plancherel on page 35. -/
theorem weightedProfile_integrable (δ : ℝ) : Integrable (weightedProfile δ) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2)) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    apply hh.congr_fun _ measurableSet_Ioi
    intro t ht
    change t ^ (1 / 2 : ℝ) * exp (-(1 / 2 : ℝ) * t ^ 2) =
      t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2)
    rw [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
  have hi := ((integrable_comp_exp
    (fun t : ℝ => t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2))).mpr hg).comp_neg
  apply hi.mono' (by unfold weightedProfile logGaussian e; fun_prop)
  filter_upwards [] with u
  have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
  rw [weightedProfile, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _),
    logGaussian, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), norm_mul,
    he0, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  simp only [smul_eq_mul]
  rw [← exp_mul]
  apply le_of_eq
  congr 2
  ring

/-- The weighted profile square integral is the Gaussian derivative norm on page 43.
This is the input energy for the first term of display 4.14 on page 35.
-/
theorem weightedProfile_square_integral (δ : ℝ) :
    (∫ u : ℝ, ‖weightedProfile δ u‖ ^ 2) = sqrt π / 4 := by
  simp_rw [weightedProfile_norm_sq]
  rw [integral_neg_eq_self
    (fun u : ℝ => exp u ^ 2 * (exp u * exp (-(exp u) ^ 2)))]
  have heq : (fun u : ℝ => exp u ^ 2 * (exp u * exp (-(exp u) ^ 2))) =
      (fun u : ℝ => exp u • ((exp u) ^ 2 * exp (-(exp u) ^ 2))) := by
    funext u
    simp only [smul_eq_mul]
    ring
  rw [heq, integral_comp_exp (fun t : ℝ => t ^ 2 * exp (-t ^ 2))]
  have hg := Gaussian269.gaussian_moment 3 1 (by norm_num) (by norm_num)
  have hGamma : Gamma (3 / 2) = sqrt π / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Gamma_one_half_eq]
    ring
  rw [hGamma] at hg
  convert hg using 1 <;> norm_num [rpow_two]
  ring

/-- The three halves Mellin line is the Fourier transform of the weighted profile.
This is the logarithmic change of variables for display 4.14 on page 35.
-/
theorem weighted_line_eq_fourier (δ τ : ℝ) :
    gaussianMellin δ ((3 / 2 : ℂ) + τ * Complex.I) =
      𝓕 (weightedProfile δ) (τ / (2 * π)) := by
  rw [gaussianMellin, mellin_eq_fourier]
  have hr : ((3 / 2 : ℂ) + (τ : ℂ) * Complex.I).re = (3 / 2 : ℝ) := by norm_num
  have hi : ((3 / 2 : ℂ) + (τ : ℂ) * Complex.I).im = τ := by norm_num
  rw [hr, hi]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (τ / (2 * π)))
  funext u
  rw [weightedProfile, logGaussian, smul_smul, ← exp_add]
  congr 1
  congr 1
  ring

/-- The three halves Mellin line is square integrable, for display 4.15 on page 35. -/
theorem weighted_line_memLp_two (δ : ℝ) :
    MemLp (fun t : ℝ => gaussianMellin δ ((3 / 2 : ℂ) + t * Complex.I)) 2 := by
  have hf := Fourier431.fourier_memLp_two
    (weightedProfile_integrable δ) (weightedProfile_memLp_two δ)
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hscaled := hi.comp_div (by positivity : (2 * π : ℝ) ≠ 0)
  have hc : Continuous (𝓕 (weightedProfile δ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (weightedProfile_integrable δ)
  have hcont : Continuous (fun t : ℝ => 𝓕 (weightedProfile δ) (t / (2 * π))) :=
    hc.comp (by fun_prop)
  simp_rw [weighted_line_eq_fourier]
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hscaled

/-- Plancherel gives the full square energy on the three halves line.
Source P0014 page 35 display 4.15 and page 43 display 4.42.
-/
theorem weighted_line_integral (δ : ℝ) :
    (∫ t : ℝ, ‖gaussianMellin δ ((3 / 2 : ℂ) + t * Complex.I)‖ ^ 2) =
      2 * π * (sqrt π / 4) := by
  simp_rw [weighted_line_eq_fourier]
  rw [Measure.integral_comp_div (fun t : ℝ => ‖𝓕 (weightedProfile δ) t‖ ^ 2),
    abs_of_pos (by positivity : 0 < 2 * π), smul_eq_mul,
    Fourier431.integral_norm_sq_fourier
      (weightedProfile_integrable δ) (weightedProfile_memLp_two δ),
    weightedProfile_square_integral]

end LeanLab.HelfgottMajor.Weighted457
