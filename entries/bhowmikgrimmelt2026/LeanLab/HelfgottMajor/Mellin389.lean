module

public import LeanLab.HelfgottMajor.Gaussian269
public import Mathlib.Analysis.MellinInversion

/-!
The logarithmic Fourier profile behind the first energy leaf in Decomp389b.
Source book Part IV page 434, Plancherel after display 16.26.
This file checks the change of variables and input energy only.
It does not assert the Fourier L2 compatibility bridge or the zero sampling bound.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Mellin389
open Real MeasureTheory Set LeanLab.HelfgottArcs Decomp269a
open scoped FourierTransform

/-- The logarithmic Fourier profile for the Gaussian Mellin transform on real part one half.
Source book page 434, with the substitution t equal to exp of minus u.
-/
noncomputable def logGaussian (δ u : ℝ) : ℂ :=
  exp (-u / 2) • ((exp (-(exp (-u)) ^ 2 / 2) : ℂ) * e (δ * exp (-u)))

/-- Mathlib's Mellin to Fourier identity specialized to the Gaussian critical line.
This checks the 2 pi frequency normalization needed for the book page 434 Plancherel step.
-/
theorem mellin_eq_fourier_logGaussian (δ τ : ℝ) :
    gaussianMellin δ ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) =
      𝓕 (logGaussian δ) (τ / (2 * π)) := by
  rw [gaussianMellin, mellin_eq_fourier]
  have hr : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I).re = (1 / 2 : ℝ) := by norm_num
  have hi : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I).im = τ := by norm_num
  rw [hr, hi]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (τ / (2 * π)))
  funext u
  unfold logGaussian
  congr 1
  congr 1
  ring

/-- The Fourier phase has unit norm, so the logarithmic input energy is shift independent.
This is the integrand in the first Plancherel display on book page 434.
-/
theorem logGaussian_norm_sq (δ u : ℝ) :
    ‖logGaussian δ u‖ ^ 2 = exp (-u) * exp (-(exp (-u)) ^ 2) := by
  have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
  have he := he0 (δ * exp (-u))
  rw [logGaussian, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), norm_mul,
    he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
  rw [pow_two (exp (-u / 2)), ← exp_add,
    pow_two (exp (-(exp (-u)) ^ 2 / 2)), ← exp_add]
  congr 1 <;> congr 1 <;> ring

/-- The logarithmic Gaussian profile is square integrable, a prerequisite for L2 Plancherel.
Source book page 434, first Plancherel display.
-/
theorem logGaussian_memLp_two (δ : ℝ) : MemLp (logGaussian δ) 2 := by
  have hg : IntegrableOn (fun t : ℝ => exp (-t ^ 2)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (s := (0 : ℝ))
      (by norm_num) (by norm_num)
  have hi := (integrable_comp_exp (fun t : ℝ => exp (-t ^ 2))).mpr hg
  have hn := hi.comp_neg
  apply (memLp_two_iff_integrable_sq_norm (by unfold logGaussian e; fun_prop)).mpr
  apply hn.congr
  filter_upwards [] with u
  simpa only [smul_eq_mul] using (logGaussian_norm_sq δ u).symm

/-- The logarithmic Gaussian is integrable as well as square integrable.
This checks the L1 input for comparing integral Fourier and L2 Fourier on book page 434.
-/
theorem logGaussian_integrable (δ : ℝ) : Integrable (logGaussian δ) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * exp (-t ^ 2 / 2)) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
      (s := (-(1 / 2 : ℝ))) (by norm_num) (by norm_num)
    apply hh.congr_fun _ measurableSet_Ioi
    intro t ht
    change t ^ (-(1 / 2 : ℝ)) * exp (-(1 / 2 : ℝ) * t ^ 2) =
      t ^ (-(1 / 2 : ℝ)) * exp (-t ^ 2 / 2)
    rw [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
  have hi := (integrable_comp_exp (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * exp (-t ^ 2 / 2))).mpr hg
  have hn := hi.comp_neg
  have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
  apply hn.mono' (by unfold logGaussian e; fun_prop : AEStronglyMeasurable (logGaussian δ))
  filter_upwards [] with u
  have hp : exp (-u) * (exp (-u)) ^ (-(1 / 2 : ℝ)) = exp (-u / 2) := by
    rw [← exp_mul, ← exp_add]
    congr 1
    ring
  rw [logGaussian, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), norm_mul,
    he0, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  simp only [smul_eq_mul]
  rw [← hp]
  exact le_of_eq (by ring)

/-- The input squared norm integral equals sqrt pi over 2, the Gaussian square moment.
This checks the input side of the first Plancherel display on book page 434.
-/
theorem logGaussian_square_integral (δ : ℝ) :
    (∫ u : ℝ, ‖logGaussian δ u‖ ^ 2) = Sec45.nTwo := by
  simp_rw [logGaussian_norm_sq]
  rw [integral_neg_eq_self (fun u : ℝ => exp u * exp (-(exp u) ^ 2))]
  change (∫ u : ℝ, exp u • exp (-(exp u) ^ 2)) = _
  rw [integral_comp_exp (fun t : ℝ => exp (-t ^ 2))]
  have h := Gaussian269.gaussian_moment 1 1 (by norm_num) (by norm_num)
  rw [Gamma_one_half_eq] at h
  simpa [Sec45.nTwo, div_eq_mul_inv, mul_comm] using h

/-- A power majorant for the logarithm squared in the Gaussian log moment.
This checks convergence of the second moment in P0014 display 4.42 on page 43.
-/
theorem log_square_majorant (t : ℝ) (ht : 0 < t) :
    log t ^ 2 ≤ 16 * (t ^ (1 / 2 : ℝ) + t ^ (-(1 / 2 : ℝ))) := by
  have hp : 0 ≤ t ^ (1 / 4 : ℝ) := rpow_nonneg ht.le _
  have hn : 0 ≤ t ^ (-(1 / 4 : ℝ)) := rpow_nonneg ht.le _
  have hp2 : (t ^ (1 / 4 : ℝ)) ^ 2 = t ^ (1 / 2 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul ht.le]
    norm_num
  have hn2 : (t ^ (-(1 / 4 : ℝ))) ^ 2 = t ^ (-(1 / 2 : ℝ)) := by
    rw [← rpow_natCast, ← rpow_mul ht.le]
    norm_num
  by_cases hlog : 0 ≤ log t
  · have hh := log_le_rpow_div ht.le (by norm_num : (0 : ℝ) < 1 / 4)
    have hl : log t ≤ 4 * t ^ (1 / 4 : ℝ) := by linarith
    have hsq : log t ^ 2 ≤ 16 * (t ^ (1 / 4 : ℝ)) ^ 2 := by
      calc
        _ ≤ (4 * t ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog hl 2
        _ = _ := by ring
    rw [hp2] at hsq
    linarith only [hsq, rpow_nonneg ht.le (-(1 / 2 : ℝ))]
  · have hh := neg_rpow_div_le_log ht.le (by norm_num : (0 : ℝ) < 1 / 4)
    have hl : -log t ≤ 4 * t ^ (-(1 / 4 : ℝ)) := by linarith
    have hsq : log t ^ 2 ≤ 16 * (t ^ (-(1 / 4 : ℝ))) ^ 2 := by
      calc
        _ = (-log t) ^ 2 := by ring
        _ ≤ (4 * t ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
        _ = _ := by ring
    rw [hn2] at hsq
    linarith only [hsq, rpow_nonneg ht.le (1 / 2 : ℝ)]

/-- The actual Gaussian log squared moment converges absolutely.
This checks that the integral in P0014 page 43 display 4.42 is defined.
Its closed form and the numerical value 1.94753 are not asserted here.
-/
theorem gaussian_log_square_integrable :
    IntegrableOn (fun t : ℝ => exp (-t ^ 2) * log t ^ 2) (Ioi 0) := by
  have hp : IntegrableOn (fun t : ℝ => t ^ (1 / 2 : ℝ) * exp (-t ^ 2)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (s := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
  have hn : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * exp (-t ^ 2)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (s := (-(1 / 2 : ℝ)))
      (by norm_num) (by norm_num)
  apply ((hp.add hn).const_mul 16).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (log_square_majorant t ht) (exp_pos (-t ^ 2)).le
  simp only [Pi.add_apply, neg_div] at *
  convert hh using 1 <;> ring

end LeanLab.HelfgottMajor.Mellin389
