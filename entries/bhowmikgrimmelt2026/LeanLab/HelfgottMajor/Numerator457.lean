module

public import LeanLab.HelfgottMajor.Weighted457
public import LeanLab.HelfgottMajor.Contour457

/-!
The Gaussian square energy input to the contour estimate in P0014 page 35 display 4.15.
Plancherel and the two Gaussian square moments give the repaired norm budget.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Numerator457
open Real MeasureTheory Set LeanLab.HelfgottArcs Decomp269a Mellin389 Contour457 Weighted457
open scoped FourierTransform

/-- The Gaussian numerator energy with no cited input or zero count hypothesis.
Source P0014 page 35 display 4.15 and page 43 display 4.42.
-/
theorem gaussian_numerator_L2 (δ : ℝ) :
    MemLp (gaussianNumerator δ) 2 ∧
      sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) ≤
        sqrt (2 * π) * (1 + 6 * |δ|) := by
  let f : ℝ → ℂ := fun t => gaussianMellin δ ((3 / 2 : ℂ) + t * Complex.I)
  let g : ℝ → ℂ := fun t => gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)
  let c : ℂ := 2 * π * Complex.I * δ
  have hf : MemLp f 2 := weighted_line_memLp_two δ
  have hg : MemLp g 2 := by
    have hfourier := Fourier431.fourier_memLp_two
      (logGaussian_integrable δ) (logGaussian_memLp_two δ)
    have hi := (memLp_two_iff_integrable_sq_norm hfourier.aestronglyMeasurable).mp hfourier
    have hscaled := hi.comp_div (by positivity : (2 * π : ℝ) ≠ 0)
    have hc : Continuous (𝓕 (logGaussian δ)) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ (logGaussian_integrable δ)
    have hcont : Continuous (fun t : ℝ => 𝓕 (logGaussian δ) (t / (2 * π))) :=
      hc.comp (by fun_prop)
    dsimp only [g]
    simp_rw [mellin_eq_fourier_logGaussian]
    exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hscaled
  have hE : (∫ t : ℝ, ‖g t‖ ^ 2) = 2 * π * (sqrt π / 2) := by
    simp_rw [g, mellin_eq_fourier_logGaussian]
    rw [Measure.integral_comp_div (fun t : ℝ => ‖𝓕 (logGaussian δ) t‖ ^ 2),
      abs_of_pos (by positivity : 0 < 2 * π), smul_eq_mul,
      Fourier431.integral_norm_sq_fourier
        (logGaussian_integrable δ) (logGaussian_memLp_two δ),
      logGaussian_square_integral]
    rfl
  have hid : gaussianNumerator δ = f - c • g := by
    funext t
    dsimp only [gaussianNumerator, f, g, c, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    congr 2 <;> ring
  have hN : MemLp (gaussianNumerator δ) 2 := hid ▸ hf.sub (hg.const_smul c)
  refine ⟨hN, ?_⟩
  have hnorm (v : ℝ → ℂ) (hv : MemLp v 2) :
      lpNorm v 2 volume = sqrt (∫ t : ℝ, ‖v t‖ ^ 2) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hv.aestronglyMeasurable]
    norm_num [sqrt_eq_rpow]
  have htri := lpNorm_sub_le (g := c • g) hf (by norm_num : (1 : ENNReal) ≤ 2)
  rw [← hid, hnorm _ hN, lpNorm_const_smul, hnorm _ hf, hnorm _ hg] at htri
  have hc : (‖c‖₊ : ℝ) = 2 * π * |δ| := by
    simp [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hc, weighted_line_integral δ, hE, sqrt_mul (by positivity : 0 ≤ 2 * π),
    sqrt_mul (by positivity : 0 ≤ 2 * π)] at htri
  have hp : sqrt π ≤ 1.78 := by
    rw [sqrt_le_left (by norm_num)]
    linarith [pi_lt_d2]
  have ha : sqrt (sqrt π / 4) ≤ 1 := by
    rw [sqrt_le_left (by norm_num)]
    linarith
  have hb : sqrt (sqrt π / 2) ≤ 0.945 := by
    rw [sqrt_le_left (by norm_num)]
    linarith
  have hcoef : 2 * π * sqrt (sqrt π / 2) ≤ 6 := by
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * π)
    linarith [pi_lt_d2]
  have hfirst := mul_le_mul_of_nonneg_left ha (sqrt_nonneg (2 * π))
  have hsecond := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (abs_nonneg δ) (sqrt_nonneg (2 * π)))
  nlinarith

end LeanLab.HelfgottMajor.Numerator457
