module

public import LeanLab.HelfgottMajor.Decomp269a
public import LeanLab.HelfgottMajor.Gaussian123

/-!
Elementary Mellin prerequisites for the new Gaussian zero sums.
Source P0014 pages 31 and 39, displays 4.1 and 4.30.
These results do not assume the three OPEN analytic leaves.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Gaussian269
open Real LeanLab.HelfgottArcs Decomp269a MeasureTheory

/-- The value F_delta of 1 is the positive half-line Fourier main term in display 4.1, page 31. -/
theorem mellin_one (δ : ℝ) : gaussianMellin δ 1 = fhat etaHeart (-δ) := by
  unfold gaussianMellin mellin
  simp only [sub_self, Complex.cpow_zero, one_smul]
  rw [← integral_indicator measurableSet_Ioi]
  unfold fhat
  congr 1
  funext t
  simp only [Set.indicator, Set.mem_Ioi, etaHeart]
  split_ifs with ht
  · simp only [mul_neg, neg_neg]
    rw [mul_comm δ t, mul_comm]
  · simp

/-- The absolute value estimate behind display 4.30, page 39, for the Gaussian at any exponent.
This is an integral bound and does not estimate a sum over zeros.
-/
theorem mellin_norm_le (δ : ℝ) (s : ℂ) :
    ‖gaussianMellin δ s‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), t ^ (s.re - 1) * exp (-t ^ 2 / 2) := by
  unfold gaussianMellin mellin
  calc
    _ ≤ ∫ t in Set.Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
      rw [norm_smul, norm_mul, he, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      simp

/-- The Gaussian Mellin integral converges absolutely for positive real part.
This checks the defining transform used in Lemma 4.1 on page 31 and display 4.30 on page 39.
-/
theorem mellin_integrable (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
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

/-- Gaussian power moments in Gamma form, the substitution used for display 4.42 on page 43.
The parameters sigma and b are positive, so the Gamma integral is convergent.
-/
theorem gaussian_moment (σ b : ℝ) (hσ : 0 < σ) (hb : 0 < b) :
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

/-- The squared Gaussian L2 integral in display 4.42 on page 43. -/
theorem gaussian_square_integral :
    (∫ t in Set.Ioi (0 : ℝ), exp (-t ^ 2 / 2) ^ 2) = sqrt π / 2 := by
  have hg := gaussian_moment 1 1 (by norm_num) (by norm_num)
  rw [Gamma_one_half_eq] at hg
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), exp (-(t ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [pow_two, ← exp_add]
      congr 1
      ring
    _ = _ := by simpa [div_eq_mul_inv, mul_comm] using hg

/-- The squared Gaussian derivative L2 integral in display 4.42 on page 43. -/
theorem gaussian_derivative_square_integral :
    (∫ t in Set.Ioi (0 : ℝ), (t * exp (-t ^ 2 / 2)) ^ 2) = sqrt π / 4 := by
  have hGamma : Gamma (3 / 2) = sqrt π / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Gamma_one_half_eq]
    ring
  have hg := gaussian_moment 3 1 (by norm_num) (by norm_num)
  rw [hGamma] at hg
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, rpow_two] at hg
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * exp (-(t ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [mul_pow, pow_two (exp _), ← exp_add]
      congr 2
      ring
    _ = _ := by
      convert hg using 1 <;> norm_num
      ring

end LeanLab.HelfgottMajor.Gaussian269
