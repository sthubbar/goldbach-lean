module

public import LeanLab.HelfgottMajor.Decomp639Contour
public import LeanLab.HelfgottMajor.Gamma503
public import LeanLab.HelfgottMajor.BookL1523
public import Mathlib

/-!
P0014 Theorem 3.1 and the coefficient reductions on pages 27 and 28.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Decomp511a
open Real SplitGaussian123 Filter
open scoped Topology

/-- LEAF numeric coefficient check. P0014 page 23, following display 3.55.
This checks the printed rounding of the elementary geometric factor to 7.82843. -/
theorem geometric_factor_rounding :
    2 / (1 - 1 / sqrt (2 : ℝ)) ≤ 7.82843 := by
  have hs : (7 / 5 : ℝ) ≤ sqrt 2 := le_sqrt_of_sq_le (by norm_num)
  have hi : 1 / sqrt (2 : ℝ) ≤ 5 / 7 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hd : 0 < 1 - 1 / sqrt (2 : ℝ) := by linarith
  rw [div_le_iff₀ hd]
  linarith

/-- LEAF numeric coefficient check. P0014 page 23, display 3.53.
This checks the printed scalar bound that is rounded upward to 1.63 in display 3.57. -/
theorem endpoint_factor_rounding :
    1 + (1 / sqrt (2 : ℝ)) / (0.79837 * sqrt 2) ≤ 1.62628 := by
  rw [div_div]
  have he : sqrt (2 : ℝ) * (0.79837 * sqrt 2) = 1.59674 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [he]
  norm_num

/-- LEAF Gaussian width rounding. P0014 page 23, after displays 3.54 and 3.55.
The contour geometry from A.29 is separate. This proves its elementary square root rounding. -/
theorem gaussian_width_rounding (r : ℝ) (hr : 0 ≤ r) :
    sqrt (0.86 * r) ≤ 0.93 * sqrt r := by
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_sqrt hr]

/-- LEAF coefficient bound. P0014 page 27, display 3.69, the row k equal to zero. -/
theorem main_coefficient_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    2 * (1 + (7.83 : ℝ) ^ (1 - σ)) * ((3 / 2 : ℝ) / (2 * π)) ^ (1 - σ) ≤
      4.217 := by
  let b : ℝ := (3 / 2) / (2 * π)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have h1 := rpow_one_add_le_one_add_mul_self (s := b - 1)
    (by linarith) (by linarith : 0 ≤ 1 - σ) (by linarith : 1 - σ ≤ 1)
  have h2 := rpow_one_add_le_one_add_mul_self (s := 7.83 * b - 1)
    (by nlinarith) (by linarith : 0 ≤ 1 - σ) (by linarith : 1 - σ ≤ 1)
  rw [show 1 + (b - 1) = b by ring] at h1
  rw [show 1 + (7.83 * b - 1) = 7.83 * b by ring] at h2
  have hbe : b ≤ (0.23874 : ℝ) := by
    dsimp [b]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pi_gt_d6]
  have hprod := mul_le_mul_of_nonneg_left hbe (by linarith : 0 ≤ 1 - σ)
  have hsum : 2 * (b ^ (1 - σ) + (7.83 * b) ^ (1 - σ)) ≤ 4.217 := by
    nlinarith
  calc
    _ = 2 * (b ^ (1 - σ) + (7.83 * b) ^ (1 - σ)) := by
      rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 7.83) hb]
      dsimp [b]
      ring
    _ ≤ _ := hsum

/-- The last error coefficient on the strip, page 10, display 3.2.
Here P_sigma is its printed first branch, since sigma lies between zero and one. -/
noncomputable def lastCoefficient (σ t d : ℝ) : ℝ :=
  (min (t / (2 * π * |d|)) (5 / 4 * sqrt t)) ^ (σ - 2)

/-- The same sign coefficient on the strip, page 10, display 3.3.
The factor sqrt pi times two pi abs delta equals the printed two pi to the three halves. -/
noncomputable def sameCoefficient (σ t d : ℝ) : ℝ :=
  exp (π / 2) / 2 * t ^ (σ / 2) *
    (1 + sqrt π * (2 * π * |d|) / sqrt t)

/-- LEAF coefficient reduction. P0014 page 27, display 3.69, using display 3.2.
The height assumption ensures both entries of the denominator minimum are at least two pi. -/
theorem mainCoefficient_le (σ t d : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hd : d ≠ 0) (ht : 100 ≤ t) (htd : 4 * π ^ 2 * |d| ≤ t) :
    mainCoefficient σ t d ≤ 4.217 := by
  have hp : 0 < 2 * π * |d| := by positivity
  have ha : 2 * π ≤ t / (2 * π * |d|) := by
    rw [le_div_iff₀ hp]
    nlinarith
  have hb : 2 * π ≤ sqrt t := by
    have hs : 10 ≤ sqrt t := le_sqrt_of_sq_le (by linarith)
    linarith [pi_lt_four]
  have hm : 2 * π ≤ min (t / (2 * π * |d|)) (sqrt t) := le_min ha hb
  have hmpos : 0 < min (t / (2 * π * |d|)) (sqrt t) := (by positivity : (0 : ℝ) < 2 * π).trans_le hm
  have hbase : (3 / 2 : ℝ) / min (t / (2 * π * |d|)) (sqrt t) ≤
      (3 / 2 : ℝ) / (2 * π) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hm
  have hmax : max ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1)) =
      (7.83 : ℝ) ^ (1 - σ) := by
    apply max_eq_left
    apply le_trans (rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
    exact one_le_rpow (by norm_num) (by linarith)
  unfold mainCoefficient
  rw [hmax]
  calc
    _ ≤ 2 * (1 + (7.83 : ℝ) ^ (1 - σ)) *
        ((3 / 2 : ℝ) / (2 * π)) ^ (1 - σ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      · exact rpow_le_rpow (by positivity) hbase (by linarith)
      · positivity
      · positivity
    _ ≤ _ := main_coefficient_bound σ hσ0 hσ1

/-- LEAF coefficient reduction. P0014 page 28, display 3.70, k equal to zero. -/
theorem lastCoefficient_le (σ t d : ℝ) (hσ1 : σ ≤ 1)
    (hd : d ≠ 0) (ht : 100 ≤ t) (htd : 4 * π ^ 2 * |d| ≤ t) :
    lastCoefficient σ t d ≤ (min (t / (2 * π * |d|)) (5 / 4 * sqrt t))⁻¹ := by
  have ha : 2 * π ≤ t / (2 * π * |d|) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hb : 2 * π ≤ 5 / 4 * sqrt t := by
    have hs : 10 ≤ sqrt t := le_sqrt_of_sq_le (by linarith)
    nlinarith [pi_lt_four]
  have hm : 1 ≤ min (t / (2 * π * |d|)) (5 / 4 * sqrt t) := by
    have hh := le_min ha hb
    linarith [pi_gt_three]
  unfold lastCoefficient
  rw [← rpow_neg_one]
  exact rpow_le_rpow_of_exponent_le hm (by linarith)

/-- LEAF coefficient reduction. P0014 page 28, display 3.70, k equal to zero. -/
theorem firstCoefficient_le (σ t : ℝ) (hσ1 : σ ≤ 1) (ht : 100 ≤ t) :
    firstCoefficient σ t ≤ (1 + (1 + sqrt 2) / t) * sqrt t := by
  unfold firstCoefficient
  rw [sqrt_eq_rpow t]
  apply mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ t) (by linarith))
  positivity

/-- LEAF coefficient estimate. P0014 page 28, the first coefficient in display 3.71. -/
theorem first_prefactor_le (t : ℝ) (ht : 100 ≤ t) :
    1 + (1 + sqrt 2) / t ≤ 1.0242 := by
  have hs : sqrt 2 ≤ (1.42 : ℝ) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h : (1 + sqrt 2) / t ≤ (0.0242 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- LEAF scalar estimate. P0014 page 28, display 3.71.
This derived bound absorbs a coarse polynomial envelope into the printed slack. -/
theorem polynomial_error_absorption (t : ℝ) (ht : 100 ≤ t) :
    9 * t * exp (-0.3 * t) ≤ 0.0008 := by
  have hpoly : t * exp (-0.13 * t) ≤ (100 / 13 : ℝ) := by
    have h := mul_exp_neg_le_exp_neg_one (0.13 * t)
    have he : exp (-1 : ℝ) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    rw [show -(0.13 * t) = -0.13 * t by ring] at h
    nlinarith only [h, he]
  have hexp : (131072 : ℝ) ≤ exp 17 := by
    calc
      _ = (2 : ℝ) ^ 17 := by norm_num
      _ ≤ (exp 1) ^ 17 := pow_le_pow_left₀ (by norm_num) exp_one_gt_two.le 17
      _ = exp 17 := by rw [← exp_nat_mul]; norm_num
  have htail : exp (-0.17 * t) ≤ 1 / (131072 : ℝ) := by
    calc
      _ ≤ exp (-17 : ℝ) := exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hexp
  calc
    _ = 9 * (t * exp (-0.13 * t)) * exp (-0.17 * t) := by
      rw [show -0.3 * t = -0.13 * t + -0.17 * t by ring, exp_add]
      ring
    _ ≤ 9 * (100 / 13 : ℝ) * (1 / 131072) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpoly (by norm_num)
      · exact htail
      · positivity
      · norm_num
    _ ≤ _ := by norm_num

/-- LEAF coefficient envelope. P0014 page 28, display 3.71, for k equal to zero.
This coarse derived envelope is used only after multiplying by the exponential decay. -/
theorem sameCoefficient_le (σ t d : ℝ) (hσ1 : σ ≤ 1)
    (ht : 100 ≤ t) (htd : 4 * π ^ 2 * |d| ≤ t) :
    sameCoefficient σ t d ≤ 9 * t * sqrt t := by
  have htpos : 0 < t := by linarith
  have hspos : 0 < sqrt t := sqrt_pos.mpr htpos
  have hs : sqrt t ≤ t := sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hpi : sqrt π ≤ 2 * π := by
    have h : sqrt π ≤ π := sqrt_le_self_iff.mpr (Or.inr (by linarith [pi_gt_three]))
    linarith [pi_pos]
  have hratio : sqrt π * (2 * π * |d|) / sqrt t ≤ sqrt t := by
    rw [div_le_iff₀ hspos]
    have hh := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 2 * π * |d| by positivity)
    nlinarith [sq_sqrt htpos.le]
  have he : exp (π / 2) ≤ 9 := by
    calc
      _ ≤ exp 2 := exp_le_exp.mpr (by linarith [pi_lt_four])
      _ = (exp 1) ^ 2 := by rw [← exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ (exp_nonneg _) exp_one_lt_three.le 2
      _ = _ := by norm_num
  have hrpow : t ^ (σ / 2) ≤ sqrt t := by
    rw [sqrt_eq_rpow t]
    exact rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  unfold sameCoefficient
  calc
    _ ≤ (9 / 2 : ℝ) * sqrt t * (2 * t) := by
      apply mul_le_mul
      · exact mul_le_mul (by linarith) hrpow (by positivity) (by norm_num)
      · linarith
      · positivity
      · positivity
    _ = _ := by ring

/-- LEAF error absorption. P0014 page 28, displays 3.71 and 3.72, k equal to zero.
Both strip exponents are allowed independently, so the reflected pair is an instance. -/
theorem two_errors_le (σ₁ σ₂ t d : ℝ) (hσ₁ : σ₁ ≤ 1) (hσ₂ : σ₂ ≤ 1)
    (ht : 100 ≤ t) (htd : 4 * π ^ 2 * |d| ≤ t) :
    firstCoefficient σ₁ t * exp (-0.4798 * t) +
      sameCoefficient σ₂ t d * exp (-(π / 4) * t) ≤
        1.025 * sqrt t * exp (-0.4798 * t) := by
  have hf : firstCoefficient σ₁ t ≤ 1.0242 * sqrt t :=
    (firstCoefficient_le σ₁ t hσ₁ ht).trans
      (mul_le_mul_of_nonneg_right (first_prefactor_le t ht) (sqrt_nonneg t))
  have hs := sameCoefficient_le σ₂ t d hσ₂ ht htd
  have hp := polynomial_error_absorption t ht
  have hdec : exp (-(π / 4) * t) ≤ exp (-0.3 * t) * exp (-0.4798 * t) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have hπ : (3.14 : ℝ) ≤ π := by linarith [pi_gt_d2]
    have hh := mul_le_mul_of_nonneg_right hπ (by linarith : 0 ≤ t)
    nlinarith only [hh, ht]
  have hlast : sameCoefficient σ₂ t d * exp (-(π / 4) * t) ≤
      0.0008 * sqrt t * exp (-0.4798 * t) := by
    calc
      _ ≤ (9 * t * sqrt t) * (exp (-0.3 * t) * exp (-0.4798 * t)) :=
        mul_le_mul hs hdec (exp_nonneg _) (by positivity)
      _ = (9 * t * exp (-0.3 * t)) * sqrt t * exp (-0.4798 * t) := by ring
      _ ≤ _ := by gcongr
  have hfirst := mul_le_mul_of_nonneg_right hf (exp_nonneg (-0.4798 * t))
  nlinarith only [hfirst, hlast]

/-- LEAF real contour tail calculation. P0014 page 25, after display 3.64.
This is the Gaussian first moment used to dominate the tail on the positive real ray. -/
theorem gaussian_first_moment_tail (a : ℝ) :
    (∫ x : ℝ in Set.Ioi a, x * exp (-x ^ 2 / 2)) = exp (-a ^ 2 / 2) := by
  have hi : MeasureTheory.Integrable (fun x : ℝ => x * exp (-x ^ 2 / 2)) := by
    convert integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
    funext x
    congr 2
    ring
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -exp (-y ^ 2 / 2))
      (x * exp (-x ^ 2 / 2)) x := by
    intro x
    convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp.neg) using 1
    · rfl
    · simp
      ring
  have hsq : Filter.Tendsto (fun x : ℝ => -x ^ 2 / 2) Filter.atTop Filter.atBot := by
    have h := (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (by norm_num : (-1 / 2 : ℝ) < 0)
    convert h using 1
    funext x
    ring
  have hz : Filter.Tendsto (fun x : ℝ => -exp (-x ^ 2 / 2)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_exp_atBot.comp hsq).neg
  simpa using MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hd x) hi.integrableOn hz

/-- LEAF real contour tail bound. P0014 page 25, after display 3.64, first branch of P_sigma.
For a positive lower endpoint and sigma between zero and two, the real Gaussian tail is
at most a to the power sigma minus two times exp of minus a squared over two. -/
theorem gaussian_tail_bound (σ a : ℝ) (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => exp (-x ^ 2 / 2) * x ^ (σ - 1)) (Set.Ioi a) ∧
      (∫ x : ℝ in Set.Ioi a, exp (-x ^ 2 / 2) * x ^ (σ - 1)) ≤
        a ^ (σ - 2) * exp (-a ^ 2 / 2) := by
  have hg : MeasureTheory.IntegrableOn (fun x : ℝ =>
      a ^ (σ - 2) * (x * exp (-x ^ 2 / 2))) (Set.Ioi a) := by
    have h : MeasureTheory.IntegrableOn (fun x : ℝ => x * exp (-(1 / 2 : ℝ) * x ^ 2))
        (Set.Ioi a) :=
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
    have heq : (fun x : ℝ => x * exp (-(1 / 2 : ℝ) * x ^ 2)) =
        (fun x : ℝ => x * exp (-x ^ 2 / 2)) := by
      funext x
      congr 2
      ring
    rw [heq] at h
    exact h.const_mul _
  have hpoint : ∀ x ∈ Set.Ioi a,
      exp (-x ^ 2 / 2) * x ^ (σ - 1) ≤ a ^ (σ - 2) * (x * exp (-x ^ 2 / 2)) := by
    intro x hx
    have hxpos : 0 < x := ha.trans hx
    have hp := rpow_le_rpow_of_nonpos ha hx.le (by linarith : σ - 2 ≤ 0)
    have hid : x ^ (σ - 1) = x ^ (σ - 2) * x := by
      rw [show σ - 1 = (σ - 2) + 1 by ring, rpow_add_one hxpos.ne']
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ x * exp (-x ^ 2 / 2) by positivity)
    nlinarith only [hh]
  have hf : MeasureTheory.IntegrableOn (fun x : ℝ =>
      exp (-x ^ 2 / 2) * x ^ (σ - 1)) (Set.Ioi a) := by
    apply hg.mono'
    · fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_nonneg _)
        (rpow_nonneg (ha.trans hx).le _))]
      exact hpoint x hx
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x : ℝ in Set.Ioi a, a ^ (σ - 2) * (x * exp (-x ^ 2 / 2)) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx
    _ = _ := by rw [MeasureTheory.integral_const_mul, gaussian_first_moment_tail]

/-- LEAF boundary diagnostic. P0014 Section 2.3, page 8, absolute convergence convention.
Multiplication by the unit modulus twist preserves the failure of absolute integrability
on the line of real part zero. This concerns the raw integral, not analytic continuation. -/
theorem twisted_zero_re_not_integrable (δ : ℝ) (s : ℂ) (hs : s.re = 0) :
    ¬ MeasureTheory.IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) (Set.Ioi 0) := by
  intro hi
  apply Gamma503.gaussian_zero_re_not_integrable s hs
  apply hi.norm.mono'
  · have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.cpow_const
        (fun x hx => Complex.ofReal_mem_slitPlane.mpr hx)
    have hg : Continuous (fun x : ℝ => (exp (-x ^ 2 / 2) : ℂ)) := by fun_prop
    exact (hc.mul hg.continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with x
    have he : ‖LeanLab.HelfgottArcs.e (δ * x)‖ = 1 := by
      simp [LeanLab.HelfgottArcs.e, Complex.norm_exp, Complex.mul_re]
    simp only [norm_mul, he, mul_one, le_refl]

/-- The sealed raw Mellin integral assigns zero on the nonintegrable boundary.
P0014 Section 2.3, page 8, and the repository total integral convention.
This asserts no zero value for the paper's analytic continuation. -/
theorem raw_mellin_zero_re (δ : ℝ) (s : ℂ) (hs : s.re = 0) :
    gaussianMellin δ s = 0 := by
  simpa only [gaussianMellin, mellin, smul_eq_mul] using
    MeasureTheory.integral_undef (twisted_zero_re_not_integrable δ s hs)

/-- LEAF real ray norm bound. P0014 page 25, display 3.64 and its first P_sigma branch.
The twisted complex tail is integrable at every positive endpoint. Its absolute value is
bounded by the real Gaussian tail, independently of the shift and imaginary part. -/
theorem real_ray_tail_bound (δ : ℝ) (s : ℂ) (a : ℝ)
    (hσ0 : 0 ≤ s.re) (hσ2 : s.re ≤ 2) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) (Set.Ioi a) ∧
      ‖∫ x : ℝ in Set.Ioi a, (x : ℂ) ^ (s - 1) *
        ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
          a ^ (s.re - 2) * exp (-a ^ 2 / 2) := by
  have hf := gaussian_tail_bound s.re a hσ0 hσ2 ha
  have hn : ∀ᵐ x : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi a),
      ‖(x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) *
        LeanLab.HelfgottArcs.e (δ * x))‖ ≤ exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := ha.trans hx
    have he : ‖LeanLab.HelfgottArcs.e (δ * x)‖ = 1 := by
      simp [LeanLab.HelfgottArcs.e, Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, norm_mul, he, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    simp only [Complex.sub_re, Complex.one_re]
    exact le_of_eq (mul_comm _ _)
  refine ⟨hf.1.mono' ?_ hn,
    (MeasureTheory.norm_integral_le_of_norm_le hf.1 hn).trans hf.2⟩
  have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Set.Ioi a) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun x hx => Complex.ofReal_mem_slitPlane.mpr (ha.trans hx))
  have hg : Continuous (fun x : ℝ => (exp (-x ^ 2 / 2) : ℂ) *
      LeanLab.HelfgottArcs.e (δ * x)) := by
    unfold LeanLab.HelfgottArcs.e
    fun_prop
  exact (hc.mul hg.continuousOn).aestronglyMeasurable measurableSet_Ioi

/-- LEAF cutoff algebra. P0014 page 25, the last estimate following display 3.64.
The Gaussian exponent at the minimum endpoint equals the printed minimum of exponents. -/
theorem cutoff_exponent (δ τ : ℝ) (hδ : δ ≠ 0) :
    (min (|τ| / (2 * π * |δ|)) (5 / 4 * sqrt |τ|)) ^ 2 / 2 =
      min ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * |τ|) := by
  let a := |τ| / (2 * π * |δ|)
  let b := 5 / 4 * sqrt |τ|
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have heqa : a ^ 2 / 2 = (1 / 8 : ℝ) * (τ / (π * δ)) ^ 2 := by
    dsimp [a]
    simp only [div_pow, mul_pow, sq_abs]
    field_simp
    <;> ring
  have heqb : b ^ 2 / 2 = (25 / 32 : ℝ) * |τ| := by
    dsimp [b]
    rw [mul_pow, sq_sqrt (abs_nonneg τ)]
    ring
  calc
    _ = min (a ^ 2 / 2) (b ^ 2 / 2) := by
      rcases le_total a b with h | h
      · rw [min_eq_left h, min_eq_left]
        exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
          (pow_le_pow_left₀ ha h 2)
      · rw [min_eq_right h, min_eq_right]
        exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
          (pow_le_pow_left₀ hb h 2)
    _ = _ := by rw [heqa, heqb]

/-- LEAF real ray estimate. P0014 page 25 after display 3.64, with the endpoint from A.36.
This applies the proved real tail bound and rewrites its exponent exactly. -/
theorem gaussian_tail_cutoff (δ τ σ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    (∫ x : ℝ in Set.Ioi (min (|τ| / (2 * π * |δ|)) (5 / 4 * sqrt |τ|)),
      exp (-x ^ 2 / 2) * x ^ (σ - 1)) ≤
      lastCoefficient σ |τ| δ *
        exp (-min ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * |τ|)) := by
  have hm : 0 < min (|τ| / (2 * π * |δ|)) (5 / 4 * sqrt |τ|) := by
    apply lt_min
    · exact div_pos hτ (by positivity)
    · positivity
  have h := (gaussian_tail_bound σ _ hσ0 hσ2 hm).2
  unfold lastCoefficient
  rw [← cutoff_exponent δ τ hδ]
  simpa only [neg_div] using h

/-- The unevaluated norm comparison for the final ray in P0014 page 25, display 3.64.
The positive endpoint removes the power singularity. -/
theorem real_ray_tail_le_integral (δ : ℝ) (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ‖∫ x : ℝ in Set.Ioi a, (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      ∫ x : ℝ in Set.Ioi a, exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
  calc
    _ ≤ ∫ x : ℝ in Set.Ioi a, ‖(x : ℂ) ^ (s - 1) *
        ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := ha.trans hx
      have he : ‖LeanLab.HelfgottArcs.e (δ * x)‖ = 1 := by
        simp [LeanLab.HelfgottArcs.e, Complex.norm_exp, Complex.mul_re]
      rw [norm_mul, norm_mul, he, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_comm _ _

/-- LEAF OPEN contour reduction. P0014 pages 23 to 25, displays 3.56 and 3.59 to 3.64,
and page 25 after display 3.64 using A.36. The real tail is left unevaluated.
This retains the steepest descent contour, its main coefficient, the initial segment
estimate and the endpoint geometry. The last real integral is proved separately.
The Mellin integral has positive real part and uses no boundary convention. -/
theorem opposite_positive_contour_before_tail (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1)) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have htpos : 0 < |s.im| := by linarith
  let a := min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (div_pos htpos (by positivity)) (by positivity)
  have hgeom := Decomp639Contour.realEndpoint_lower δ s.im hd htpos
  have hep : 0 < Decomp639Contour.realEndpoint δ s.im := ha.trans_le hgeom
  have htail := real_ray_tail_le_integral δ s _ hep
  have hmono : (∫ x : ℝ in Set.Ioi (Decomp639Contour.realEndpoint δ s.im),
      exp (-x ^ 2 / 2) * x ^ (s.re - 1)) ≤
      ∫ x : ℝ in Set.Ioi a, exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
    apply MeasureTheory.setIntegral_mono_set
      (gaussian_tail_bound s.re a hσ0.le (by linarith) ha).1
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := ha.trans hx
      positivity
    · exact Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt hgeom hx)
  have hmain := Decomp639Contour.saddle_segment_bound δ s hσ0 hσ1 ht hsign
  have hfirst := Decomp639Contour.initial_segment_bound δ s hσ0 hσ1 ht hsign
  rw [Decomp639Contour.contour_shift δ s hσ0 hσ1 ht hsign]
  calc
    _ ≤ ‖Decomp639Contour.initialIntegral δ s‖ +
        ‖Decomp639Contour.saddleIntegral δ s‖ +
        ‖∫ x : ℝ in Set.Ioi (Decomp639Contour.realEndpoint δ s.im),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) *
            LeanLab.HelfgottArcs.e (δ * x))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := by linarith only [hmain, hfirst, htail, hmono]

/-- Raw boundary adapter for the contour reduction. P0014 pages 23 to 25, displays 3.56 and 3.59 to 3.64,
and page 25 after display 3.64 using A.36. The real tail is left unevaluated.
This retains the steepest descent contour, its main coefficient, the initial segment
estimate and the endpoint geometry. The last real integral is proved separately.
CONDITIONAL ON opposite_positive_contour_before_tail. -/
theorem opposite_contour_before_tail (δ : ℝ) (s : ℂ)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1)) := by
  by_cases hp : 0 < s.re
  · exact opposite_positive_contour_before_tail δ s hp hσ1 ht hsign
  · have hs0 : s.re = 0 := le_antisymm (le_of_not_gt hp) hσ0
    rw [raw_mellin_zero_re δ s hs0, norm_zero]
    have hd : δ ≠ 0 := by intro h; simp [h] at hsign
    have htpos : 0 < |s.im| := by linarith
    have hm : 0 < min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|) := by
      apply lt_min
      · exact div_pos htpos (by positivity)
      · positivity
    have hi : 0 ≤ ∫ x : ℝ in Set.Ioi
        (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hm.trans hx
      positivity
    have hmain : 0 ≤ mainCoefficient s.re |s.im| δ := by
      unfold mainCoefficient
      positivity
    have hfirst : 0 ≤ firstCoefficient s.re |s.im| := by
      unfold firstCoefficient
      positivity
    exact add_nonneg (add_nonneg (mul_nonneg hmain (exp_nonneg _))
      (mul_nonneg hfirst (exp_nonneg _))) hi

/-- LEAF contour bound. P0014 Theorem 3.1, pages 9 and 10, displays 3.1 and 3.2.
This is the opposite sign case restricted to the closed critical strip and height at least 100.
The three coefficients are exact printed coefficients, with P_sigma on its first branch.
CONDITIONAL ON opposite_contour_before_tail. The real tail calculation is proved. -/
theorem opposite_sign_contour (δ : ℝ) (s : ℂ)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      lastCoefficient s.re |s.im| δ *
        exp (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
          ((25 / 32 : ℝ) * |s.im|)) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have h := opposite_contour_before_tail δ s hσ0 hσ1 ht hsign
  have htail := gaussian_tail_cutoff δ s.im s.re hd (by linarith) hσ0 (by linarith)
  linarith only [h, htail]

/-- LEAF Gamma coefficient. P0014 page 27 after display 3.67.
The real Gamma function is at most square root pi on the interval from one half to one. -/
theorem gamma_half_strip_le (a : ℝ) (ha : 1 / 2 ≤ a) (hb : a ≤ 1) :
    Gamma a ≤ sqrt π := by
  have h := convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) ⟨ha, hb⟩
  have hp : 1 ≤ sqrt π := le_sqrt_of_sq_le (by nlinarith [pi_gt_three])
  simpa only [Gamma_one_half_eq, Gamma_one, max_eq_left hp] using h

/-- LEAF Gamma coefficient algebra. P0014 page 27 after displays 3.66 and 3.67.
This proves the bracket bound in the equal sign coefficient, with no contour hypothesis. -/
theorem gamma_recurrence_coefficient (σ t L : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 < t) (hL : 0 ≤ L) :
    (t ^ ((σ + 2) / 2) * Gamma ((σ + 2) / 2) +
      L * t ^ ((σ + 1) / 2) * Gamma ((σ + 1) / 2)) / t ≤
        t ^ (σ / 2) * (1 + sqrt π * L / sqrt t) := by
  have hΓ1 := Gamma503.gamma_le_one ((σ + 2) / 2) (by linarith) (by linarith)
  have hΓ2 := gamma_half_strip_le ((σ + 1) / 2) (by linarith) (by linarith)
  have hp1 : t ^ ((σ + 2) / 2) = t ^ (σ / 2) * t := by
    rw [show (σ + 2) / 2 = σ / 2 + 1 by ring, rpow_add ht, rpow_one]
  have hp2 : t ^ ((σ + 1) / 2) = t ^ (σ / 2) * sqrt t := by
    rw [show (σ + 1) / 2 = σ / 2 + 1 / 2 by ring, rpow_add ht, sqrt_eq_rpow t]
  calc
    _ ≤ (t ^ ((σ + 2) / 2) * 1 + L * t ^ ((σ + 1) / 2) * sqrt π) / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      exact add_le_add (mul_le_mul_of_nonneg_left hΓ1 (by positivity))
        (mul_le_mul_of_nonneg_left hΓ2 (by positivity))
    _ = t ^ (σ / 2) + (L * t ^ (σ / 2) * sqrt π) * (sqrt t / t) := by
      rw [hp1, hp2]
      field_simp
    _ = _ := by rw [sqrt_div_self']; ring

/-- Integration by parts reduction of the rotated contour bound. P0014 pages 26 and 27,
displays 3.66 and 3.67 and the first bound on page 27. The Gamma factors are unevaluated.
The positive real part makes every raised Mellin integral converge.
CONDITIONAL ON Decomp511b.same_raised_contour. Integration by parts is proved. -/
theorem same_shifted_contour (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : 0 < δ * s.im) :
    ‖gaussianMellin δ s‖ ≤ exp (π / 2) / 2 *
      ((|s.im| ^ ((s.re + 2) / 2) * Gamma ((s.re + 2) / 2) +
        (2 * π * |δ|) * |s.im| ^ ((s.re + 1) / 2) * Gamma ((s.re + 1) / 2)) / ‖s‖) *
        exp (-(π / 4) * |s.im|) := by
  have htpos : 0 < |s.im| := by linarith
  have hnorm : 0 < ‖s‖ := htpos.trans_le (Complex.abs_im_le_norm s)
  have h1 := Decomp511b.same_raised_contour δ (s + 2)
    (by simp; linarith)
    (by simpa using ht) (by simpa using hsign)
  have h2 := Decomp511b.same_raised_contour δ (s + 1)
    (by simp; linarith)
    (by simpa using ht) (by simpa using hsign)
  norm_num at h1 h2
  have h := Decomp511b.twisted_recurrence_norm δ s hσ0
  calc
    _ ≤ (‖gaussianMellin δ (s + 2)‖ +
        (2 * π * |δ|) * ‖gaussianMellin δ (s + 1)‖) / ‖s‖ := h
    _ ≤ ((exp (π / 2) / 2 * |s.im| ^ ((s.re + 2) / 2) *
        Gamma ((s.re + 2) / 2) * exp (-(π / 4) * |s.im|)) +
        (2 * π * |δ|) * (exp (π / 2) / 2 * |s.im| ^ ((s.re + 1) / 2) *
          Gamma ((s.re + 1) / 2) * exp (-(π / 4) * |s.im|))) / ‖s‖ := by
      apply div_le_div_of_nonneg_right _ hnorm.le
      apply add_le_add
      · simpa only [neg_mul] using h1
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [neg_mul] using h2
    _ = _ := by ring

/-- Gamma reduction of the equal sign contour bound. P0014 Theorem 3.1, page 10, display 3.3.
This is the equal nonzero sign case restricted to positive real part at most one and height at least 100.
CONDITIONAL ON same_shifted_contour. The Mellin integral has positive real part. Section 3.8 rotates the contour to angle pi over four minus alpha and integrates by parts. -/
theorem same_positive_contour (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : 0 < δ * s.im) :
    ‖gaussianMellin δ s‖ ≤
      sameCoefficient s.re |s.im| δ * exp (-(π / 4) * |s.im|) := by
  have htpos : 0 < |s.im| := by linarith
  have hc := gamma_recurrence_coefficient s.re |s.im| (2 * π * |δ|)
    hσ0.le hσ1 htpos (by positivity)
  have hnorm : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnum : 0 ≤ |s.im| ^ ((s.re + 2) / 2) * Gamma ((s.re + 2) / 2) +
      (2 * π * |δ|) * |s.im| ^ ((s.re + 1) / 2) * Gamma ((s.re + 1) / 2) := by
    apply add_nonneg
    · exact mul_nonneg (rpow_nonneg htpos.le _) (Gamma_pos_of_pos (by linarith)).le
    · exact mul_nonneg (by positivity) (Gamma_pos_of_pos (by linarith)).le
  have hf := div_le_div_of_nonneg_left hnum htpos hnorm
  have h := same_shifted_contour δ s hσ0 hσ1 ht hsign
  calc
    _ ≤ _ := h
    _ ≤ exp (π / 2) / 2 *
        (|s.im| ^ (s.re / 2) * (1 + sqrt π * (2 * π * |δ|) / sqrt |s.im|)) *
        exp (-(π / 4) * |s.im|) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hf.trans hc) (by positivity)) (exp_nonneg _)
    _ = _ := by unfold sameCoefficient; ring

/-- Raw boundary adapter for the equal sign contour bound. P0014 Theorem 3.1, page 10, display 3.3.
This is the equal nonzero sign case restricted to the closed critical strip and height at least 100.
CONDITIONAL ON same_positive_contour. Section 3.8 rotates the contour to angle pi over four minus alpha and integrates by parts. -/
theorem same_sign_contour (δ : ℝ) (s : ℂ)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : 0 < δ * s.im) :
    ‖gaussianMellin δ s‖ ≤
      sameCoefficient s.re |s.im| δ * exp (-(π / 4) * |s.im|) := by
  by_cases hp : 0 < s.re
  · exact same_positive_contour δ s hp hσ1 ht hsign
  · have hs0 : s.re = 0 := le_antisymm (le_of_not_gt hp) hσ0
    rw [raw_mellin_zero_re δ s hs0, norm_zero]
    unfold sameCoefficient
    positivity

/-- The opposite sign member of the pair and its equal sign reflection.
P0014 pages 27 and 28, displays 3.69 to 3.72 at k equal to zero.
CONDITIONAL ON opposite_sign_contour and same_sign_contour. -/
theorem opposite_pair_expansion (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      (1.025 * sqrt |s.im| * exp (-0.4798 * |s.im|) +
        (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|))⁻¹ *
          exp (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
            ((25 / 32 : ℝ) * |s.im|))) := by
  have ht : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  have htd : 4 * π ^ 2 * |δ| ≤ |s.im| := (le_max_right _ _).trans hτ
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hre0 : 0 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hre1 : (1 - s).re ≤ 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have him : |(1 - s).im| = |s.im| := by simp
  have h1 := opposite_sign_contour δ s hσ0 hσ1 ht hsign
  have h2 := same_sign_contour δ (1 - s) hre0 hre1 (by simpa only [him] using ht)
    (by simp only [Complex.sub_im, Complex.one_im, zero_sub]; nlinarith only [hsign])
  rw [him] at h2
  have hm := mainCoefficient_le s.re |s.im| δ hσ0 hσ1 hd ht htd
  have hl := lastCoefficient_le s.re |s.im| δ hσ1 hd ht htd
  have he := two_errors_le s.re (1 - s).re |s.im| δ hσ1 hre1 ht htd
  have hmain := mul_le_mul_of_nonneg_right hm
    (exp_nonneg (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|))
  have hlast := mul_le_mul_of_nonneg_right hl
    (exp_nonneg (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
      ((25 / 32 : ℝ) * |s.im|)))
  linarith only [h1, h2, he, hmain, hlast]

/-- The two sign cases of the reflected saddle expansion.
P0014 pages 27 and 28, displays 3.69 to 3.72 at k equal to zero.
CONDITIONAL ON the two open contour estimates of Theorem 3.1. -/
theorem pair_expansion (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      (1.025 * sqrt |s.im| * exp (-0.4798 * |s.im|) +
        (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|))⁻¹ *
          exp (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
            ((25 / 32 : ℝ) * |s.im|))) := by
  have ht : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  have him0 : s.im ≠ 0 := by intro h; norm_num [h] at ht
  rcases lt_or_gt_of_ne (mul_ne_zero hδ him0) with hsign | hsign
  · exact opposite_pair_expansion δ s hσ0 hσ1 hτ hsign
  · have h := opposite_pair_expansion δ (1 - s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simpa using hτ)
      (by simp only [Complex.sub_im, Complex.one_im, zero_sub]; nlinarith only [hsign])
    simpa only [sub_sub_cancel, Complex.sub_im, Complex.one_im, zero_sub,
      abs_neg, neg_div, neg_sq, add_comm (‖gaussianMellin δ (1 - s)‖)] using h

end LeanLab.HelfgottMajor.Decomp511a
