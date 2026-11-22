module

public import LeanLab.KadiriLumley2014.Weight

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 pages 4 and 5 equations 2.17 and 2.22 to 2.25.
Elementary complex exponential and smoothing transform bounds.
AI wrote this Lean code, Codex by OpenAI, 2026-10-26.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- Page 5 equation 2.22. The exponential quotient is its integral from zero to u. -/
theorem exp_quotient_integral {s : ℂ} (hs : s ≠ 0) (u : ℝ) :
    (Complex.exp (s * u) - 1) / s = ∫ v in (0 : ℝ)..u, Complex.exp (s * v) := by
  simpa using (integral_exp_mul_complex (a := 0) (b := u) hs).symm

/-- Page 5 equation 2.22. The norm of the exponential quotient is bounded
by the integral of its real exponential envelope. -/
theorem exp_quotient_norm_integral {s : ℂ} (hs : s ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    ‖(Complex.exp (s * u) - 1) / s‖ ≤ ∫ v in (0 : ℝ)..u, Real.exp (s.re * v) := by
  rw [exp_quotient_integral hs]
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun v : ℝ => Complex.exp (s * v)) hu
  simpa [Complex.norm_exp, Complex.mul_re] using h

/-- Page 5 equation 2.23. The imaginary part bounds the complex denominator. -/
theorem exp_quotient_norm_im {s : ℂ} {u : ℝ} (hτ : 0 < s.im) :
    ‖(Complex.exp (s * u) - 1) / s‖ ≤ (Real.exp (u * s.re) + 1) / s.im := by
  rw [norm_div]
  have hn : s.im ≤ ‖s‖ := (le_abs_self s.im).trans (Complex.abs_im_le_norm s)
  have hnum : ‖Complex.exp (s * u) - 1‖ ≤ Real.exp (u * s.re) + 1 := by
    have h := norm_sub_le (Complex.exp (s * u)) 1
    simpa [Complex.norm_exp, Complex.mul_re, mul_comm] using h
  exact div_le_div₀ (by positivity) hnum hτ hn


/-- Page 5 equation 2.22, for a positive real part. -/
theorem exp_quotient_norm_re {s : ℂ} {u : ℝ} (hσ : 0 < s.re) (hu : 0 ≤ u) :
    ‖(Complex.exp (s * u) - 1) / s‖ ≤ (Real.exp (u * s.re) - 1) / s.re := by
  have hs : s ≠ 0 := by intro hz; simp [hz] at hσ
  have h := exp_quotient_norm_integral hs hu
  rw [intervalIntegral.integral_comp_mul_left Real.exp hσ.ne', integral_exp] at h
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h


/-- The normalized weight integral in page 4 equation 2.17. -/
noncomputable def weightTransform (m : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)) /
    ((∫ t in (0 : ℝ)..1, weight m t : ℝ) : ℂ)

/-- The smoothing transform G of page 4 equation 2.17. -/
noncomputable def smoothingG (m : ℕ) (δ u : ℝ) (s : ℂ) : ℂ :=
  ((Complex.exp (s * u) - 1) / s) / ((Real.exp u - 1 : ℝ) : ℂ) * weightTransform m δ s

/-- Page 9 before Theorem 2.7, the weight factor at one is F0. -/
theorem weightTransform_one (m : ℕ) (δ : ℝ) :
    weightTransform m δ 1 = ((1 + δ / 2 : ℝ) : ℂ) := by
  unfold weightTransform
  have heq : (fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (1 : ℂ) * (weight m t : ℂ)) =
      (fun t => (((1 + δ * t) * weight m t : ℝ) : ℂ)) := by
    funext t
    simp
  rw [heq, intervalIntegral.integral_ofReal, ← Complex.ofReal_div, weight_F0_exact]

/-- Page 5 equation 2.24 at k = 0, normalized by the positive mass. -/
theorem weightTransform_norm_le (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ}
    (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖weightTransform m δ s‖ ≤ 1 + δ / 2 := by
  let F := fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)
  have hFc : Continuous F := by
    apply Continuous.mul
    · exact (Complex.continuous_ofReal_cpow_const hσ).comp (by fun_prop)
    · exact Complex.continuous_ofReal.comp (weight_continuous m)
  have hbound : (∫ t in (0 : ℝ)..1, ‖F t‖) ≤
      ∫ t in (0 : ℝ)..1, (1 + δ * t) * weight m t := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hFc.norm.intervalIntegrable _ _)
      ((by unfold weight; fun_prop : Continuous (fun t => (1 + δ * t) * weight m t)).intervalIntegrable _ _)
    intro t ht
    have hb : 1 ≤ 1 + δ * t := by nlinarith [ht.1]
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + δ * t),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg m ht)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hb hσ1) (weight_nonneg m ht)
  have hn := (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := F) (by norm_num : (0 : ℝ) ≤ 1)).trans hbound
  unfold weightTransform
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_mass_pos m)]
  exact ((div_le_div_iff_of_pos_right (weight_mass_pos m)).mpr hn).trans_eq
    (weight_F0_exact m δ)

/-- Page 9 before Theorem 2.7. G at one is exactly F0 for nonzero u. -/
theorem smoothingG_one (m : ℕ) (δ : ℝ) {u : ℝ} (hu : u ≠ 0) :
    smoothingG m δ u 1 = ((1 + δ / 2 : ℝ) : ℂ) := by
  have he : Real.exp u - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hu)
  unfold smoothingG
  rw [weightTransform_one]
  have heC : (Real.exp u : ℂ) - 1 ≠ 0 := by exact_mod_cast he
  simp [← Complex.ofReal_exp, Complex.ofReal_sub, heC]

/-- Page 5 equation 2.25 for the polynomial weight and positive real part. -/
theorem smoothingG_norm_re (m : ℕ) {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖smoothingG m δ u s‖ ≤
      (1 + δ / 2) * (Real.exp (u * s.re) - 1) / ((Real.exp u - 1) * s.re) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hq := exp_quotient_norm_re hσ hu.le
  have hw := weightTransform_norm_le m hδ hσ hσ1
  unfold smoothingG
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hdiv := (div_le_div_iff_of_pos_right he).mpr hq
  have hnum : 0 ≤ Real.exp (u * s.re) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hu.le hσ.le)
    linarith
  have hmul := mul_le_mul hdiv hw (norm_nonneg _)
    (div_nonneg (div_nonneg hnum hσ.le) he.le)
  refine hmul.trans_eq ?_
  field_simp


/-- Page 8 equation 2.52. The critical-line exponential factor simplifies exactly. -/
theorem critical_exp_ratio {u : ℝ} (hu : 0 < u) :
    (Real.exp (u * (1 / 2)) - 1) / ((Real.exp u - 1) * (1 / 2)) =
      2 / (Real.exp (u / 2) + 1) := by
  have hE : 1 < Real.exp (u / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  have hs : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hs]
  have he : Real.exp (u / 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp : Real.exp (u / 2) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith [hs]

/-- Page 8 equation 2.52, the single-zero bound behind Sigma02. -/
theorem smoothingG_norm_half (m : ℕ) {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u)
    {s : ℂ} (hσ : s.re = 1 / 2) :
    ‖smoothingG m δ u s‖ ≤ 2 * (1 + δ / 2) / (Real.exp (u / 2) + 1) := by
  have h := smoothingG_norm_re m hδ hu (s := s) (by rw [hσ]; norm_num) (by rw [hσ]; norm_num)
  rw [hσ] at h
  calc
    _ ≤ (1 + δ / 2) * (Real.exp (u * (1 / 2)) - 1) / ((Real.exp u - 1) * (1 / 2)) := h
    _ = (1 + δ / 2) * ((Real.exp (u * (1 / 2)) - 1) / ((Real.exp u - 1) * (1 / 2))) := by ring
    _ = _ := by rw [critical_exp_ratio hu]; ring

/-- Page 8 equation 2.52. Pairing the two ordinates gives the coefficient
four times F0 divided by exp of u/2 plus one. -/
theorem smoothingG_pair_half (m : ℕ) {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u)
    {s : ℂ} (hσ : s.re = 1 / 2) :
    ‖smoothingG m δ u s‖ + ‖smoothingG m δ u (star s)‖ ≤
      4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) := by
  have h := smoothingG_norm_half m hδ hu hσ
  have h' := smoothingG_norm_half m hδ hu (s := star s) (by simpa using hσ)
  calc
    _ ≤ 2 * (1 + δ / 2) / (Real.exp (u / 2) + 1) +
        2 * (1 + δ / 2) / (Real.exp (u / 2) + 1) := add_le_add h h'
    _ = _ := by ring

/-- The real-part-zero endpoint of the exponential envelope in equation 2.22. -/
theorem exp_quotient_norm_zero {s : ℂ} (hs : s ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (hσ : s.re = 0) : ‖(Complex.exp (s * u) - 1) / s‖ ≤ u := by
  simpa [hσ] using exp_quotient_norm_integral hs hu

end LeanLab.KadiriLumley2014.Task92
