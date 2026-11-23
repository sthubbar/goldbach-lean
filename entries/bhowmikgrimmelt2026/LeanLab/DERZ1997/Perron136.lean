module

public import LeanLab.DERZ1997.Kernel136
public import LeanLab.Routes.Decomp1551a

/-!
Classical Perron kernel helpers for the P0011 page 101 decomposition.
Source: Davenport chapter 17, page 105.
These helpers prove the large-height and small-height estimates for every positive abscissa.
The original all-height kernel leaves retain their sealed statements.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.DERZ1997.Perron136
open Complex LeanLab.DERZ1997.Decomp1529b LeanLab.Routes.Decomp1551a

/-- Rescale any positive abscissa to 2 by a real change of variables.
Davenport chapter 17, page 105, the truncated Perron kernel. -/
theorem perron_rescale {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) :
    perronI y c T = perronI (y ^ (c / 2)) 2 (T / (c / 2)) := by
  let a : ℝ := c / 2
  let z : ℝ := y ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hy a
  have hpower (u : ℝ) :
      (y : ℂ) ^ ((c : ℂ) + ((a * u : ℝ) : ℂ) * I) =
        (z : ℂ) ^ ((2 : ℂ) + u * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne')]
    rw [← Complex.ofReal_log hy.le, ← Complex.ofReal_log hz.le]
    dsimp [z]
    rw [Real.log_rpow hy]
    push_cast
    congr 1
    dsimp [a]
    push_cast
    ring
  have hden (u : ℝ) : (c : ℂ) + ((a * u : ℝ) : ℂ) * I =
      (a : ℂ) * ((2 : ℂ) + u * I) := by
    dsimp [a]
    push_cast
    ring
  have hterm (u : ℝ) : (a : ℂ) *
      ((y : ℂ) ^ ((c : ℂ) + ((a * u : ℝ) : ℂ) * I) /
        ((c : ℂ) + ((a * u : ℝ) : ℂ) * I)) =
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I) := by
    rw [hpower, hden, ← mul_div_assoc]
    exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ha.ne')
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  have hs := intervalIntegral.smul_integral_comp_mul_left (a := -T / a) (b := T / a) f a
  have hl : a * (-T / a) = -T := by field_simp
  have hr : a * (T / a) = T := by field_simp
  rw [hl, hr] at hs
  have heq : (∫ u : ℝ in (-T / a)..(T / a),
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I)) =
      ∫ t : ℝ in (-T)..T, f t := by
    calc
      _ = ∫ u : ℝ in (-T / a)..(T / a), (a : ℂ) * f (a * u) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact (hterm u).symm
      _ = (a : ℂ) * ∫ u : ℝ in (-T / a)..(T / a), f (a * u) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [← Complex.real_smul]; exact hs
  unfold perronI
  change (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t) =
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ in (-(T / a))..(T / a),
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I)
  rw [← neg_div, heq]

/-- The classical Perron error bound, for every positive abscissa and height.
Davenport chapter 17, page 105. Reuses the proved lab estimate at abscissa 2. -/
theorem perron_remainder_bound {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronI y c T - (if 1 < y then 1 else 0)‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  have hscale : perronI y c T = pK (y ^ (c / 2)) (T / (c / 2)) := by
    rw [perron_rescale (T := T) hy hc]
    simp only [perronI, pK, Complex.ofReal_ofNat, Complex.ofReal_mul, one_div]
  let a : ℝ := c / 2
  let z : ℝ := y ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hy a
  have hlog : Real.log z = a * Real.log y := Real.log_rpow hy a
  have hbranch : (1 < z) ↔ (1 < y) := by
    rw [Real.one_lt_rpow_iff_of_pos hy]
    simp [ha, ha.not_gt]
  have hz1 : z ≠ 1 := by
    intro h
    have hh := congrArg Real.log h
    rw [hlog, Real.log_one] at hh
    exact (mul_ne_zero ha.ne' (Real.log_ne_zero_of_pos_of_ne_one hy hy1)) hh
  have h := perron_kernel_bound z hz hz1 (T / a) (div_pos hT ha)
  rw [hscale]
  have hpow : z ^ 2 = y ^ c := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    congr 1
    dsimp [a]
    ring
  simp only [hbranch, hpow, hlog, abs_mul, abs_of_pos ha] at h
  have hden : Real.pi * (T / a) * (a * |Real.log y|) = Real.pi * T * |Real.log y| := by
    field_simp
  rw [hden] at h
  exact h

/-- Both sides of the discontinuity occur in the permitted domain. -/
example :
    (‖perronI 2 1 1 - 1‖ ≤ (2 : ℝ) ^ (1 : ℝ) / (Real.pi * 1 * |Real.log 2|)) ∧
    (‖perronI (1 / 2) 1 1‖ ≤ (1 / 2 : ℝ) ^ (1 : ℝ) /
      (Real.pi * 1 * |Real.log (1 / 2)|)) := by
  constructor
  · simpa only [show (1 : ℝ) < 2 by norm_num, ite_true] using
      perron_remainder_bound (y := 2) (c := 1) (T := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · simpa only [show ¬(1 : ℝ) < 1 / 2 by norm_num, ite_false, sub_zero] using
      perron_remainder_bound (y := 1 / 2) (c := 1) (T := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Davenport chapter 17, page 105: the y greater than one leaf
on the region where T log y is at least one. -/
theorem perron_gt_one_large {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (hlarge : 1 ≤ T * Real.log y) :
    ‖perronI y c T - 1‖ ≤ y ^ c * min 1 (1 / (T * Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hd : 0 < T * Real.log y := mul_pos hT hlog
  have h := perron_remainder_bound (c := c) (T := T) hy0 (ne_of_gt hy) hc hT
  simp only [hy, ite_true, abs_of_pos hlog] at h
  refine h.trans ?_
  rw [min_eq_right ((div_le_one hd).mpr hlarge)]
  calc
    y ^ c / (Real.pi * T * Real.log y) = (y ^ c / (T * Real.log y)) / Real.pi := by ring
    _ ≤ y ^ c / (T * Real.log y) := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    _ = _ := by ring
/-- Davenport chapter 17, page 105: the y less than one leaf
on the region where T times the absolute log of y is at least one. -/
theorem perron_lt_one_large {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T)
    (hlarge : 1 ≤ T * |Real.log y|) :
    ‖perronI y c T‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  have hlog : 0 < |Real.log y| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy0 (ne_of_lt hy))
  have hd : 0 < T * |Real.log y| := mul_pos hT hlog
  have h := perron_remainder_bound (c := c) (T := T) hy0 (ne_of_lt hy) hc hT
  simp only [not_lt_of_ge hy.le, ite_false, sub_zero] at h
  refine h.trans ?_
  rw [min_eq_right ((div_le_one hd).mpr hlarge)]
  calc
    y ^ c / (Real.pi * T * |Real.log y|) = (y ^ c / (T * |Real.log y|)) / Real.pi := by ring
    _ ≤ y ^ c / (T * |Real.log y|) := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    _ = _ := by ring
/-- The large-height majorant alone exceeds the uniform target at a small height.
This is a limitation of that bound, not a counterexample to the Perron leaves. -/
theorem tail_majorant_exceeds_uniform : (2 : ℝ) ^ (1 : ℝ) <
    (2 : ℝ) ^ (1 : ℝ) / (Real.pi * (1 / 100) * |Real.log 2|) := by
  rw [Real.rpow_one]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  rw [abs_of_pos hlog, lt_div_iff₀ (by positivity)]
  have hprod : Real.pi * Real.log 2 < 4 :=
    (mul_lt_mul_of_pos_left hlog1 Real.pi_pos).trans (by simpa using Real.pi_lt_four)
  nlinarith

/-- The symmetric Perron integral has norm at most y to the power c when
T times the absolute log of y is at most one. Davenport chapter 17, page 105. -/
theorem perron_norm_small {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hsmall : T * |Real.log y| ≤ 1) : ‖perronI y c T‖ ≤ y ^ c := by
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  let A : ℝ → ℝ := fun t => (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) / (c ^ 2 + t ^ 2)
  let B : ℝ → ℝ := fun t => (c * Real.sin (t * Real.log y) - t * Real.cos (t * Real.log y)) / (c ^ 2 + t ^ 2)
  have hyp : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpow (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * I) =
      ((y ^ c : ℝ) : ℂ) * ((Real.cos (t * Real.log y) : ℂ) + (Real.sin (t * Real.log y) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hy.le]
    have he : ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.rpow_def_of_pos hy]
  have hre (t : ℝ) : (f t).re = y ^ c * A t := by
    dsimp [f, A]
    rw [hpow]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have him (t : ℝ) : (f t).im = y ^ c * B t := by
    dsimp [f, B]
    rw [hpow]
    simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have hodd (t : ℝ) : (f (-t)).im = -(f t).im := by
    rw [him, him]
    dsimp [B]
    simp only [neg_mul, Real.sin_neg, Real.cos_neg, neg_sq]
    ring
  have hi0 : (∫ t : ℝ in (-T)..T, (f t).im) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  have hn (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.div ?_ (by fun_prop) hn
    simp_rw [hpow]
    fun_prop
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
  have hJI : (∫ t in (-T)..T, f t).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, (f t).im := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = 0 := hi0
  have hpoint (t : ℝ) : |(f t).re| ≤ y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|) := by
    rw [hre, abs_mul, abs_of_pos hyp]
    apply mul_le_mul_of_nonneg_left _ hyp.le
    dsimp [A]
    rw [abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
    have hcos : |c * Real.cos (t * Real.log y)| ≤ c := by
      rw [abs_mul, abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hc.le).trans_eq (mul_one c)
    have hsin : |t * Real.sin (t * Real.log y)| ≤ t ^ 2 * |Real.log y| := by
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := t * Real.log y)) (abs_nonneg t)
      rw [abs_mul] at h
      nlinarith [sq_abs t]
    have htri := abs_add_le (c * Real.cos (t * Real.log y)) (t * Real.sin (t * Real.log y))
    have hcancel : c / (c ^ 2 + t ^ 2) * (c ^ 2 + t ^ 2) = c := div_mul_cancel₀ _ (hden t).ne'
    nlinarith [mul_nonneg (sq_nonneg c) (abs_nonneg (Real.log y))]
  have hquot : Continuous (fun t : ℝ => c / (c ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  have hg : Continuous (fun t : ℝ => y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|)) :=
    continuous_const.mul (hquot.add continuous_const)
  have hbound : |∫ t in (-T)..T, (f t).re| ≤
      ∫ t in (-T)..T, y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|) := by
    calc
      _ ≤ ∫ t in (-T)..T, |(f t).re| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => (f t).re) (by linarith : -T ≤ T)
      _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
        ((Complex.continuous_re.comp hcont).abs.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
        (fun t _ => hpoint t)
  have heval : (∫ t in (-T)..T, y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|)) =
      y ^ c * (2 * Real.arctan (T / c) + 2 * T * |Real.log y|) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hquot.intervalIntegrable _ _) intervalIntegrable_const,
      integral_div_sq_add_sq]
    simp only [neg_div, Real.arctan_neg, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heval] at hbound
  have hR : |∫ t in (-T)..T, (f t).re| ≤ y ^ c * (Real.pi + 2) := by
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hyp.le)
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  have hJ : (∫ t in (-T)..T, f t) = ((∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    · simpa only [Complex.ofReal_im] using hJI
  have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  unfold perronI
  change ‖(1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, f t‖ ≤ _
  rw [hJ, hfac, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (show 0 < (1 / (2 * Real.pi) : ℝ) by positivity)]
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  exact hR.trans (mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hyp.le)


/-- The y greater than one small-height error bound.
Davenport chapter 17, page 105. The kernel is real and nonnegative in this region. -/
theorem perron_gt_one_small {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (hsmall : T * Real.log y ≤ 1) : ‖perronI y c T - 1‖ ≤ y ^ c := by
  have hy0 : 0 < y := by linarith
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  let A : ℝ → ℝ := fun t => (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) / (c ^ 2 + t ^ 2)
  let B : ℝ → ℝ := fun t => (c * Real.sin (t * Real.log y) - t * Real.cos (t * Real.log y)) / (c ^ 2 + t ^ 2)
  have hyp : 0 < y ^ c := Real.rpow_pos_of_pos hy0 c
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpow (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * I) =
      ((y ^ c : ℝ) : ℂ) * ((Real.cos (t * Real.log y) : ℂ) + (Real.sin (t * Real.log y) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy0.ne'), ← Complex.ofReal_log hy0.le]
    have he : ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.rpow_def_of_pos hy0]
  have hre (t : ℝ) : (f t).re = y ^ c * A t := by
    dsimp [f, A]
    rw [hpow]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have him (t : ℝ) : (f t).im = y ^ c * B t := by
    dsimp [f, B]
    rw [hpow]
    simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have hodd (t : ℝ) : (f (-t)).im = -(f t).im := by
    rw [him, him]
    dsimp [B]
    simp only [neg_mul, Real.sin_neg, Real.cos_neg, neg_sq]
    ring
  have hi0 : (∫ t : ℝ in (-T)..T, (f t).im) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  have hn (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.div ?_ (by fun_prop) hn
    simp_rw [hpow]
    fun_prop
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
  have hJI : (∫ t in (-T)..T, f t).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, (f t).im := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = 0 := hi0
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hnonneg : 0 ≤ ∫ t in (-T)..T, (f t).re := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have hat : |t| ≤ T := abs_le.mpr ht
    have hphase : |t * Real.log y| ≤ 1 := by
      rw [abs_mul, abs_of_pos hlog]
      exact (mul_le_mul_of_nonneg_right hat hlog.le).trans hsmall
    have hcos : 0 ≤ Real.cos (t * Real.log y) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp hphase).1, Real.pi_gt_three],
        by linarith [(abs_le.mp hphase).2, Real.pi_gt_three]⟩
    have hsin : 0 ≤ t * Real.sin (t * Real.log y) := by
      rcases le_or_gt 0 t with ht0 | ht0
      · exact mul_nonneg ht0 (Real.sin_nonneg_of_nonneg_of_le_pi
          (mul_nonneg ht0 hlog.le) (by linarith [(abs_le.mp hphase).2, Real.pi_gt_three]))
      · exact mul_nonneg_of_nonpos_of_nonpos ht0.le
          (Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (mul_nonpos_of_nonpos_of_nonneg ht0.le hlog.le)
            (by linarith [(abs_le.mp hphase).1, Real.pi_gt_three]))
    rw [hre]
    apply mul_nonneg hyp.le
    dsimp [A]
    exact div_nonneg (add_nonneg (mul_nonneg hc.le hcos) hsin) (hden t).le
  have hJ : (∫ t in (-T)..T, f t) = ((∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    · simpa only [Complex.ofReal_im] using hJI
  have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  have hval : perronI y c T = (((1 / (2 * Real.pi)) * ∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    unfold perronI
    change (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t) = _
    rw [hJ, hfac, Complex.ofReal_mul]
  let R : ℝ := (1 / (2 * Real.pi)) * ∫ t in (-T)..T, (f t).re
  have hR0 : 0 ≤ R := mul_nonneg (by positivity) hnonneg
  have hnorm := perron_norm_small hy0 hc hT (by simpa only [abs_of_pos hlog] using hsmall)
  have hR : R ≤ y ^ c := by
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0] at hnorm
    exact hnorm
  have hy1 : 1 ≤ y ^ c := Real.one_le_rpow hy.le hc.le
  have hdiff : perronI y c T - 1 = ((R - 1 : ℝ) : ℂ) := by
    rw [hval]
    dsimp [R]
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The positive coefficients for termwise integration are summable for c greater than one.
Davenport chapter 17, page 105. Mathlib supplies absolute convergence of the von Mangoldt series. -/
theorem perron_coeff_summable {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (x / n) ^ c) := by
  have hf := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc)
  rw [LSeriesSummable, ← summable_norm_iff] at hf
  have hg := hf.mul_left (x ^ c)
  convert hg using 1
  funext n
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [Nat.ne_of_gt hn, ite_false, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.ofReal_re, Real.div_rpow hx.le (Nat.cast_nonneg n)]
    ring

end LeanLab.DERZ1997.Perron136
