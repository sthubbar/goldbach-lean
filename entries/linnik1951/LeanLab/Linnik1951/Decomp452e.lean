module

public import Mathlib

/-!
Original page 158 equations 4.5 and 4.6.
Keep the full denominator in the primitive of the radial complex power.
These bounds support a signed kernel repair.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open MeasureTheory

/-- The radial primitive bound retains the real part of its denominator. -/
theorem radial_cpow_integral_bound452 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (r : ℂ) (hr : r.re < -1) :
    ‖∫ u : ℝ in a..b, (u : ℂ) ^ r‖ ≤
      (a ^ (r.re + 1) + b ^ (r.re + 1)) / ‖r + 1‖ := by
  have hrne : r ≠ -1 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.mem_uIcc]
    rintro (h | h) <;> linarith [h.1, h.2]
  rw [integral_cpow (Or.inr ⟨hrne, hzero⟩), norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖(b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)‖ ≤
        ‖(b : ℂ) ^ (r + 1)‖ + ‖(a : ℂ) ^ (r + 1)‖ := norm_sub_le _ _
    _ = _ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_cpow_eq_rpow_re_of_pos ha]
      simp only [Complex.add_re, Complex.one_re]
      ring

/-- The Mellin radial exponent gives the Euclidean denominator of epsilon and frequency difference. -/
theorem radial_mellin_integral_bound452 (a b ε d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) :
    ‖∫ u : ℝ in a..b, (u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      (a ^ (-ε) + b ^ (-ε)) / Real.sqrt (ε ^ 2 + d ^ 2) := by
  have h := radial_cpow_integral_bound452 a b ha hb
    (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I) (by simp; linarith)
  have hre : (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I).re + 1 = -ε := by
    simp
  have hn : ‖(-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I) + 1‖ =
      Real.sqrt (ε ^ 2 + d ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rwa [hre, hn] at h

/-- Away from the diagonal, the frequency difference alone bounds the radial denominator. -/
theorem radial_mellin_off_diagonal452 (a b ε d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hε : 0 < ε) (hd : d ≠ 0) :
    ‖∫ u : ℝ in a..b, (u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      2 * a ^ (-ε) / |d| := by
  have hb : 0 < b := ha.trans_le hab
  have h := radial_mellin_integral_bound452 a b ε d ha hb hε
  have hp : b ^ (-ε) ≤ a ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  have hden : |d| ≤ Real.sqrt (ε ^ 2 + d ^ 2) := by
    calc |d| = Real.sqrt (d ^ 2) := (Real.sqrt_sq_eq_abs d).symm
         _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have hdpos : 0 < |d| := abs_pos.mpr hd
  calc
    _ ≤ (a ^ (-ε) + b ^ (-ε)) / Real.sqrt (ε ^ 2 + d ^ 2) := h
    _ ≤ (a ^ (-ε) + b ^ (-ε)) / |d| :=
      div_le_div_of_nonneg_left (by positivity) hdpos hden
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hdpos.le

/-- A diagonal bound for the radial integral follows from the integral of one over u. -/
theorem radial_mellin_log_bound452 (a b ε d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hε : 0 < ε) :
    ‖∫ u : ℝ in a..b, (u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      a ^ (-ε) * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hg : ContinuousOn (fun u : ℝ => a ^ (-ε) * (1 / u)) (Set.uIcc a b) := by
    apply continuousOn_const.mul
    apply continuousOn_const.div continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact ne_of_gt (ha.trans_le hu.1)
  have hnorm : ∀ u ∈ Set.Ioc a b,
      ‖(u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤ a ^ (-ε) * (1 / u) := by
    intro u hu
    have hup : 0 < u := ha.trans hu.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hup]
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
    have heq : u ^ (-(1 + ε)) = u ^ (-ε) * (1 / u) := by
      rw [show -(1 + ε) = -ε + (-1 : ℝ) by ring, Real.rpow_add hup,
        Real.rpow_neg_one, one_div]
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos ha hu.1.le (by linarith)) (by positivity)
  calc
    _ ≤ ∫ u : ℝ in a..b, a ^ (-ε) * (1 / u) :=
      intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ hnorm) hg.intervalIntegrable
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha hb]

/-- A uniform radial estimate includes a logarithmic factor near equal Mellin frequencies. -/
theorem radial_mellin_uniform_bound452 (a b ε d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hε : 0 < ε) :
    ‖∫ u : ℝ in a..b, (u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      4 * a ^ (-ε) * (1 + Real.log (b / a)) / (1 + |d|) := by
  have hA : 0 < a ^ (-ε) := Real.rpow_pos_of_pos ha _
  have hL : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  have hden : 0 < 1 + |d| := by positivity
  by_cases hd : |d| ≤ 1
  · have h := radial_mellin_log_bound452 a b ε d ha hab hε
    apply (le_div_iff₀ hden).mpr
    have h1 := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1 + |d|)
    have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + |d| ≤ 2)
      (mul_nonneg hA.le hL)
    nlinarith
  · have hd1 : 1 ≤ |d| := le_of_lt (lt_of_not_ge hd)
    have hdpos : 0 < |d| := by linarith
    have hdne : d ≠ 0 := abs_pos.mp hdpos
    have h := radial_mellin_off_diagonal452 a b ε d ha hab hε hdne
    refine h.trans ?_
    rw [div_le_div_iff₀ hdpos hden]
    have h1 := mul_le_mul_of_nonneg_left (by linarith : 1 + |d| ≤ 2 * |d|)
      (by positivity : 0 ≤ 2 * a ^ (-ε))
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith : (1 : ℝ) ≤ 1 + Real.log (b / a))
      (by positivity : 0 ≤ 4 * a ^ (-ε) * |d|)
    nlinarith

end LeanLab.Linnik1951
