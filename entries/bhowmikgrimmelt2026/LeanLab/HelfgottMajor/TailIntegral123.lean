module

public import Mathlib

/-!
Route burst 2026-11-12, session 9. P0014 Lemma 4.5, pages 40 to 42, displays 4.35 to 4.41.
The two improper tail integrals of Lemma 4.5 and their proved bounds, displays 4.36 and 4.41.
This file depends on Mathlib only, so SplitGaussian123 can import it without an import cycle.
The definitions and proofs are copied verbatim from Decomp269c.lean lines 13 to 913, where they
are already PROVED; Decomp269c cannot be imported here because it imports Decomp123, which
imports SplitGaussian123. The source display 4.34 gives the factor 4.226 used downstream.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.TailIntegral123
open Real MeasureTheory Filter

/-- The density in the zero count integral of display 4.35 on page 41. -/
noncomputable def countDensity (q t : ℝ) : ℝ :=
  1 / (2 * π) * log (q * t / (2 * π)) + 1 / (4 * t)

/-- The exponential integral estimated in display 4.36 on page 41. -/
noncomputable def expTailIntegral (q T : ℝ) : ℝ :=
  ∫ t in Set.Ioi T, exp (-0.1598 * t) * countDensity q t

/-- The Gaussian integral of display 4.40 on page 42. Its branch is absent at zero shift. -/
noncomputable def gaussianTailIntegral (q δ T : ℝ) : ℝ :=
  if δ = 0 then 0 else
    ∫ t in Set.Ioi T, exp (-0.1065 * (t / (π * |δ|)) ^ 2) * countDensity q t

open MeasureTheory Filter

/-! ## Elementary improper integrals -/

section Elementary

variable (lam T : ℝ)

/-- Antiderivative of `t ↦ exp (-lam (t-T))`. -/
private theorem hasDerivAt_exp_shift (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (Real.exp (-lam * (t - T))) t := by
  have hid : HasDerivAt (fun t : ℝ => t - T) 1 t := (hasDerivAt_id t).sub_const T
  have h1 : HasDerivAt (fun t : ℝ => -lam * (t - T)) (-lam) t := by
    simpa using hid.const_mul (-lam)
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-lam * (t - T)))
      (Real.exp (-lam * (t - T)) * (-lam)) t := h1.exp
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (-lam * (t - T)) / lam)
      (Real.exp (-lam * (t - T)) * (-lam) / lam) t := h2.div_const lam
  have h4 : HasDerivAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (-(Real.exp (-lam * (t - T)) * (-lam) / lam)) t := h3.neg
  have h5 : (-(Real.exp (-lam * (t - T)) * (-lam) / lam)) = Real.exp (-lam * (t - T)) := by
    field_simp
  rw [h5] at h4
  exact h4

private theorem continuous_exp_shift :
    Continuous (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam)) := by fun_prop

private theorem tendsto_exp_shift (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam)) atTop (nhds 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 lam hlam
    simpa using h
  have heq : (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      = fun t : ℝ => -(Real.exp (lam * T) / lam) * Real.exp (-lam * t) := by
    funext t
    rw [show -lam * (t - T) = -lam * t + lam * T by ring, Real.exp_add]
    ring
  rw [heq]
  simpa using h0.const_mul (-(Real.exp (lam * T) / lam))

/-- `∫_T^∞ exp (-lam (t-T)) dt = 1/lam` for `lam > 0`. -/
private theorem integral_Ioi_exp_neg_mul_sub (hlam : 0 < lam) :
    ∫ t in Set.Ioi T, Real.exp (-lam * (t - T)) = 1 / lam := by
  have hcont : ContinuousWithinAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (Set.Ici T) T := (continuous_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ Real.exp (-lam * (t - T)) := fun t _ =>
    (Real.exp_pos _).le
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (a := T)
    (g := fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
    (g' := fun t : ℝ => Real.exp (-lam * (t - T))) (l := 0) hcont
    (fun t _ => hasDerivAt_exp_shift lam T hlam.ne' t) hpos (tendsto_exp_shift lam T hlam)
  rw [h]
  simp

private theorem integrableOn_exp_neg_mul_sub (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * (t - T))) (Set.Ioi T) := by
  have hcont : ContinuousWithinAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (Set.Ici T) T := (continuous_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ Real.exp (-lam * (t - T)) := fun t _ =>
    (Real.exp_pos _).le
  exact integrableOn_Ioi_deriv_of_nonneg hcont (fun t _ => hasDerivAt_exp_shift lam T hlam.ne' t) hpos
    (tendsto_exp_shift lam T hlam)

/-- Antiderivative of `t ↦ (t-T) * exp (-lam (t-T))`. -/
private theorem hasDerivAt_sub_exp_shift (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
      ((t - T) * Real.exp (-lam * (t - T))) t := by
  have hs : HasDerivAt (fun t : ℝ => t - T) 1 t := (hasDerivAt_id t).sub_const T
  have harg : HasDerivAt (fun t : ℝ => -lam * (t - T)) (-lam) t := by
    simpa using hs.const_mul (-lam)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-lam * (t - T)))
      (Real.exp (-lam * (t - T)) * (-lam)) t := harg.exp
  have hP : HasDerivAt (fun t : ℝ => (t - T) / lam + 1 / lam ^ 2) (1 / lam) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t - T) / lam) (1 / lam) t := by
      simpa using hs.div_const lam
    simpa using h1.add_const (1 / lam ^ 2)
  have hprod := hexp.mul hP
  have hneg := hprod.neg
  have hval : (-(Real.exp (-lam * (t - T)) * (-lam) * ((t - T) / lam + 1 / lam ^ 2) +
      Real.exp (-lam * (t - T)) * (1 / lam))) = (t - T) * Real.exp (-lam * (t - T)) := by
    field_simp
    ring
  rw [hval] at hneg
  exact hneg

private theorem continuous_sub_exp_shift :
    Continuous (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2))) := by
  fun_prop

private theorem tendsto_sub_exp_shift (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
      atTop (nhds 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 lam hlam
    simpa using h
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-lam * t)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 lam hlam
    simpa using h
  have heq : (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
      = fun t : ℝ => (-(Real.exp (lam * T) / lam)) * (t * Real.exp (-lam * t)) +
          (-(Real.exp (lam * T) * (1 / lam ^ 2 - T / lam))) * Real.exp (-lam * t) := by
    funext t
    rw [show -lam * (t - T) = -lam * t + lam * T by ring, Real.exp_add]
    ring
  rw [heq]
  have hsum := (h1.const_mul (-(Real.exp (lam * T) / lam))).add
    (h0.const_mul (-(Real.exp (lam * T) * (1 / lam ^ 2 - T / lam))))
  simpa using hsum

/-- `∫_T^∞ (t-T) exp (-lam (t-T)) dt = 1/lam^2` for `lam > 0`. -/
private theorem integral_Ioi_sub_exp_neg_mul_sub (hlam : 0 < lam) :
    ∫ t in Set.Ioi T, (t - T) * Real.exp (-lam * (t - T)) = 1 / lam ^ 2 := by
  have hcont : ContinuousWithinAt
      (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2))) (Set.Ici T) T :=
    (continuous_sub_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ (t - T) * Real.exp (-lam * (t - T)) := by
    intro t ht
    have htT : 0 ≤ t - T := by have h : T < t := ht; linarith
    exact mul_nonneg htT (Real.exp_pos _).le
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (a := T)
    (g := fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
    (g' := fun t : ℝ => (t - T) * Real.exp (-lam * (t - T))) (l := 0) hcont
    (fun t _ => hasDerivAt_sub_exp_shift lam T hlam.ne' t) hpos (tendsto_sub_exp_shift lam T hlam)
  rw [h]
  simp

private theorem integrableOn_sub_exp_neg_mul_sub (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => (t - T) * Real.exp (-lam * (t - T))) (Set.Ioi T) := by
  have hcont : ContinuousWithinAt
      (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2))) (Set.Ici T) T :=
    (continuous_sub_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ (t - T) * Real.exp (-lam * (t - T)) := by
    intro t ht
    have htT : 0 ≤ t - T := by have h : T < t := ht; linarith
    exact mul_nonneg htT (Real.exp_pos _).le
  exact integrableOn_Ioi_deriv_of_nonneg hcont (fun t _ => hasDerivAt_sub_exp_shift lam T hlam.ne' t) hpos
    (tendsto_sub_exp_shift lam T hlam)

end Elementary

/-! ## Pointwise bound for the zero density -/

/-- For `t > T ≥ 100` the zero density is at most its linearised envelope at `T`. -/
private theorem countDensity_le_linear (q : ℕ) [NeZero q] (T t : ℝ) (hT : 100 ≤ T) (ht : T < t) :
    countDensity q t ≤
      (1 / (2 * π)) * log ((q : ℝ) * T / (2 * π)) + (1 / (2 * π)) / T * (t - T) + 1 / (4 * T) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hA : (0 : ℝ) < (q : ℝ) * T / (2 * π) := by positivity
  have hB : (0 : ℝ) < t / T := by positivity
  have hmul : (q : ℝ) * T / (2 * π) * (t / T) = (q : ℝ) * t / (2 * π) := by
    field_simp
    try ring
  have hlog : log ((q : ℝ) * t / (2 * π)) ≤ log ((q : ℝ) * T / (2 * π)) + (t - T) / T := by
    rw [← hmul, Real.log_mul hA.ne' hB.ne']
    have h1 := Real.log_le_sub_one_of_pos hB
    have h2 : t / T - 1 = (t - T) / T := by
      field_simp
      try ring
    linarith
  have hpi : (0 : ℝ) < 1 / (2 * π) := by positivity
  have hinv : 1 / (4 * t) ≤ 1 / (4 * T) := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * T)
    linarith
  have hmain := mul_le_mul_of_nonneg_left hlog hpi.le
  have hD : 1 / (2 * π) * ((t - T) / T) = (1 / (2 * π)) / T * (t - T) := by
    field_simp
    try ring
  unfold countDensity
  linarith

/-- The density is nonnegative past `T ≥ 100`. -/
private theorem countDensity_nonneg (q : ℕ) [NeZero q] (T t : ℝ) (hT : 100 ≤ T) (ht : T < t) :
    0 ≤ countDensity q t := by
  have ht0 : 0 < t := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := NeZero.pos q
    exact_mod_cast this
  have harg : (1 : ℝ) ≤ (q : ℝ) * t / (2 * π) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [Real.pi_lt_four]
  have hlog : 0 ≤ log ((q : ℝ) * t / (2 * π)) := Real.log_nonneg harg
  have hpi : (0 : ℝ) < 1 / (2 * π) := by positivity
  unfold countDensity
  have h2 : (0 : ℝ) < 1 / (4 * t) := by positivity
  have := mul_nonneg hpi.le hlog
  linarith

/-! ## The arithmetic core of display 4.36 -/

private theorem expTail_arithmetic (L T : ℝ) (hL : 2.7672 ≤ L) (hT : 100 ≤ T) :
    (1 / (2 * π)) * L / 0.1598 + ((1 / (2 * π)) / T) / 0.1598 ^ 2 +
        (1 / (4 * T)) / 0.1598 ≤ 1.0242 * L := by
  have hT0 : 0 < T := by linarith
  have hLpos : 0 < L := by linarith
  have hpi1 : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hcoef : 1 / (2 * π) ≤ 1 / (2 * 3.141592) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hTinv : 1 / T ≤ 1 / 100 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have h1 : (1 / (2 * π)) * L / 0.1598 ≤ (1 / (2 * 3.141592)) * L / 0.1598 := by
    apply div_le_div_of_nonneg_right ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_right hcoef hLpos.le
  have h2 : ((1 / (2 * π)) / T) / 0.1598 ^ 2 ≤ ((1 / (2 * 3.141592)) / 100) / 0.1598 ^ 2 := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have hm := mul_le_mul hcoef hTinv (by positivity) (by positivity)
    simpa [div_eq_mul_inv] using hm
  have h3 : (1 / (4 * T)) / 0.1598 ≤ (1 / (4 * 100)) / 0.1598 := by
    apply div_le_div_of_nonneg_right ?_ (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hTinv (by norm_num : (0:ℝ) ≤ 1/4)
    have e1 : 1 / (4 * T) = (1/4) * (1/T) := by field_simp
    have e2 : 1 / (4 * (100:ℝ)) = (1/4) * (1/100) := by field_simp
    rw [e1, e2]
    exact hm
  have hc1 : (1 / (2 * (3.141592:ℝ))) / 0.1598 ≤ (0.9959636:ℝ) := by norm_num
  have hc0 : (1 / (2 * (3.141592:ℝ))) / 100 / 0.1598 ^ 2 + (1 / (4 * 100)) / 0.1598
      ≤ (0.0779702:ℝ) := by norm_num
  have hm : (1 / (2 * (3.141592:ℝ))) * L / 0.1598 ≤ (0.9959636:ℝ) * L := by
    rw [show (1 / (2 * (3.141592:ℝ))) * L / 0.1598 =
      ((1 / (2 * (3.141592:ℝ))) / 0.1598) * L by ring]
    exact mul_le_mul_of_nonneg_right hc1 hLpos.le
  have hfinal : (1 / (2 * 3.141592)) * L / 0.1598 + ((1 / (2 * 3.141592)) / 100) / 0.1598 ^ 2 +
      (1 / (4 * 100)) / 0.1598 ≤ 1.0242 * L := by
    linarith
  linarith

/-! ## The lower bound for `log (q T / 2π)` -/

private theorem log_qt_lower (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    (2.7672 : ℝ) ≤ log ((q : ℝ) * T / (2 * π)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := NeZero.pos q
    exact_mod_cast this
  have hT0 : 0 < T := by linarith
  have hpos100 : (0 : ℝ) < 100 / (2 * π) := by positivity
  have hmono : 100 / (2 * π) ≤ (q : ℝ) * T / (2 * π) := by
    apply div_le_div_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ 2 * π)
    nlinarith
  have hle := Real.log_le_log hpos100 hmono
  have e1 : (100 : ℝ) / (2 * π) = 16 * (25 / (8 * π)) := by
    field_simp
    ring
  have h16 : (0 : ℝ) < 16 := by norm_num
  have h25 : (0 : ℝ) < 25 / (8 * π) := by positivity
  have l1 : Real.log ((100 : ℝ) / (2 * π)) = Real.log 16 + Real.log (25 / (8 * π)) := by
    rw [e1, Real.log_mul h16.ne' h25.ne']
  have l16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have l25 : Real.log ((25 : ℝ) / (8 * π)) = -Real.log (8 * π / 25) := by
    rw [show (25 : ℝ) / (8 * π) = (8 * π / 25)⁻¹ by field_simp]
    exact Real.log_inv _
  have h8pi : (0 : ℝ) < 8 * π / 25 := by positivity
  have h8pile : Real.log (8 * π / 25) ≤ 8 * π / 25 - 1 := Real.log_le_sub_one_of_pos h8pi
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpi : π ≤ (3.141593 : ℝ) := le_of_lt Real.pi_lt_d6
  have hconst : (2.7672 : ℝ) ≤ 4 * 0.6931471803 + 1 - 8 * (3.141593 : ℝ) / 25 := by
    norm_num
  linarith

/-! ## The exponential tail integral, display 4.36 -/

private theorem exp_integral_bound_aux (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    expTailIntegral q T ≤
      1.0242 * log ((q : ℝ) * T / (2 * π)) * Real.exp (-0.1598 * T) := by
  classical
  have hT0 : 0 < T := by linarith
  have ha : (0 : ℝ) < 0.1598 := by norm_num
  set L : ℝ := log ((q : ℝ) * T / (2 * π)) with hL
  set F : ℝ → ℝ := fun t => ((1 / (2 * π)) * L + 1 / (4 * T)) * Real.exp (-0.1598 * (t - T))
    with hF
  set H : ℝ → ℝ := fun t => ((1 / (2 * π)) / T) * ((t - T) * Real.exp (-0.1598 * (t - T)))
    with hH
  set G : ℝ → ℝ := fun t => Real.exp (-0.1598 * T) * (F t + H t) with hG
  have hbase1 : IntegrableOn (fun t => Real.exp (-0.1598 * (t - T))) (Set.Ioi T) :=
    integrableOn_exp_neg_mul_sub 0.1598 T ha
  have hbase2 : IntegrableOn (fun t => (t - T) * Real.exp (-0.1598 * (t - T))) (Set.Ioi T) :=
    integrableOn_sub_exp_neg_mul_sub 0.1598 T ha
  have hiF : IntegrableOn F (Set.Ioi T) := by
    rw [hF]
    exact hbase1.const_mul ((1 / (2 * π)) * L + 1 / (4 * T))
  have hiH : IntegrableOn H (Set.Ioi T) := by
    rw [hH]
    exact hbase2.const_mul ((1 / (2 * π)) / T)
  have hGint : IntegrableOn G (Set.Ioi T) := by
    rw [hG]
    exact (hiF.add hiH).const_mul (Real.exp (-0.1598 * T))
  have hGval : ∫ t in Set.Ioi T, G t = Real.exp (-0.1598 * T) *
      (((1 / (2 * π)) * L + 1 / (4 * T)) * (1 / 0.1598) +
        ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2)) := by
    rw [hG, integral_const_mul]
    congr 1
    rw [integral_add hiF hiH, hF, hH]
    rw [integral_const_mul, integral_const_mul]
    rw [integral_Ioi_exp_neg_mul_sub 0.1598 T ha,
      integral_Ioi_sub_exp_neg_mul_sub 0.1598 T ha]
  have hf_nonneg : ((0 : ℝ → ℝ)) ≤ᵐ[volume.restrict (Set.Ioi T)]
      (fun t => Real.exp (-0.1598 * t) * countDensity q t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (countDensity_nonneg q T t hT ht)
  have hle : (fun t => Real.exp (-0.1598 * t) * countDensity q t)
      ≤ᵐ[volume.restrict (Set.Ioi T)] G := by
    rw [hG, hF, hH]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hcd := countDensity_le_linear q T t hT ht
    have hcd' : countDensity q t ≤
        ((1 / (2 * π)) / T) * (t - T) + ((1 / (2 * π)) * L + 1 / (4 * T)) := by
      rw [hL]
      linarith
    have hexp : Real.exp (-0.1598 * t) =
        Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    calc Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)) * countDensity q t
        ≤ Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)) *
            (((1 / (2 * π)) / T) * (t - T) + ((1 / (2 * π)) * L + 1 / (4 * T))) :=
          mul_le_mul_of_nonneg_left hcd'
            (by positivity : (0 : ℝ) ≤ Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)))
      _ = Real.exp (-0.1598 * T) *
            (((1 / (2 * π)) * L + 1 / (4 * T)) * Real.exp (-0.1598 * (t - T)) +
             ((1 / (2 * π)) / T) * ((t - T) * Real.exp (-0.1598 * (t - T)))) := by ring
  have hmain : expTailIntegral q T ≤ ∫ t in Set.Ioi T, G t := by
    have h := integral_mono_of_nonneg (μ := volume.restrict (Set.Ioi T)) hf_nonneg hGint hle
    simpa [expTailIntegral] using h
  have hLlow : (2.7672 : ℝ) ≤ L := by
    rw [hL]
    exact log_qt_lower q T hT
  have hnum : (1 / (2 * π)) * L * (1 / 0.1598) + ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2) +
      (1 / (4 * T)) * (1 / 0.1598) ≤ 1.0242 * L := by
    simpa [div_eq_mul_inv] using expTail_arithmetic L T hLlow hT
  calc expTailIntegral q T ≤ ∫ t in Set.Ioi T, G t := hmain
    _ = Real.exp (-0.1598 * T) *
      (((1 / (2 * π)) * L + 1 / (4 * T)) * (1 / 0.1598) +
        ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2)) := hGval
    _ ≤ 1.0242 * log ((q : ℝ) * T / (2 * π)) * Real.exp (-0.1598 * T) := by
        rw [← hL]
        have h2 : ((1 / (2 * π)) * L + 1 / (4 * T)) * (1 / 0.1598) +
            ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2) ≤ 1.0242 * L := by
          nlinarith [hnum]
        have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-0.1598 * T)).le
        nlinarith [this]


/-! ## Shifting improper integrals to the origin -/

private theorem integral_Ioi_shift (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) :
    ∫ t in Set.Ioi T, f (t - T) = ∫ s in Set.Ioi (0 : ℝ), f s := by
  have hiff : ∀ t : ℝ, (0 : ℝ) < t + (-T) ↔ T < t := by
    intro t; constructor <;> intro h <;> linarith
  have hpt : (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator f (t + (-T)))
      = fun t : ℝ => (Set.Ioi T).indicator (fun t => f (t - T)) t := by
    funext t
    by_cases ht : T < t
    · have h1 : (0 : ℝ) < t + (-T) := (hiff t).mpr ht
      simp [Set.indicator, ht, h1, sub_eq_add_neg]
    · have h1 : ¬ (0 : ℝ) < t + (-T) := fun h => ht ((hiff t).mp h)
      simp [Set.indicator, ht, h1, sub_eq_add_neg]
  have hfm : StronglyMeasurable ((Set.Ioi (0 : ℝ)).indicator f) :=
    (hf.measurable.indicator measurableSet_Ioi).stronglyMeasurable
  have hmap := integral_map_of_stronglyMeasurable (μ := volume)
    (φ := fun x : ℝ => x + (-T)) (by fun_prop : Measurable (fun x : ℝ => x + (-T))) hfm
  rw [(inferInstance : Measure.IsAddRightInvariant (volume : Measure ℝ)).map_add_right_eq_self (-T)]
    at hmap
  calc ∫ t in Set.Ioi T, f (t - T)
      = ∫ t, (Set.Ioi T).indicator (fun t => f (t - T)) t := by
        rw [integral_indicator measurableSet_Ioi]
    _ = ∫ t, (Set.Ioi (0 : ℝ)).indicator f (t + (-T)) := by rw [hpt]
    _ = ∫ s, (Set.Ioi (0 : ℝ)).indicator f s := hmap.symm
    _ = ∫ s in Set.Ioi (0 : ℝ), f s := by rw [integral_indicator measurableSet_Ioi]

private theorem integrableOn_shift (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) :
    IntegrableOn (fun t => f (t - T)) (Set.Ioi T) ↔ IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  have hiff : ∀ t : ℝ, (0 : ℝ) < t + (-T) ↔ T < t := by
    intro t; constructor <;> intro h <;> linarith
  have hpt : (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator f (t + (-T)))
      =ᵐ[volume] fun t : ℝ => (Set.Ioi T).indicator (fun t => f (t - T)) t := by
    filter_upwards with t
    by_cases ht : T < t
    · have h1 : (0 : ℝ) < t + (-T) := (hiff t).mpr ht
      simp [Set.indicator, ht, h1, sub_eq_add_neg]
    · have h1 : ¬ (0 : ℝ) < t + (-T) := fun h => ht ((hiff t).mp h)
      simp [Set.indicator, ht, h1, sub_eq_add_neg]
  have hfm : AEStronglyMeasurable ((Set.Ioi (0 : ℝ)).indicator f)
      (Measure.map (fun x : ℝ => x + (-T)) volume) := by
    rw [(inferInstance : Measure.IsAddRightInvariant (volume : Measure ℝ)).map_add_right_eq_self (-T)]
    exact (hf.measurable.indicator measurableSet_Ioi).aestronglyMeasurable
  rw [← integrable_indicator_iff (f := fun t => f (t - T)) measurableSet_Ioi,
      ← integrable_indicator_iff (f := f) measurableSet_Ioi]
  have hmap := integrable_map_measure (μ := volume) (f := fun x : ℝ => x + (-T))
    (g := (Set.Ioi (0 : ℝ)).indicator f) hfm
    (by fun_prop : AEMeasurable (fun x : ℝ => x + (-T)) volume)
  rw [(inferInstance : Measure.IsAddRightInvariant (volume : Measure ℝ)).map_add_right_eq_self (-T)]
    at hmap
  rw [← integrable_congr hpt]
  exact hmap.symm

/-! ## Power times exponential, shifted -/

private theorem integral_Ioi_pow_exp_neg_mul_sub (lam T : ℝ) (hlam : 0 < lam) (k : ℕ) :
    ∫ t in Set.Ioi T, (t - T)^k * Real.exp (-lam * (t - T)) = k.factorial / lam^(k+1) := by
  have hcont : Continuous (fun s : ℝ => s^k * Real.exp (-lam*s)) := by fun_prop
  rw [integral_Ioi_shift (fun s : ℝ => s^k * Real.exp (-lam*s)) hcont T]
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k:ℝ)+1) (r := lam)
    (by positivity) hlam
  have hexp : (k:ℝ)+1-1 = (k:ℝ) := by ring
  rw [hexp] at h1
  have hsimp : ∫ s in Set.Ioi (0:ℝ), s^k * Real.exp (-lam*s)
      = ∫ s in Set.Ioi (0:ℝ), s^(k:ℝ) * Real.exp (-(lam*s)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp [Real.rpow_natCast]
  rw [hsimp, h1]
  have hgamma : Real.Gamma ((k:ℝ)+1) = (k.factorial : ℝ) := Real.Gamma_nat_eq_factorial k
  rw [hgamma]
  rw [show (1:ℝ)/lam = lam⁻¹ by ring, Real.inv_rpow (le_of_lt hlam)]
  rw [show (lam:ℝ) ^ ((k:ℝ)+1) = lam ^ (k+1) by
    rw [show ((k:ℝ)+1) = ((k+1:ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]]
  rw [div_eq_mul_inv]
  ring

private theorem integrableOn_pow_exp_neg_mul_sub (lam T : ℝ) (hlam : 0 < lam) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t - T)^k * Real.exp (-lam * (t - T))) (Set.Ioi T) := by
  have hcont : Continuous (fun s : ℝ => s^k * Real.exp (-lam*s)) := by fun_prop
  rw [integrableOn_shift (fun s : ℝ => s^k * Real.exp (-lam*s)) hcont T]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k:ℝ)) (b := lam)
    (by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith) (by norm_num) hlam
  refine h.congr_fun ?_ measurableSet_Ioi
  intro s hs
  simp [Real.rpow_one, Real.rpow_natCast]

/-! ## The scalar inequality `exp (-y) ≤ 1 - y + y²/2` -/

private theorem exp_neg_le_one_sub_add_sq (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y^2/2 := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 1 - y + y^2/2 - Real.exp (-y))
      (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (1:ℝ) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => y^2/2) x x := by
      have h := (hasDerivAt_pow 2 x).div_const 2
      convert h using 1
      ring
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      have h := (hasDerivAt_neg x).exp
      convert h using 1
      ring
    have h := (h1.add h2).sub h3
    convert h using 1
    ring
  have hmono : MonotoneOn (fun y : ℝ => 1 - y + y^2/2 - Real.exp (-y)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro x hx
      rw [(hderiv x).deriv]
      have := Real.add_one_le_exp (-x)
      linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simpa using h

/-! ## The Gaussian factor, split at `T` -/

private theorem gaussian_exp_le (δ T t : ℝ) (hδ : δ ≠ 0) (ht : T < t) :
    Real.exp (-0.1065 * (t / (π * |δ|)) ^ 2) ≤
      Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) *
        Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T)) *
        (1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
          0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4)) := by
  have hdabs : (0:ℝ) < |δ| := abs_pos.mpr hδ
  have hd : (0:ℝ) < π * |δ| := by positivity
  have hy : (0:ℝ) ≤ 0.1065 * (t - T)^2 / (π * |δ|)^2 := by positivity
  have hineq := exp_neg_le_one_sub_add_sq (0.1065 * (t - T)^2 / (π * |δ|)^2) hy
  have hexp : Real.exp (-0.1065 * (t / (π * |δ|)) ^ 2)
      = Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) *
        Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T)) *
        Real.exp (-(0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hexp]
  have hpos1 : (0:ℝ) < Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) := Real.exp_pos _
  have hpos2 : (0:ℝ) < Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T)) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hineq (le_of_lt (mul_pos hpos1 hpos2))
  calc Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) *
        Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T)) *
        Real.exp (-(0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2))
      = (Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) *
        Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T))) *
        Real.exp (-(0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2)) := by ring
    _ ≤ (Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) *
        Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T))) *
        (1 - 0.1065 * (t - T)^2 / (π * |δ|)^2 + (0.1065 * (t - T)^2 / (π * |δ|)^2)^2/2) := hmul
    _ = Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) *
        Real.exp (-(2 * 0.1065 * T / (π * |δ|) ^ 2) * (t - T)) *
        (1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
          0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4)) := by ring

/-! ## The six-term combination of `(t-T)^k exp (-lam (t-T))` -/

private theorem gaussian_combo_integrable (lam T : ℝ) (hlam : 0 < lam) (k : Fin 6 → ℝ) :
    IntegrableOn (fun t => ∑ i : Fin 6, k i * ((t - T) ^ (i : ℕ) * Real.exp (-lam * (t - T))))
      (Set.Ioi T) := by
  have h : ∀ i : Fin 6, IntegrableOn
      (fun t => k i * ((t - T) ^ (i : ℕ) * Real.exp (-lam * (t - T)))) (Set.Ioi T) :=
    fun i => (integrableOn_pow_exp_neg_mul_sub lam T hlam (i : ℕ)).const_mul (k i)
  exact integrable_finsetSum (Finset.univ : Finset (Fin 6)) (fun i _ => h i)

private theorem gaussian_combo_integral (lam T : ℝ) (hlam : 0 < lam) (k : Fin 6 → ℝ) :
    ∫ t in Set.Ioi T, ∑ i : Fin 6, k i * ((t - T) ^ (i : ℕ) * Real.exp (-lam * (t - T)))
      = ∑ i : Fin 6, k i * (((i : ℕ).factorial : ℝ) / lam ^ ((i : ℕ) + 1)) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_Ioi_pow_exp_neg_mul_sub lam T hlam (i : ℕ)]
  · intro i _
    exact (integrableOn_pow_exp_neg_mul_sub lam T hlam (i : ℕ)).const_mul (k i)

/-! ## The arithmetic core of the Gaussian bound -/

/-! ## The numeric core of the Gaussian bound -/

set_option maxHeartbeats 1600000 in
/-- The numeric core of the Gaussian bound, in the `X` form. -/
private theorem gaussian_numeric (X d0 T Lt : ℝ) (hd : 0 < d0) (hT : 100 ≤ T)
    (hXge : 4 * π ≤ X) (hTX : T = π * d0 * X) (hLt : 2.7672 ≤ Lt) :
    Lt * d0 / (4 * 0.1065 * X) + 1 / (8 * 0.1065 * X ^ 2) + d0 / (8 * 0.1065 ^ 2 * X ^ 3)
      - Lt * d0 / (8 * 0.1065 ^ 2 * X ^ 3) - 3 * d0 / (16 * 0.1065 ^ 3 * X ^ 5)
      + 3 * Lt * d0 / (16 * 0.1065 ^ 3 * X ^ 5) + 3 / (32 * 0.1065 ^ 3 * X ^ 6)
      + 15 * d0 / (32 * 0.1065 ^ 4 * X ^ 7) ≤ 0.18787 * d0 * Lt := by
  have hXpos : 0 < X := by nlinarith [hXge, Real.pi_gt_d6]
  have hLtpos : 0 < Lt := by linarith
  have hdLt : 0 < d0 * Lt := by positivity
  have hXbig : (12.566 : ℝ) ≤ X := by nlinarith [hXge, Real.pi_gt_d6]
  have hXL : (12.566 : ℝ) * 2.7672 ≤ X * Lt := by nlinarith [hXbig, hLt]
  have hLtinv : 1 / Lt ≤ 1 / 2.7672 := one_div_le_one_div_of_le (by norm_num) hLt
  have hd0inv : 1 / d0 ≤ π * X / 100 := by
    rw [div_le_iff₀ hd]; nlinarith [hTX, hT]
  suffices hPhi : 1 / (4 * 0.1065 * X) + 1 / (8 * 0.1065 * X ^ 2 * d0 * Lt)
      - 1 / (8 * 0.1065 ^ 2 * X ^ 3) + 1 / (8 * 0.1065 ^ 2 * X ^ 3 * Lt)
      - 3 / (16 * 0.1065 ^ 3 * X ^ 5 * Lt) + 3 / (16 * 0.1065 ^ 3 * X ^ 5)
      + 3 / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt)
      + 15 / (32 * 0.1065 ^ 4 * X ^ 7 * Lt) ≤ (0.18787 : ℝ) by
    have hq : (Lt * d0 / (4 * 0.1065 * X) + 1 / (8 * 0.1065 * X ^ 2) + d0 / (8 * 0.1065 ^ 2 * X ^ 3)
        - Lt * d0 / (8 * 0.1065 ^ 2 * X ^ 3) - 3 * d0 / (16 * 0.1065 ^ 3 * X ^ 5)
        + 3 * Lt * d0 / (16 * 0.1065 ^ 3 * X ^ 5) + 3 / (32 * 0.1065 ^ 3 * X ^ 6)
        + 15 * d0 / (32 * 0.1065 ^ 4 * X ^ 7)) / (d0 * Lt)
        = 1 / (4 * 0.1065 * X) + 1 / (8 * 0.1065 * X ^ 2 * d0 * Lt)
          - 1 / (8 * 0.1065 ^ 2 * X ^ 3) + 1 / (8 * 0.1065 ^ 2 * X ^ 3 * Lt)
          - 3 / (16 * 0.1065 ^ 3 * X ^ 5 * Lt) + 3 / (16 * 0.1065 ^ 3 * X ^ 5)
          + 3 / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt)
          + 15 / (32 * 0.1065 ^ 4 * X ^ 7 * Lt) := by
      field_simp
      ring
    rw [← hq] at hPhi
    have h2 := (div_le_iff₀ hdLt).1 hPhi
    calc Lt * d0 / (4 * 0.1065 * X) + 1 / (8 * 0.1065 * X ^ 2) + d0 / (8 * 0.1065 ^ 2 * X ^ 3)
        - Lt * d0 / (8 * 0.1065 ^ 2 * X ^ 3) - 3 * d0 / (16 * 0.1065 ^ 3 * X ^ 5)
        + 3 * Lt * d0 / (16 * 0.1065 ^ 3 * X ^ 5) + 3 / (32 * 0.1065 ^ 3 * X ^ 6)
        + 15 * d0 / (32 * 0.1065 ^ 4 * X ^ 7) ≤ 0.18787 * (d0 * Lt) := h2
      _ = 0.18787 * d0 * Lt := by ring
  by_cases hcase : X ≤ 13
  · have hX3 : X ^ 3 ≤ 13 ^ 3 := pow_le_pow_left₀ (by linarith) hcase 3
    have hX5 : (12.566 : ℝ) ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ (by norm_num) hXbig 5
    have hX7 : (12.566 : ℝ) ^ 7 ≤ X ^ 7 := pow_le_pow_left₀ (by norm_num) hXbig 7
    have hX3L : (12.566 : ℝ) ^ 3 * 2.7672 ≤ X ^ 3 * Lt := by
      have h3 : (12.566 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hXbig 3
      nlinarith only [h3, hLt, pow_pos hXpos 3]
    have hX5L : (12.566 : ℝ) ^ 5 * 2.7672 ≤ X ^ 5 * Lt :=
      mul_le_mul hX5 hLt (by norm_num) (pow_pos hXpos 5).le
    have hX7L : (12.566 : ℝ) ^ 7 * 2.7672 ≤ X ^ 7 * Lt :=
      mul_le_mul hX7 hLt (by norm_num) (pow_pos hXpos 7).le
    have t1 : 1 / (4 * 0.1065 * X) ≤ (0.186808 : ℝ) := by
      have h1 : 1 / (4 * 0.1065 * X) ≤ 1 / (4 * 0.1065 * 12.566) := by
        apply one_div_le_one_div_of_le (a := 4 * 0.1065 * 12.566) (by norm_num)
        nlinarith only [hXbig]
      have h2 : 1 / (4 * 0.1065 * 12.566) ≤ (0.186808 : ℝ) := by norm_num
      exact h1.trans h2
    have t2 : 1 / (8 * 0.1065 * X ^ 2 * d0 * Lt) ≤ (0.001061 : ℝ) := by
      have ha : 1 / (8 * 0.1065 * X ^ 2 * d0 * Lt) ≤ π / (800 * 0.1065 * X * Lt) := by
        rw [show (1:ℝ) / (8 * 0.1065 * X ^ 2 * d0 * Lt)
            = (1 / d0) * (1 / (8 * 0.1065 * X ^ 2 * Lt)) by field_simp; try ring]
        have hpos2 : (0:ℝ) < 1 / (8 * 0.1065 * X ^ 2 * Lt) := by positivity
        calc (1 / d0) * (1 / (8 * 0.1065 * X ^ 2 * Lt))
            ≤ (π * X / 100) * (1 / (8 * 0.1065 * X ^ 2 * Lt)) :=
              mul_le_mul_of_nonneg_right hd0inv hpos2.le
          _ = π / (800 * 0.1065 * X * Lt) := by field_simp; try ring
      have hb : π / (800 * 0.1065 * X * Lt) ≤ 3.141593 / (800 * 0.1065 * 12.566 * 2.7672) := by
        have h1 : π / (800 * 0.1065 * X * Lt) ≤ 3.141593 / (800 * 0.1065 * X * Lt) := by
          gcongr
          exact le_of_lt Real.pi_lt_d6
        have h2 : 3.141593 / (800 * 0.1065 * X * Lt)
            ≤ 3.141593 / (800 * 0.1065 * 12.566 * 2.7672) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith only [hXL]
        exact h1.trans h2
      have hc : 3.141593 / (800 * 0.1065 * 12.566 * 2.7672) ≤ (0.001061 : ℝ) := by norm_num
      linarith only [ha, hb, hc]
    have t3a : -(1 / (8 * 0.1065 ^ 2 * X ^ 3)) ≤ -(0.0050162 : ℝ) := by
      have ha : (0.0050162 : ℝ) ≤ 1 / (8 * 0.1065 ^ 2 * X ^ 3) := by
        have h1 : 1 / (8 * 0.1065 ^ 2 * 13 ^ 3) ≤ 1 / (8 * 0.1065 ^ 2 * X ^ 3) := by
          apply one_div_le_one_div_of_le (a := 8 * 0.1065 ^ 2 * X ^ 3) (by positivity)
          nlinarith only [hX3]
        have h2 : (0.0050162 : ℝ) ≤ 1 / (8 * 0.1065 ^ 2 * 13 ^ 3) := by norm_num
        exact h2.trans h1
      linarith only [ha]
    have t3b : 1 / (8 * 0.1065 ^ 2 * X ^ 3 * Lt) ≤ (0.0020072 : ℝ) := by
      have h1 : 1 / (8 * 0.1065 ^ 2 * X ^ 3 * Lt)
          ≤ 1 / (8 * 0.1065 ^ 2 * 12.566 ^ 3 * 2.7672) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith only [hX3L]
      have h2 : 1 / (8 * 0.1065 ^ 2 * 12.566 ^ 3 * 2.7672) ≤ (0.0020072 : ℝ) := by norm_num
      exact h1.trans h2
    have t4 : -(3 / (16 * 0.1065 ^ 3 * X ^ 5 * Lt)) ≤ 0 := by
      have hpos : (0:ℝ) ≤ 3 / (16 * 0.1065 ^ 3 * X ^ 5 * Lt) := by positivity
      linarith only [hpos]
    have t5 : 3 / (16 * 0.1065 ^ 3 * X ^ 5) ≤ (0.0004955 : ℝ) := by
      have h1 : 3 / (16 * 0.1065 ^ 3 * X ^ 5) ≤ 3 / (16 * 0.1065 ^ 3 * 12.566 ^ 5) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith only [hX5]
      have h2 : 3 / (16 * 0.1065 ^ 3 * 12.566 ^ 5) ≤ (0.0004955 : ℝ) := by norm_num
      exact h1.trans h2
    have t6 : 3 / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt) ≤ (0.0000029 : ℝ) := by
      have ha : 3 / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt)
          ≤ 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt) := by
        rw [show (3:ℝ) / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt)
            = (1 / d0) * (3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt)) by field_simp; try ring]
        have hpos2 : (0:ℝ) < 3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt) := by positivity
        calc (1 / d0) * (3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt))
            ≤ (π * X / 100) * (3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt)) :=
              mul_le_mul_of_nonneg_right hd0inv hpos2.le
          _ = 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt) := by field_simp; try ring
      have hb : 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt)
          ≤ 3 * 3.141593 / (3200 * 0.1065 ^ 3 * 12.566 ^ 5 * 2.7672) := by
        have h1 : 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt)
            ≤ 3 * 3.141593 / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt) := by
          gcongr
          linarith only [Real.pi_lt_d6]
        have h2 : 3 * 3.141593 / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt)
            ≤ 3 * 3.141593 / (3200 * 0.1065 ^ 3 * 12.566 ^ 5 * 2.7672) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith only [hX5L]
        exact h1.trans h2
      have hc : 3 * 3.141593 / (3200 * 0.1065 ^ 3 * 12.566 ^ 5 * 2.7672) ≤ (0.0000029 : ℝ) := by
        norm_num
      linarith only [ha, hb, hc]
    have t7 : 15 / (32 * 0.1065 ^ 4 * X ^ 7 * Lt) ≤ (0.0000267 : ℝ) := by
      have h1 : 15 / (32 * 0.1065 ^ 4 * X ^ 7 * Lt)
          ≤ 15 / (32 * 0.1065 ^ 4 * 12.566 ^ 7 * 2.7672) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith only [hX7L]
      have h2 : 15 / (32 * 0.1065 ^ 4 * 12.566 ^ 7 * 2.7672) ≤ (0.0000267 : ℝ) := by norm_num
      exact h1.trans h2
    linarith only [t1, t2, t3a, t3b, t4, t5, t6, t7]
  · push_neg at hcase
    have hX5 : 13 ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ (by norm_num) hcase.le 5
    have hX7 : 13 ^ 7 ≤ X ^ 7 := pow_le_pow_left₀ (by norm_num) hcase.le 7
    have hX3L : (12.566 : ℝ) ^ 3 * 2.7672 ≤ X ^ 3 * Lt := by
      have h3 : (12.566 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hXbig 3
      nlinarith only [h3, hLt, pow_pos hXpos 3]
    have hX5L : 13 ^ 5 * 2.7672 ≤ X ^ 5 * Lt :=
      mul_le_mul hX5 hLt (by norm_num) (pow_pos hXpos 5).le
    have hX7L : 13 ^ 7 * 2.7672 ≤ X ^ 7 * Lt :=
      mul_le_mul hX7 hLt (by norm_num) (pow_pos hXpos 7).le
    have t1 : 1 / (4 * 0.1065 * X) ≤ (0.1805707 : ℝ) := by
      have h1 : 1 / (4 * 0.1065 * X) ≤ 1 / (4 * 0.1065 * 13) := by
        apply one_div_le_one_div_of_le (a := 4 * 0.1065 * 13) (by norm_num)
        nlinarith only [hcase]
      have h2 : 1 / (4 * 0.1065 * 13) ≤ (0.1805707 : ℝ) := by norm_num
      exact h1.trans h2
    have t2 : 1 / (8 * 0.1065 * X ^ 2 * d0 * Lt) ≤ (0.0010251 : ℝ) := by
      have ha : 1 / (8 * 0.1065 * X ^ 2 * d0 * Lt) ≤ π / (800 * 0.1065 * X * Lt) := by
        rw [show (1:ℝ) / (8 * 0.1065 * X ^ 2 * d0 * Lt)
            = (1 / d0) * (1 / (8 * 0.1065 * X ^ 2 * Lt)) by field_simp; try ring]
        have hpos2 : (0:ℝ) < 1 / (8 * 0.1065 * X ^ 2 * Lt) := by positivity
        calc (1 / d0) * (1 / (8 * 0.1065 * X ^ 2 * Lt))
            ≤ (π * X / 100) * (1 / (8 * 0.1065 * X ^ 2 * Lt)) :=
              mul_le_mul_of_nonneg_right hd0inv hpos2.le
          _ = π / (800 * 0.1065 * X * Lt) := by field_simp; try ring
      have hb : π / (800 * 0.1065 * X * Lt) ≤ 3.141593 / (800 * 0.1065 * 13 * 2.7672) := by
        have h1 : π / (800 * 0.1065 * X * Lt) ≤ 3.141593 / (800 * 0.1065 * X * Lt) := by
          gcongr
          exact le_of_lt Real.pi_lt_d6
        have h2 : 3.141593 / (800 * 0.1065 * X * Lt)
            ≤ 3.141593 / (800 * 0.1065 * 13 * 2.7672) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith only [hcase.le, hLt]
        exact h1.trans h2
      have hc : 3.141593 / (800 * 0.1065 * 13 * 2.7672) ≤ (0.0010251 : ℝ) := by norm_num
      linarith only [ha, hb, hc]
    have t3a : -(1 / (8 * 0.1065 ^ 2 * X ^ 3)) ≤ 0 := by
      have h : (0:ℝ) ≤ 1 / (8 * 0.1065 ^ 2 * X ^ 3) := by positivity
      linarith only [h]
    have t3b : 1 / (8 * 0.1065 ^ 2 * X ^ 3 * Lt) ≤ (0.0020072 : ℝ) := by
      have h1 : 1 / (8 * 0.1065 ^ 2 * X ^ 3 * Lt)
          ≤ 1 / (8 * 0.1065 ^ 2 * 12.566 ^ 3 * 2.7672) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith only [hX3L]
      have h2 : 1 / (8 * 0.1065 ^ 2 * 12.566 ^ 3 * 2.7672) ≤ (0.0020072 : ℝ) := by norm_num
      exact h1.trans h2
    have t4 : -(3 / (16 * 0.1065 ^ 3 * X ^ 5 * Lt)) ≤ 0 := by
      have hpos : (0:ℝ) ≤ 3 / (16 * 0.1065 ^ 3 * X ^ 5 * Lt) := by positivity
      linarith only [hpos]
    have t5 : 3 / (16 * 0.1065 ^ 3 * X ^ 5) ≤ (0.0004181 : ℝ) := by
      have h1 : 3 / (16 * 0.1065 ^ 3 * X ^ 5) ≤ 3 / (16 * 0.1065 ^ 3 * 13 ^ 5) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith only [hX5]
      have h2 : 3 / (16 * 0.1065 ^ 3 * 13 ^ 5) ≤ (0.0004181 : ℝ) := by norm_num
      exact h1.trans h2
    have t6 : 3 / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt) ≤ (0.0000025 : ℝ) := by
      have ha : 3 / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt)
          ≤ 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt) := by
        rw [show (3:ℝ) / (32 * 0.1065 ^ 3 * X ^ 6 * d0 * Lt)
            = (1 / d0) * (3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt)) by field_simp; try ring]
        have hpos2 : (0:ℝ) < 3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt) := by positivity
        calc (1 / d0) * (3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt))
            ≤ (π * X / 100) * (3 / (32 * 0.1065 ^ 3 * X ^ 6 * Lt)) :=
              mul_le_mul_of_nonneg_right hd0inv hpos2.le
          _ = 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt) := by field_simp; try ring
      have hb : 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt)
          ≤ 3 * 3.141593 / (3200 * 0.1065 ^ 3 * 13 ^ 5 * 2.7672) := by
        have h1 : 3 * π / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt)
            ≤ 3 * 3.141593 / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt) := by
          gcongr
          linarith only [Real.pi_lt_d6]
        have h2 : 3 * 3.141593 / (3200 * 0.1065 ^ 3 * X ^ 5 * Lt)
            ≤ 3 * 3.141593 / (3200 * 0.1065 ^ 3 * 13 ^ 5 * 2.7672) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith only [hX5L]
        exact h1.trans h2
      have hc : 3 * 3.141593 / (3200 * 0.1065 ^ 3 * 13 ^ 5 * 2.7672) ≤ (0.0000025 : ℝ) := by
        norm_num
      linarith only [ha, hb, hc]
    have t7 : 15 / (32 * 0.1065 ^ 4 * X ^ 7 * Lt) ≤ (0.0000210 : ℝ) := by
      have h1 : 15 / (32 * 0.1065 ^ 4 * X ^ 7 * Lt)
          ≤ 15 / (32 * 0.1065 ^ 4 * 13 ^ 7 * 2.7672) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith only [hX7L]
      have h2 : 15 / (32 * 0.1065 ^ 4 * 13 ^ 7 * 2.7672) ≤ (0.0000210 : ℝ) := by norm_num
      exact h1.trans h2
    linarith only [t1, t2, t3a, t3b, t4, t5, t6, t7]

/-! ## The Gaussian tail integral, display 4.37 to 4.41 -/

set_option maxHeartbeats 1600000 in
private theorem gaussian_integral_bound_aux (q : ℕ) [NeZero q] (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log ((q : ℝ) * T / (2 * π)) *
        Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
  classical
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT4 : 4 * π ^ 2 * |δ| ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hd0 : (0:ℝ) < |δ| := abs_pos.mpr hδ
  have hb : (0:ℝ) < 0.1065 := by norm_num
  have hLc : (0:ℝ) < π * |δ| := by positivity
  set Lt : ℝ := log ((q : ℝ) * T / (2 * π)) with hLtdef
  have hLtlow : (2.7672 : ℝ) ≤ Lt := by
    rw [hLtdef]; exact log_qt_lower q T hT100
  set lam : ℝ := 2 * 0.1065 * T / (π * |δ|) ^ 2 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  set s0 : ℝ := 1 / lam with hs0def
  have hs0eq : s0 = (π * |δ|) ^ 2 / (2 * 0.1065 * T) := by
    rw [hs0def, hlamdef]; field_simp; try ring
  set X : ℝ := T / (π * |δ|) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; positivity
  have hTX : T = π * |δ| * X := by rw [hXdef]; field_simp
  have hXge : 4 * π ≤ X := by
    rw [hXdef, le_div_iff₀ hLc]
    nlinarith only [hT4]
  set k : Fin 6 → ℝ := ![(1 / (2 * π)) * Lt + 1 / (4 * T), (1 / (2 * π)) / T,
      -(((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 / (π * |δ|) ^ 2)),
      -(((1 / (2 * π)) / T) * (0.1065 / (π * |δ|) ^ 2)),
      ((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4)),
      ((1 / (2 * π)) / T) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))] with hk
  set g : ℝ → ℝ := fun t => Real.exp (-0.1065 * X ^ 2) *
      ∑ i : Fin 6, k i * ((t - T) ^ (i : ℕ) * Real.exp (-lam * (t - T))) with hg
  have hgint : IntegrableOn g (Set.Ioi T) := by
    rw [hg]
    exact (gaussian_combo_integrable lam T hlampos k).const_mul _
  have hval : ∫ t in Set.Ioi T, g t = Real.exp (-0.1065 * X ^ 2) *
      (((1 / (2 * π)) * Lt + 1 / (4 * T)) * s0 + (1 / (2 * π * T)) * s0 ^ 2
       - (((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 / (π * |δ|) ^ 2)) * (2 * s0 ^ 3)
       - ((1 / (2 * π * T)) * (0.1065 / (π * |δ|) ^ 2)) * (6 * s0 ^ 4)
       + (((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))) * (24 * s0 ^ 5)
       + ((1 / (2 * π * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))) * (120 * s0 ^ 6)) := by
    rw [hg, integral_const_mul, gaussian_combo_integral lam T hlampos k]
    congr 1
    simp only [Fin.sum_univ_six, hk]
    simp
    rw [hs0def]
    norm_num
    field_simp
    try ring
  have hf_nonneg : ((0 : ℝ → ℝ)) ≤ᵐ[volume.restrict (Set.Ioi T)]
      (fun t => Real.exp (-0.1065 * (t / (π * |δ|)) ^ 2) * countDensity q t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (countDensity_nonneg q T t hT100 ht)
  have hle : (fun t => Real.exp (-0.1065 * (t / (π * |δ|)) ^ 2) * countDensity q t)
      ≤ᵐ[volume.restrict (Set.Ioi T)] g := by
    rw [hg]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hexp0 := gaussian_exp_le δ T t hδ ht
    have hexp : Real.exp (-0.1065 * (t / (π * |δ|)) ^ 2) ≤
        Real.exp (-0.1065 * X ^ 2) * Real.exp (-lam * (t - T)) *
          (1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
            0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4)) := by
      rw [hXdef, hlamdef]
      exact hexp0
    have hcd := countDensity_le_linear q T t hT100 ht
    -- the polynomial factor is nonnegative
    have hpoly : (0:ℝ) ≤ 1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
        0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4) := by
      have hy : (0:ℝ) ≤ 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 := by positivity
      have h := exp_neg_le_one_sub_add_sq (0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2) hy
      have hy2 : (0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2) ^ 2 / 2
          = 0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4) := by
        field_simp; try ring
      rw [hy2] at h
      have h2 : (0:ℝ) < Real.exp (-(0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2)) := Real.exp_pos _
      linarith only [h, h2]
    have hE2 : (0:ℝ) ≤ Real.exp (-0.1065 * X ^ 2) * Real.exp (-lam * (t - T)) *
        (1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
          0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4)) := by
      have h1 : (0:ℝ) < Real.exp (-0.1065 * X ^ 2) := Real.exp_pos _
      have h2 : (0:ℝ) < Real.exp (-lam * (t - T)) := Real.exp_pos _
      exact mul_nonneg (mul_nonneg h1.le h2.le) hpoly
    have hcdN := countDensity_nonneg q T t hT100 ht
    have hstep : Real.exp (-0.1065 * (t / (π * |δ|)) ^ 2) * countDensity q t
        ≤ (Real.exp (-0.1065 * X ^ 2) * Real.exp (-lam * (t - T)) *
            (1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
              0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4))) *
            ((1 / (2 * π)) * log ((q : ℝ) * T / (2 * π)) +
              (1 / (2 * π)) / T * (t - T) + 1 / (4 * T)) :=
      mul_le_mul hexp hcd hcdN hE2
    have hident : (∑ i : Fin 6, k i * ((t - T) ^ (i : ℕ) * Real.exp (-lam * (t - T))))
        = Real.exp (-lam * (t - T)) *
            (1 - 0.1065 * (t - T) ^ 2 / (π * |δ|) ^ 2 +
              0.1065 ^ 2 * (t - T) ^ 4 / (2 * (π * |δ|) ^ 4)) *
            ((1 / (2 * π)) * Lt + (1 / (2 * π)) / T * (t - T) + 1 / (4 * T)) := by
      set e := Real.exp (-lam * (t - T)) with he
      rw [Fin.sum_univ_six, hk]
      simp
      try ring
    refine hstep.trans (le_of_eq ?_)
    rw [hident]
    ring
  have hnum := gaussian_numeric X |δ| T Lt hd0 hT100 hXge hTX hLtlow
  have hmain : gaussianTailIntegral q δ T ≤ ∫ t in Set.Ioi T, g t := by
    rw [gaussianTailIntegral, if_neg hδ]
    exact integral_mono_of_nonneg (μ := volume.restrict (Set.Ioi T)) hf_nonneg hgint hle
  calc gaussianTailIntegral q δ T ≤ ∫ t in Set.Ioi T, g t := hmain
    _ = Real.exp (-0.1065 * X ^ 2) *
        (((1 / (2 * π)) * Lt + 1 / (4 * T)) * s0 + (1 / (2 * π * T)) * s0 ^ 2
         - (((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 / (π * |δ|) ^ 2)) * (2 * s0 ^ 3)
         - ((1 / (2 * π * T)) * (0.1065 / (π * |δ|) ^ 2)) * (6 * s0 ^ 4)
         + (((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))) * (24 * s0 ^ 5)
         + ((1 / (2 * π * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))) * (120 * s0 ^ 6)) := hval
    _ ≤ Real.exp (-0.1065 * X ^ 2) * (0.18787 * |δ| * Lt) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have hconv : ((1 / (2 * π)) * Lt + 1 / (4 * T)) * s0 + (1 / (2 * π * T)) * s0 ^ 2
            - (((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 / (π * |δ|) ^ 2)) * (2 * s0 ^ 3)
            - ((1 / (2 * π * T)) * (0.1065 / (π * |δ|) ^ 2)) * (6 * s0 ^ 4)
            + (((1 / (2 * π)) * Lt + 1 / (4 * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))) * (24 * s0 ^ 5)
            + ((1 / (2 * π * T)) * (0.1065 ^ 2 / (2 * (π * |δ|) ^ 4))) * (120 * s0 ^ 6)
            = Lt * |δ| / (4 * 0.1065 * X) + 1 / (8 * 0.1065 * X ^ 2)
              + |δ| / (8 * 0.1065 ^ 2 * X ^ 3)
              - Lt * |δ| / (8 * 0.1065 ^ 2 * X ^ 3) - 3 * |δ| / (16 * 0.1065 ^ 3 * X ^ 5)
              + 3 * Lt * |δ| / (16 * 0.1065 ^ 3 * X ^ 5) + 3 / (32 * 0.1065 ^ 3 * X ^ 6)
              + 15 * |δ| / (32 * 0.1065 ^ 4 * X ^ 7) - 1 / (16 * 0.1065 ^ 2 * X ^ 4) := by
          rw [hs0eq, hXdef]
          field_simp
          ring
        rw [hconv]
        have hdrop2 : (0:ℝ) ≤ 1 / (16 * 0.1065 ^ 2 * X ^ 4) := by positivity
        linarith only [hnum, hdrop2]
    _ = 0.18787 * |δ| * log ((q : ℝ) * T / (2 * π)) *
        Real.exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
        rw [hLtdef, hXdef]; ring

/-- PROVED. P0014 page 41, display 4.36: the exponential tail integral is at most
1.0242 log(qT/2π) e^(-0.1598 T) for T at least 100. Copy of Decomp269c.exp_integral_bound. -/
theorem exp_integral_bound (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    expTailIntegral q T ≤
      1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) := by
  exact exp_integral_bound_aux q T hT

/-- PROVED. P0014 page 42, displays 4.37 to 4.41: for nonzero shift the Gaussian tail integral
is at most 0.18787 abs delta log(qT/2π) e^(-0.1065 (T/(π abs delta))^2).
Copy of Decomp269c.gaussian_integral_bound. -/
theorem gaussian_integral_bound (q : ℕ) [NeZero q] (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
  exact gaussian_integral_bound_aux q δ T hδ hT

end LeanLab.HelfgottMajor.TailIntegral123
