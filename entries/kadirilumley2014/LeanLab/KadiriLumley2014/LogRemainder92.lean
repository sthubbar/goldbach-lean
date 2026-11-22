module

public import LeanLab.KadiriLumley2014.Weight

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4, the remainder before equation 2.16.
These elementary inequalities do not assume the cited explicit formula.
AI wrote this Lean code, Codex by OpenAI, 2026-10-26.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- A logarithmic difference is bounded by the linear exponential envelope. -/
theorem log_one_sub_exp_bound {u q : ℝ} (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.log (1 - Real.exp (-2 * u) * q) - Real.log (1 - q) ≤
      2 * u * q / (1 - q) := by
  have hE : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha : 0 < 1 - q := by linarith
  have hb : 0 < 1 - Real.exp (-2 * u) * q := by nlinarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hl
  have heq : (1 - Real.exp (-2 * u) * q) / (1 - q) - 1 =
      q * (1 - Real.exp (-2 * u)) / (1 - q) := by field_simp; ring
  rw [heq] at hl
  have hE' : 1 - Real.exp (-2 * u) ≤ 2 * u := by linarith [Real.add_one_le_exp (-2 * u)]
  have hp := mul_le_mul_of_nonneg_left hE' hq0
  exact hl.trans ((div_le_div_iff_of_pos_right ha).mpr (by nlinarith))

/-- Page 4 before equation 2.16, a pointwise bound at every Y at least X. -/
theorem logarithmic_remainder_bound {u X Y : ℝ} (hu : 0 ≤ u) (hX : 3 ≤ X) (hXY : X ≤ Y) :
    Real.log (1 - Real.exp (-2 * u) / Y ^ 2) - Real.log (1 - 1 / Y ^ 2) ≤ u / X := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := hX0.trans_le hXY
  have hY3 : 3 ≤ Y := hX.trans hXY
  have hYsq : 1 < Y ^ 2 := by nlinarith
  have hq : 1 / Y ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hY0)).mpr hYsq
  have hl := log_one_sub_exp_bound hu (by positivity : (0 : ℝ) ≤ 1 / Y ^ 2) hq
  have heq : 2 * u * (1 / Y ^ 2) / (1 - 1 / Y ^ 2) = 2 * u / (Y ^ 2 - 1) := by
    field_simp
  have hn : 0 < Y ^ 2 - 1 := by linarith
  have hc : 2 * u / (Y ^ 2 - 1) ≤ u / X := by
    apply (div_le_div_iff₀ hn hX0).mpr
    have hpoly : 0 ≤ Y ^ 2 - 1 - 2 * X := by nlinarith
    nlinarith [mul_nonneg hu hpoly]
  simpa [div_eq_mul_inv] using hl.trans (heq.le.trans hc)


/-- The logarithmic remainder is continuous on the smoothing interval. -/
theorem log_remainder_continuousOn {u δ X : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ =>
      Real.log (1 - Real.exp (-2 * u) / (X * (1 + δ * t)) ^ 2) -
        Real.log (1 - 1 / (X * (1 + δ * t)) ^ 2)) (Icc 0 1) := by
  have hY : ∀ t ∈ Icc (0 : ℝ) 1, 3 ≤ X * (1 + δ * t) := by
    intro t ht
    have h0 : 0 ≤ δ * t := mul_nonneg hδ ht.1
    nlinarith
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, 1 < (X * (1 + δ * t)) ^ 2 := by
    intro t ht
    nlinarith [hY t ht]
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (X * (1 + δ * t)) ^ 2 ≠ 0 := by
    intro t ht
    linarith [hsq t ht]
  have hc : ContinuousOn (fun t : ℝ => (X * (1 + δ * t)) ^ 2) (Icc 0 1) := by fun_prop
  have hE : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hA : ContinuousOn (fun t : ℝ => 1 - Real.exp (-2 * u) / (X * (1 + δ * t)) ^ 2)
      (Icc 0 1) := continuousOn_const.sub (continuousOn_const.div hc hne)
  have hB : ContinuousOn (fun t : ℝ => 1 - 1 / (X * (1 + δ * t)) ^ 2)
      (Icc 0 1) := continuousOn_const.sub (continuousOn_const.div hc hne)
  apply (hA.log _).sub (hB.log _)
  · intro t ht
    apply ne_of_gt
    apply sub_pos.mpr
    exact (div_lt_one (by nlinarith [hsq t ht])).mpr (hE.trans_lt (hsq t ht))
  · intro t ht
    apply ne_of_gt
    apply sub_pos.mpr
    exact (div_lt_one (by nlinarith [hsq t ht])).mpr (hsq t ht)

/-- Page 4 before equation 2.16. The normalized logarithmic term is at least
minus u divided by twice X, independently of the explicit formula. -/
theorem weighted_log_remainder_bound (m : ℕ) {u δ X : ℝ}
    (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hX : 3 ≤ X) :
    -(∫ t in (0 : ℝ)..1,
      (Real.log (1 - Real.exp (-2 * u) / (X * (1 + δ * t)) ^ 2) -
        Real.log (1 - 1 / (X * (1 + δ * t)) ^ 2)) * weight m t) /
      (2 * (∫ t in (0 : ℝ)..1, weight m t)) ≥ -(u / (2 * X)) := by
  have hc := log_remainder_continuousOn hu hδ hX
  have hi := (hc.mul (weight_continuous m).continuousOn).intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
  have hbound : (∫ t in (0 : ℝ)..1,
      (Real.log (1 - Real.exp (-2 * u) / (X * (1 + δ * t)) ^ 2) -
        Real.log (1 - 1 / (X * (1 + δ * t)) ^ 2)) * weight m t) ≤
      u / X * (∫ t in (0 : ℝ)..1, weight m t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num) hi
      (((weight_continuous m).const_mul (u / X)).intervalIntegrable _ _)
    intro t ht
    have hXY : X ≤ X * (1 + δ * t) := by
      have h0 : 0 ≤ δ * t := mul_nonneg hδ ht.1
      nlinarith
    exact mul_le_mul_of_nonneg_right (logarithmic_remainder_bound hu hX hXY) (weight_nonneg m ht)
  have hm := weight_mass_pos m
  have hX0 : 0 < X := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * (∫ t in (0 : ℝ)..1, weight m t))).mpr
  have heq : -(u / (2 * X)) * (2 * (∫ t in (0 : ℝ)..1, weight m t)) =
      -(u / X * (∫ t in (0 : ℝ)..1, weight m t)) := by field_simp
  rw [heq]
  linarith

end LeanLab.KadiriLumley2014.Task92
