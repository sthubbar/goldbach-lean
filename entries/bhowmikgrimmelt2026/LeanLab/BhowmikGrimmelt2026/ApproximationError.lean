module

public import LeanLab.BhowmikGrimmelt2026.Convolution

/-!
The exact error integral preceding the Parseval step in Lemma 7.3, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The finitely supported integer transform is a continuous function of frequency. -/
theorem continuous_GThat {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    {T : ℝ} (hT : 0 < T) : Continuous (GThat G T) := by
  have heq : GThat G T = fun β => ∑ n ∈ Finset.Icc ⌈-2 * T⌉ ⌊2 * T⌋,
      (GT G T n : ℂ) * ee (β * n) := by
    funext β
    apply tsum_eq_sum
    intro n hn
    simp [GT_int_eq_zero hsupp hT n hn]
  rw [heq]
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul (ee_contDiff.continuous.comp (continuous_id.mul continuous_const))

/-- The major arc weight transform is continuous. -/
theorem continuous_bRhat {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (heven : ∀ x, G (-x) = G x) (R : ℝ) (T : ℕ → ℝ)
    (hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q) : Continuous (bRhat G R T) := by
  have heq := funext (bRhat_eq hsupp heven R T hT)
  rw [heq]
  apply continuous_finset_sum
  intro q hq
  apply continuous_finset_sum
  intro a ha
  exact (continuous_GThat hsupp (hT q hq)).comp (continuous_id.sub continuous_const)

/-- The finite smoothed prime sum is continuous in frequency. -/
theorem continuous_Sphi (ϕ : ℝ → ℝ) (N : ℕ) : Continuous (Sphi ϕ N) := by
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul (ee_contDiff.continuous.comp (continuous_id.mul continuous_const))

/-- The difference in Lemma 7.3 equals the integral with multiplier one minus bRhat. -/
theorem rphi_sub_weighted_integral {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (heven : ∀ x, G (-x) = G x)
    (R : ℝ) (T : ℕ → ℝ) (hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q)
    (ϕ : ℝ → ℝ) (N : ℕ) :
    (rphi ϕ N : ℂ) - (∫ α in (0 : ℝ)..1,
      Sphi ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * (1 - bRhat G R T α) * ee (-(N * α)) := by
  have hcS := continuous_Sphi ϕ N
  have hcb := continuous_bRhat hsupp heven R T hT
  have hce : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hi1 : IntervalIntegrable (fun α => Sphi ϕ N α ^ 2 * ee (-(N * α))) volume 0 1 := by
    convert ((hcS.pow 2).mul hce).intervalIntegrable (μ := volume) (0 : ℝ) 1 using 1
  have hi2 : IntervalIntegrable
      (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α))) volume 0 1 := by
    convert (((hcS.pow 2).mul hcb).mul hce).intervalIntegrable (μ := volume) (0 : ℝ) 1 using 1
  rw [rphi_eq_integral, ← intervalIntegral.integral_sub hi1 hi2]
  apply intervalIntegral.integral_congr
  intro α hα
  ring

end LeanLab.BhowmikGrimmelt2026
