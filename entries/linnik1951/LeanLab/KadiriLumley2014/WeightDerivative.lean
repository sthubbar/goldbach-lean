module

public import LeanLab.KadiriLumley2014.Weight

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 10, proof of Lemma 3.1.
Journal INTEGERS 14 A61 page 13.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- An explicit polynomial for the first derivative. -/
def weightD (m : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * (4 * t * (1 - t)) ^ (m - 1) * (4 - 8 * t)

/-- The displayed polynomial is the derivative for every natural m. -/
theorem weight_hasDerivAt (m : ℕ) (t : ℝ) : HasDerivAt (weight m) (weightD m t) t := by
  have hbase : HasDerivAt (fun x : ℝ => 4 * x * (1 - x)) (4 - 8 * t) t := by
    have h := (((hasDerivAt_id t).const_mul 4).mul
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)))
    convert h using 1
    · rfl
    · dsimp
      ring
  change HasDerivAt (fun x : ℝ => (4 * x * (1 - x)) ^ m)
    ((m : ℝ) * (4 * t * (1 - t)) ^ (m - 1) * (4 - 8 * t)) t
  exact hbase.pow m

/-- The derivative polynomial is continuous. -/
theorem weightD_continuous (m : ℕ) : Continuous (weightD m) := by
  unfold weightD
  fun_prop

/-- The derivative is nonnegative on the left half. -/
theorem weightD_nonneg (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    0 ≤ weightD m t := by
  unfold weightD
  have ht1 : t ≤ 1 := by linarith [ht.2]
  have hb : 0 ≤ 4 * t * (1 - t) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith [ht.1])) (by linarith [ht.2])
  have hl : 0 ≤ 4 - 8 * t := by linarith [ht.2]
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hb _)) hl

/-- The derivative is nonpositive on the right half. -/
theorem weightD_nonpos (m : ℕ) {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    weightD m t ≤ 0 := by
  unfold weightD
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hb : 0 ≤ 4 * t * (1 - t) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith [ht.1])) (by linarith [ht.2])
  have hr : 4 - 8 * t ≤ 0 := by linarith [ht.1]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by positivity) (pow_nonneg hb _)) hr

/-- The absolute integral of the first derivative is exactly two. -/
theorem weightD_abs_integral {m : ℕ} (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, |weightD m t|) = 2 := by
  have hcont := weightD_continuous m
  have hleft : (∫ t in (0 : ℝ)..(1 / 2), weightD m t) = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => weight_hasDerivAt m t) (hcont.intervalIntegrable _ _)]
    rw [weight_half, (weight_endpoints hm).1]
    norm_num
  have hright : (∫ t in (1 / 2 : ℝ)..1, weightD m t) = -1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => weight_hasDerivAt m t) (hcont.intervalIntegrable _ _)]
    rw [weight_half, (weight_endpoints hm).2]
    norm_num
  have habsleft : (∫ t in (0 : ℝ)..(1 / 2), |weightD m t|) = 1 := by
    calc
      (∫ t in (0 : ℝ)..(1 / 2), |weightD m t|) =
          ∫ t in (0 : ℝ)..(1 / 2), weightD m t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        exact abs_of_nonneg (weightD_nonneg m ht)
      _ = 1 := hleft
  have habsright : (∫ t in (1 / 2 : ℝ)..1, |weightD m t|) = 1 := by
    calc
      (∫ t in (1 / 2 : ℝ)..1, |weightD m t|) =
          ∫ t in (1 / 2 : ℝ)..1, -weightD m t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        exact abs_of_nonpos (weightD_nonpos m ht)
      _ = 1 := by rw [intervalIntegral.integral_neg, hright]; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.abs.intervalIntegrable 0 (1 / 2)) (hcont.abs.intervalIntegrable (1 / 2) 1),
    habsleft, habsright]
  norm_num

end LeanLab.KadiriLumley2014.Task64
