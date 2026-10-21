module

public import LeanLab.LZCesaroShort.Lemma3Parseval

/-!
# Fourier coefficients of absolutely convergent series on `[-1/2, 1/2]`

Lab file, unit U-6103, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN. The circle method step of P0058 Section 4, eq. (26) and (19):

* `coef_tsum`: `∫_{-1/2}^{1/2} (Σ' C m e(mβ)) e(-nβ) dβ = C n` for absolutely summable `C`;
* `coef_mul_tsum`: `∫_{-1/2}^{1/2} (Σ' a m e(mβ)) (Σ' b k e(kβ)) e(-nβ) dβ = Σ_{i + j = n} a i b j`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher

lemma e_mul_e_neg (m n : ℕ) (β : ℝ) : e (m * β) * e (-(n * β)) = e (((m : ℤ) - n : ℤ) * β) := by
  rw [← e_add]; congr 1; push_cast; ring

/-- Orthogonality for a finite sum. -/
lemma coef_finset (C : ℕ → ℂ) (M n : ℕ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), (∑ m ∈ range M, C m * e (m * β)) * e (-(n * β))
      = if n < M then C n else 0 := by
  simp_rw [sum_mul, mul_assoc, e_mul_e_neg]
  have hsw : ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ∑ m ∈ range M, C m * e ((((m : ℤ) - n : ℤ) : ℝ) * β)
      = ∑ m ∈ range M, ∫ β in (-(1 / 2 : ℝ))..(1 / 2), C m * e ((((m : ℤ) - n : ℤ) : ℝ) * β) :=
    intervalIntegral.integral_finset_sum (fun m _ =>
      (continuous_const.mul (continuous_e_mul _)).intervalIntegrable _ _)
  rw [hsw]
  simp_rw [intervalIntegral.integral_const_mul, integral_e_int]
  split_ifs with h
  · rw [sum_eq_single n]
    · simp
    · intro m _ hmn; simp [sub_eq_zero, hmn]
    · intro hn; exact absurd (mem_range.mpr h) hn
  · refine sum_eq_zero fun m hm => ?_
    have : m ≠ n := by rintro rfl; exact h (mem_range.mp hm)
    simp [sub_eq_zero, this]

/-- **Orthogonality** for an absolutely convergent series. -/
theorem coef_tsum (C : ℕ → ℂ) (hC : Summable (fun m => ‖C m‖)) (n : ℕ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), (∑' m, C m * e (m * β)) * e (-(n * β)) = C n := by
  set T := ∑' m, ‖C m‖ with hT
  have hsumm : ∀ β : ℝ, Summable (fun m => C m * e (m * β)) := fun β =>
    Summable.of_norm_bounded hC (fun m => by rw [norm_mul, norm_e, mul_one])
  have hcont : ∀ M : ℕ, Continuous fun β : ℝ => (∑ m ∈ range M, C m * e (m * β)) * e (-(n * β)) :=
    fun M => (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_e_mul _)).mul
      (continuous_e.comp (continuous_const.mul continuous_id).neg)
  have hlim : Tendsto (fun M : ℕ => ∫ β in (-(1 / 2 : ℝ))..(1 / 2),
      (∑ m ∈ range M, C m * e (m * β)) * e (-(n * β))) atTop
      (𝓝 (∫ β in (-(1 / 2 : ℝ))..(1 / 2), (∑' m, C m * e (m * β)) * e (-(n * β)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => T)
      (Eventually.of_forall fun M => (hcont M).aestronglyMeasurable)
      (Eventually.of_forall fun M => ae_of_all _ fun β _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun β _ => ?_)
    · rw [norm_mul, norm_e, mul_one]
      calc ‖∑ m ∈ range M, C m * e (m * β)‖ ≤ ∑ m ∈ range M, ‖C m * e (m * β)‖ := norm_sum_le _ _
        _ = ∑ m ∈ range M, ‖C m‖ := by simp_rw [norm_mul, norm_e, mul_one]
        _ ≤ T := hC.sum_le_tsum _ (fun m _ => norm_nonneg _)
    · exact ((hsumm β).hasSum.tendsto_sum_nat).mul_const _
  have heq : (fun M : ℕ => ∫ β in (-(1 / 2 : ℝ))..(1 / 2),
      (∑ m ∈ range M, C m * e (m * β)) * e (-(n * β))) = fun M => if n < M then C n else 0 :=
    funext fun M => coef_finset C M n
  rw [heq] at hlim
  have hev : Tendsto (fun M : ℕ => if n < M then C n else 0) atTop (𝓝 (C n)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop n] with M hM
    simp [hM]
  exact tendsto_nhds_unique hlim hev

/-- The product of two absolutely convergent series is the Cauchy product series. -/
lemma tsum_mul_tsum_e (a b : ℕ → ℂ) (ha : Summable (fun m => ‖a m‖))
    (hb : Summable (fun m => ‖b m‖)) (β : ℝ) :
    (∑' m, a m * e (m * β)) * (∑' k, b k * e (k * β))
      = ∑' s, (∑ p ∈ antidiagonal s, a p.1 * b p.2) * e (s * β) := by
  have ha' : Summable (fun m => ‖a m * e (m * β)‖) := by simp_rw [norm_mul, norm_e, mul_one]; exact ha
  have hb' : Summable (fun m => ‖b m * e (m * β)‖) := by simp_rw [norm_mul, norm_e, mul_one]; exact hb
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha' hb']
  refine tsum_congr fun s => ?_
  rw [sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  have : e (s * β) = e (p.1 * β) * e (p.2 * β) := by
    rw [← e_add, ← hp]; congr 1; push_cast; ring
  rw [this]; ring

/-- **The convolution coefficient.** -/
theorem coef_mul_tsum (a b : ℕ → ℂ) (ha : Summable (fun m => ‖a m‖))
    (hb : Summable (fun m => ‖b m‖)) (n : ℕ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2),
        (∑' m, a m * e (m * β)) * (∑' k, b k * e (k * β)) * e (-(n * β))
      = ∑ p ∈ antidiagonal n, a p.1 * b p.2 := by
  simp_rw [tsum_mul_tsum_e a b ha hb]
  exact coef_tsum _ (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb) n

/-- Continuity of an absolutely convergent series in `β`. -/
lemma continuous_tsum_e (C : ℕ → ℂ) (hC : Summable (fun m => ‖C m‖)) :
    Continuous (fun β : ℝ => ∑' m, C m * e (m * β)) :=
  continuous_tsum (fun m => continuous_const.mul (continuous_e_mul _)) hC
    (fun m β => by rw [norm_mul, norm_e, mul_one])

end LeanLab.LZCesaroShort

