module

public import LeanLab.KadiriLumley2014.OmegaIntegral

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 3 equation 2.12 and page 4 before equation 2.16.
Finite von Mangoldt expansion of the polynomial-smoothed psi average.
This does not assume an explicit formula over zeta zeros.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64

/-- A single nonnegative von Mangoldt step is monotone. -/
theorem vonMangoldt_step_mono (n : ℕ) :
    Monotone (fun y : ℝ => if (n : ℝ) ≤ y then ArithmeticFunction.vonMangoldt n else 0) := by
  intro y z hyz
  by_cases hny : (n : ℝ) ≤ y
  · simp [hny, hny.trans hyz]
  · by_cases hnz : (n : ℝ) ≤ z
    · simp [hny, hnz, ArithmeticFunction.vonMangoldt_nonneg]
    · simp [hny, hnz]

/-- A common finite cutoff expresses psi without a moving summation index. -/
theorem psi_eq_fixed_sum {N : ℕ} {y : ℝ} (hy : 0 ≤ y) (hN : y ≤ N) :
    Chebyshev.psi y = ∑ n ∈ Finset.Ioc 0 N,
      if (n : ℝ) ≤ y then ArithmeticFunction.vonMangoldt n else 0 := by
  classical
  rw [← Finset.sum_filter]
  unfold Chebyshev.psi
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hfN : ⌊y⌋₊ ≤ N := by simpa using Nat.floor_mono hN
  constructor
  · rintro ⟨hn0, hny⟩
    exact ⟨⟨hn0, hny.trans hfN⟩, (Nat.le_floor_iff hy).mp hny⟩
  · rintro ⟨⟨hn0, _⟩, hny⟩
    exact ⟨hn0, (Nat.le_floor_iff hy).mpr hny⟩

/-- The two arguments of psi stay below the same cutoff on the smoothing interval. -/
theorem psi_smoothing_cutoff {δ u X : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hX : 0 ≤ X)
    (hN : Real.exp u * X * (1 + δ) ≤ N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ X * (1 + δ * t) ∧ X * (1 + δ * t) ≤ N ∧
      0 ≤ Real.exp u * (X * (1 + δ * t)) ∧ Real.exp u * (X * (1 + δ * t)) ≤ N := by
  have hbase : 0 ≤ X * (1 + δ * t) :=
    mul_nonneg hX (by nlinarith [mul_nonneg hδ ht.1])
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu
  have hsmall : X * (1 + δ * t) ≤ Real.exp u * (X * (1 + δ * t)) := by nlinarith
  have hlarge : Real.exp u * (X * (1 + δ * t)) ≤ N := by
    have htδ : 1 + δ * t ≤ 1 + δ := by nlinarith [ht.2]
    have hm := mul_le_mul_of_nonneg_left htδ (mul_nonneg (Real.exp_nonneg u) hX)
    nlinarith
  exact ⟨hbase, hsmall.trans hlarge, mul_nonneg (Real.exp_nonneg u) hbase, hlarge⟩

/-- The psi average is an exact finite sum of weighted von Mangoldt steps.
Only a finite integral interchange is used. -/
theorem psiAverage_eq_finite_sum (m : ℕ) {δ u X : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hX : 0 ≤ X)
    (hN : Real.exp u * X * (1 + δ) ≤ N) :
    psiAverage m δ u X =
      (∑ n ∈ Finset.Ioc 0 N, ∫ t in (0 : ℝ)..1,
        ((if (n : ℝ) ≤ Real.exp u * (X * (1 + δ * t)) then ArithmeticFunction.vonMangoldt n else 0) -
          (if (n : ℝ) ≤ X * (1 + δ * t) then ArithmeticFunction.vonMangoldt n else 0)) * weight m t) /
        (∫ t in (0 : ℝ)..1, weight m t) := by
  classical
  unfold psiAverage
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ n ∈ Finset.Ioc 0 N,
        ((if (n : ℝ) ≤ Real.exp u * (X * (1 + δ * t)) then ArithmeticFunction.vonMangoldt n else 0) -
          (if (n : ℝ) ≤ X * (1 + δ * t) then ArithmeticFunction.vonMangoldt n else 0)) * weight m t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      obtain ⟨hL0, hLN, hU0, hUN⟩ := psi_smoothing_cutoff hδ hu hX hN ht
      dsimp only
      rw [psi_eq_fixed_sum hU0 hUN, psi_eq_fixed_sum hL0 hLN,
        ← Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by
      apply intervalIntegral.integral_finsetSum
      intro n _
      exact weighted_difference_integrable (vonMangoldt_step_mono n) m hδ (Real.exp_nonneg u) hX

end LeanLab.KadiriLumley2014.Task301
