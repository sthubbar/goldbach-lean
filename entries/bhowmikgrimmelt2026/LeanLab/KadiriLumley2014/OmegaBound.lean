module

public import Mathlib

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 3, equations 2.10 and 2.11.
Journal INTEGERS 14 A61 page 4, equations 10 and 11.
This is the elementary numerical bound after the cited Costa estimate.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- A rational bound for the small negative exponential in equation 2.10. -/
theorem exp_neg_38_sixth_lt : Real.exp (-(38 : ℝ) / 6) < 0.00178 := by
  have hc : (1 + (1 / 3 : ℝ) + (1 / 3 : ℝ) ^ 2 / 2 + (1 / 3 : ℝ) ^ 3 / 6) ≤
      Real.exp (1 / 3) := by
    simpa [Finset.sum_range_succ, Nat.factorial] using
      Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) 4
  have hp : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := by
    gcongr
    exact Real.exp_one_gt_d9.le
  have he : Real.exp (38 / 6 : ℝ) = Real.exp 1 ^ 6 * Real.exp (1 / 3) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  have hlarge : (1 / 0.00178 : ℝ) < Real.exp (38 / 6) := by
    rw [he]
    have hmul := mul_le_mul hp hc (by norm_num) (by positivity : 0 ≤ Real.exp 1 ^ 6)
    norm_num at hmul ⊢
    linarith
  have hneg : Real.exp (-(38 : ℝ) / 6) = 1 / Real.exp (38 / 6) := by
    rw [neg_div, Real.exp_neg, one_div]
  rw [hneg]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  nlinarith

/-- X to the power minus one sixth is at most the rational enclosure. -/
theorem rpow_neg_sixth_le {X : ℝ} (hX : Real.exp 38 ≤ X) :
    X ^ (-(1 : ℝ) / 6) ≤ 0.00178 := by
  have h := Real.rpow_le_rpow_of_nonpos (Real.exp_pos 38) hX
    (by norm_num : -(1 : ℝ) / 6 ≤ 0)
  rw [← Real.exp_mul] at h
  exact h.trans (by convert exp_neg_38_sixth_lt.le using 1; norm_num)

/-- Uniform elementary bound for the Costa error coefficient. -/
theorem omega_coefficient_lt {u δ X : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 0.0001)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hX : Real.exp 38 ≤ X) :
    Real.sqrt (1 + δ) *
      (1.001 * Real.exp (u / 2) - 0.999 +
        X ^ (-(1 : ℝ) / 6) * (1 + δ) ^ (-(1 : ℝ) / 6) *
          (Real.exp (u / 3) - 1)) < 2.05022 * 10 ^ (-3 : ℤ) := by
  have hs : Real.sqrt (1 + δ) ≤ 1.00005 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith
  have h2 : Real.exp (u / 2) ≤ 1 / (1 - 0.00005) := by
    calc
      Real.exp (u / 2) ≤ Real.exp 0.00005 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / (1 - 0.00005) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have h3 : Real.exp (u / 3) - 1 ≤ 1 / (1 - (1 / 30000 : ℝ)) - 1 := by
    have he := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 30000) (by norm_num : (1 / 30000 : ℝ) < 1)
    have hm : Real.exp (u / 3) ≤ Real.exp (1 / 30000) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h3n : 0 ≤ Real.exp (u / 3) - 1 := by
    have := Real.one_le_exp_iff.mpr (by linarith : 0 ≤ u / 3)
    linarith
  have hx := rpow_neg_sixth_le hX
  have hdp : (1 + δ) ^ (-(1 : ℝ) / 6) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
      (by linarith : (1 : ℝ) ≤ 1 + δ) (by norm_num : -(1 : ℝ) / 6 ≤ 0)
    simpa using h
  have hxpos : 0 ≤ X ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg
    (le_trans (Real.exp_pos 38).le hX) _
  have hdp0 : 0 ≤ (1 + δ) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by linarith) _
  have hprod : X ^ (-(1 : ℝ) / 6) * (1 + δ) ^ (-(1 : ℝ) / 6) ≤ 0.00178 := by
    nlinarith
  have hterm := mul_le_mul hprod h3 h3n (by norm_num : (0 : ℝ) ≤ 0.00178)
  have hbr : 1.001 * Real.exp (u / 2) - 0.999 +
      X ^ (-(1 : ℝ) / 6) * (1 + δ) ^ (-(1 : ℝ) / 6) *
        (Real.exp (u / 3) - 1) ≤
      1.001 / (1 - 0.00005) - 0.999 + 0.00178 * (1 / (1 - (1 / 30000 : ℝ)) - 1) := by
    linarith
  have hbr0 : 0 ≤ 1.001 * Real.exp (u / 2) - 0.999 +
      X ^ (-(1 : ℝ) / 6) * (1 + δ) ^ (-(1 : ℝ) / 6) *
        (Real.exp (u / 3) - 1) := by
    have he2 : 1 ≤ Real.exp (u / 2) := Real.one_le_exp_iff.mpr (by linarith)
    have ht0 := mul_nonneg (mul_nonneg hxpos hdp0) h3n
    nlinarith
  have hbound := mul_le_mul hs hbr hbr0 (by norm_num : (0 : ℝ) ≤ 1.00005)
  norm_num at hbound ⊢
  nlinarith

end LeanLab.KadiriLumley2014.Task64
