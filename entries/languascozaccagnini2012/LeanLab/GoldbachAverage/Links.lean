module

public import Mathlib
public import LeanLab.GoldbachAverage.ZeroSums

/-!
Links between the cited error terms: Languasco-Zaccagnini's O(N log³ N) gives
Bhowmik-Schlage-Puchta's O(N log⁵ N), which gives Fujii's O((N log N)^{4/3}).
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
noncomputable section
namespace LeanLab.GoldbachAverage

/-- The error in the explicit formula. -/
def E (N : ℕ) : ℝ := ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖

theorem log_two_sq_ge : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by
  have := Real.log_two_gt_d9; nlinarith

theorem lz_to_bsp (h : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * N * Real.log N ^ 3) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * N * Real.log N ^ 5 := by
  obtain ⟨K, hK⟩ := h
  refine ⟨max K 0 / 0.48, fun N hN => le_trans (hK N hN) ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : 0.48 ≤ Real.log N ^ 2 := le_trans log_two_sq_ge (pow_le_pow_left₀ hL0.le hL 2)
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hX : 0 ≤ (N : ℝ) * Real.log N ^ 3 := by positivity
  calc K * N * Real.log N ^ 3 ≤ max K 0 * ((N : ℝ) * Real.log N ^ 3) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (by positivity)) (by positivity)
    _ = max K 0 / 0.48 * (0.48 * ((N : ℝ) * Real.log N ^ 3)) := by field_simp
    _ ≤ max K 0 / 0.48 * (Real.log N ^ 2 * ((N : ℝ) * Real.log N ^ 3)) := by gcongr
    _ = max K 0 / 0.48 * N * Real.log N ^ 5 := by ring

/-- `N log⁵ N ≤ 11^{11/3} (N log N)^{4/3}` for `N ≥ 2`, from `log N ≤ 11 N^{1/11}`. -/
theorem key_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) * Real.log N ^ 5 ≤ (11 : ℝ) ^ ((11 : ℝ) / 3) * ((N : ℝ) * Real.log N) ^ ((4 : ℝ) / 3) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  -- L ≤ 11 N^{1/11}
  have h1 : L ≤ 11 * (N : ℝ) ^ ((1 : ℝ) / 11) := by
    have := Real.log_le_rpow_div (x := (N : ℝ)) hNp.le (ε := 1 / 11) (by norm_num)
    rw [hLdef]; linarith [show (N : ℝ) ^ ((1 : ℝ) / 11) / (1 / 11) = 11 * (N : ℝ) ^ ((1 : ℝ) / 11) by ring]
  -- L^{11/3} ≤ 11^{11/3} N^{1/3}
  have h2 : L ^ ((11 : ℝ) / 3) ≤ (11 : ℝ) ^ ((11 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have := Real.rpow_le_rpow hL.le h1 (by norm_num : (0 : ℝ) ≤ 11 / 3)
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hNp.le] at this
    norm_num at this ⊢
    exact this
  -- assemble
  have e1 : (N : ℝ) * L ^ 5 = (N : ℝ) * L ^ ((4 : ℝ) / 3) * L ^ ((11 : ℝ) / 3) := by
    rw [mul_assoc, ← Real.rpow_add hL]; norm_num
  have e2 : ((N : ℝ) * L) ^ ((4 : ℝ) / 3) = (N : ℝ) ^ ((4 : ℝ) / 3) * L ^ ((4 : ℝ) / 3) :=
    Real.mul_rpow hNp.le hL.le
  have e3 : (N : ℝ) ^ ((4 : ℝ) / 3) = (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add hNp, Real.rpow_one]
  rw [e1, e2, e3]
  have hA : 0 ≤ (N : ℝ) * L ^ ((4 : ℝ) / 3) := by positivity
  calc (N : ℝ) * L ^ ((4 : ℝ) / 3) * L ^ ((11 : ℝ) / 3)
      ≤ (N : ℝ) * L ^ ((4 : ℝ) / 3) * ((11 : ℝ) ^ ((11 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left h2 hA
    _ = (11 : ℝ) ^ ((11 : ℝ) / 3) * ((N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 3) * L ^ ((4 : ℝ) / 3)) := by
        ring

theorem bsp_to_fujii (h : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * N * Real.log N ^ 5) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * ((N : ℝ) * Real.log N) ^ ((4 : ℝ) / 3) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨max K 0 * (11 : ℝ) ^ ((11 : ℝ) / 3), fun N hN => le_trans (hK N hN) ?_⟩
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hX : 0 ≤ (N : ℝ) * Real.log N ^ 5 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have := Real.log_nonneg this
    positivity
  calc K * N * Real.log N ^ 5 ≤ max K 0 * ((N : ℝ) * Real.log N ^ 5) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (by positivity)) (by positivity)
    _ ≤ max K 0 * ((11 : ℝ) ^ ((11 : ℝ) / 3) * ((N : ℝ) * Real.log N) ^ ((4 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left (key_bound N hN) hK0
    _ = _ := by ring

end LeanLab.GoldbachAverage
