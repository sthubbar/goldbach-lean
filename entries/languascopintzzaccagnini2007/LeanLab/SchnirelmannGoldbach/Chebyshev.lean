module

public import Mathlib

/-!
AI-written Lean code by Claude, 2026-10-16.
Chebyshev lower bound for the prime counting function, derived from Mathlib's
`Chebyshev.pi_ge`.
-/

@[expose] public section

open Real
namespace LeanLab.SchnirelmannGoldbach
/-- Chebyshev lower bound in the form needed for S3. -/
theorem pi_lower : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    c * m / Real.log m ≤ (Nat.primeCounting m : ℝ) := by
  have hl2 := Real.log_two_gt_d9
  refine ⟨Real.log 2 / 2, by positivity, 100, fun m hm => ?_⟩
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  refine le_trans ?_ (Chebyshev.pi_ge m)
  apply div_le_div_of_nonneg_right _ hlogm.le
  -- log (m+1) - log 8 ≤ (m+1)/8 - 1
  have h1 : Real.log ((m + 1) / 8) ≤ (m + 1) / 8 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h8] at h1
  nlinarith
end LeanLab.SchnirelmannGoldbach
