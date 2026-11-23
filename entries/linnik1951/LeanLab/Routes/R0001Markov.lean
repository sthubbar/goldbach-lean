module

public import LeanLab.Routes.R0001Averaged

/-!
Route R-0001 salvage, U-0993 continued: the exceptional set skeleton step.
The number of residues n where the minor arc part of the binary count is at least T is at most
the minor arc L4 mass over T². This is the step every exceptional set paper, Montgomery-Vaughan
1975 onward, takes on the minor arcs. AI wrote this Lean code. Goldbach is open.
-/

@[expose] public section

open ZMod Finset

namespace LeanLab.Routes.R0001

variable {N : ℕ} [NeZero N]

/-- The minor arc part of the binary count at `n`, unnormalized. -/
noncomputable def minorPart (Φ : ZMod N → ℂ) (m : Finset (ZMod N)) (n : ZMod N) : ℂ :=
  ∑ k ∈ m, 𝓕 Φ k ^ 2 * (stdAddChar (n * k) : ℂ)

/-- Markov plus the averaged identity, for `T ≥ 0`; for negative `T` the bound is false: `#{n : |minorPart n| ≥ T} · T² ≤ N ∑_{k∈m} |S(k)|⁴`. -/
theorem card_large_minor_le (Φ : ZMod N → ℂ) (m : Finset (ZMod N)) (T : ℝ) (hT : 0 ≤ T) :
    ((univ.filter fun n => T ≤ ‖minorPart Φ m n‖).card : ℝ) * T ^ 2
      ≤ (N : ℝ) * ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 := by
  classical
  rw [← averaged_minor Φ m]
  have h1 : ((univ.filter fun n => T ≤ ‖minorPart Φ m n‖).card : ℝ) * T ^ 2
      ≤ ∑ n ∈ univ.filter (fun n => T ≤ ‖minorPart Φ m n‖), ‖minorPart Φ m n‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    exact pow_le_pow_left₀ hT (Finset.mem_filter.1 hn).2 2
  refine h1.trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n _ _ => ?_
  positivity

/-- Vacuity test: with `T = 0` the left side is `N · 0 = 0`, so the bound holds trivially;
the content is for `T` of the size of the main term. -/
example (Φ : ZMod N → ℂ) (m : Finset (ZMod N)) :
    ((univ.filter fun n => (0 : ℝ) ≤ ‖minorPart Φ m n‖).card : ℝ) * 0 ^ 2
      ≤ (N : ℝ) * ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 := card_large_minor_le Φ m 0 le_rfl

end LeanLab.Routes.R0001
