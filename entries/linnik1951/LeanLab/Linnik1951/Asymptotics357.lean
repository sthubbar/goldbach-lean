module

public import LeanLab.Linnik1951.Decomp280b

/-!
P0093 page 166. Logarithmic absorption of a power saving.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Filter
open scoped Topology

/-- P0093 page 166 after equation 9.3. Every positive power saving absorbs
any fixed logarithmic power. This states only the real asymptotic step. -/
theorem power_saving_negligible357 (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) ^ (1 - δ) * Real.log N ^ k ≤ ε * N := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).def (div_pos hε hC)
  have hn : ∀ᶠ (N : ℕ) in atTop, ‖Real.log (N : ℝ) ^ (k : ℝ)‖ ≤
      (ε / C) * ‖(N : ℝ) ^ δ‖ := tendsto_natCast_atTop_atTop.eventually hh
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hn
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have h := hN0 N (by have := le_max_right 1 N0; omega)
  simp only [Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog k), abs_of_pos (Real.rpow_pos_of_pos hpos δ)] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ C * (N : ℝ) ^ (1 - δ) by positivity)
  have hp : (N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ = N := by
    rw [← Real.rpow_add hpos]
    simp
  calc
    _ ≤ C * (N : ℝ) ^ (1 - δ) * (ε / C * (N : ℝ) ^ δ) := hmul
    _ = ε * ((N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ) := by field_simp
    _ = _ := by rw [hp]

end LeanLab.Linnik1951
