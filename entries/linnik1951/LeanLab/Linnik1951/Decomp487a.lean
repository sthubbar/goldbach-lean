module

public import LeanLab.Linnik1951.SPLIT_central_kernel_mass442
public import LeanLab.Linnik1951.Decomp376b
public import LeanLab.Linnik1951.SPLIT1622_mellin

/-!
P0093 route supplies for Assembly376.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 158 before equation 4.8. The abstract central estimate uses the proved absolute kernel mass. No character transfer or GRH is used. -/
theorem lemma2_central_proved487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
          ‖mellinU1622 N M α‖ ≤ B * (N : ℝ) / Real.sqrt R * Real.log N ^ 3 := by
  obtain ⟨C, hC, N0, hc⟩ := central_kernel_mass442_split
  refine ⟨(1 / (2 * Real.pi)) * B0 * C, by positivity, max 1 N0, ?_⟩
  intro N hN R hR1 hR M hM α hα
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hRp : 0 < R := by linarith
  have hRN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = N := Real.rpow_one _
  obtain ⟨hI, hm⟩ := hc N (by omega) α hα
  have hl : 0 ≤ Real.log N ^ 3 := pow_nonneg (Real.log_nonneg hNr) 3
  calc
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mellin_kernel_domination442 N α B0 hB0.le M hM hI
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * Real.sqrt N * Real.log N ^ 3) := by
      gcongr
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * ((N : ℝ) / Real.sqrt R) * Real.log N ^ 3) := by
      gcongr
      exact sqrt_scale442 N R hNp hRp hRN
    _ = _ := by ring

end LeanLab.Linnik1951
