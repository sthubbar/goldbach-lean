module

public import LeanLab.Tolev2009.Decomp355b

/-!
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 11 to 12 and 18 to 19.
The exact parent uses the new finite coefficient supply.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp355c
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a LeanLab.Tolev2009.Decomp314b

/-- Exact supply for the sealed finite singular integral error statement.
Derived from the local prime product leaf only.
The finite gcd average and all integral estimates are proved. -/
theorem singular_integral_error :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => model (Qof A N) (τof A N) k l N -
            truncatedMain (Qof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨c, hc, he⟩ := geometric_integral_error
  obtain ⟨C, Nm, hC, hm⟩ := Decomp355b.coefficient_mass_mean A hA l₃ hl₃
  obtain ⟨Ng, hg⟩ := integral_cutoff_regime A
  refine ⟨c * C, max Nm Ng, ?_⟩
  intro lam hlam N hodd hN
  have hNm := (le_max_left _ _).trans hN
  have hNg := (le_max_right _ _).trans hN
  obtain ⟨hL, hτ, hNτ⟩ := hg N hNg
  apply mean_of_mass_bound _ A c C lam l₃ N hA hL hc hC hlam (hm N hodd hNm)
  intro k l hk hl
  have hQ : 0 < Qof A N := Real.rpow_pos_of_pos (by linarith) _
  have ht := finite_integral_contraction (Qof A N) (τof A N) c k l N hQ.le hc
    (Decomp355a.weighted_coeff_summable k l N hk hl hodd)
    (fun q hq => he N q (τof A N) (mem_Icc.mp hq).1 hτ hNτ)
  have hid : c * (τof A N) ^ 2 * Qof A N = c * (N : ℝ) ^ 2 / Qof A N := by
    unfold τof
    field_simp
  simpa only [hid] using ht

end LeanLab.Tolev2009.Decomp355c
