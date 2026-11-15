module

public import LeanLab.Tolev2009.Decomp346a
public import LeanLab.Tolev2009.Decomp346b
public import LeanLab.Tolev2009.Decomp346c
public import LeanLab.Tolev2009.Decomp355c
public import LeanLab.Tolev2009.Decomp314c

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://arxiv.org/abs/0803.0831 pages 7 to 12 and 18 to 19.
These exact assemblies reuse the proved task346 and task355 supplies.
No inherited leaf file is changed.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.MajorArc341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction
open LeanLab.Tolev2009.Decomp286a LeanLab.Tolev2009.Decomp314a
open LeanLab.Tolev2009.Decomp314b LeanLab.Tolev2009.Decomp314c

/-- Exact progression replacement from the three proved remainder means.
Halupczok 2008 pages 7 to 11, the O1, O2 and O3 assembly. -/
theorem progression_replacement :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => RM (Qof A N) (τof A N) k l N -
            model (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨Ng, hg⟩ := rational_arc_expansion A hA
  obtain ⟨C₁, N₁, h₁⟩ := Decomp346a.linear_remainder_mean A hA l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := Decomp346b.quadratic_remainder_mean A hA l₃ hl₃
  obtain ⟨C₃, N₃, h₃⟩ := Decomp346c.cubic_remainder_mean A hA l₃ hl₃
  refine ⟨C₁ + C₂ + C₃, max Ng (max N₁ (max N₂ N₃)), ?_⟩
  intro lam hlam N hodd hN
  have hNg : Ng ≤ N := (le_max_left _ _).trans hN
  have hNs := (le_max_right _ _).trans hN
  have hN₁ := (le_max_left _ _).trans hNs
  have hNs' := (le_max_right _ _).trans hNs
  have hN₂ := (le_max_left _ _).trans hNs'
  have hN₃ := (le_max_right _ _).trans hNs'
  simp_rw [hg N hNg]
  have hs := EF_add_le
    (fun k l => errorTerm 1 (Qof A N) (τof A N) k l N +
      errorTerm 2 (Qof A N) (τof A N) k l N)
    (fun k l => errorTerm 3 (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N
  have ht := EF_add_le
    (fun k l => errorTerm 1 (Qof A N) (τof A N) k l N)
    (fun k l => errorTerm 2 (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N
  have hb₁ := h₁ lam hlam N hodd hN₁
  have hb₂ := h₂ lam hlam N hodd hN₂
  have hb₃ := h₃ lam hlam N hodd hN₃
  nlinarith

/-- Exact singular series tail from the proved coefficient moment and summability.
Halupczok 2008 page 12 e1 and pages 18 to 19. -/
theorem singular_series_tail :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => truncatedMain (Qof A N) k l N -
            M singSeries k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, Nm, hC, hm⟩ := Decomp355b.coefficient_mass_mean A hA l₃ hl₃
  obtain ⟨Ng, hg⟩ := integral_cutoff_regime A
  refine ⟨C, max Nm Ng, ?_⟩
  intro lam hlam N hodd hN
  have hNm := (le_max_left _ _).trans hN
  have hNg := (le_max_right _ _).trans hN
  have hL := (hg N hNg).1
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  have he : ∀ k l, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      |truncatedMain (Qof A N) k l N - M singSeries k l N| ≤
        (1 * (N : ℝ) ^ 2 / Qof A N) * coefficientMass k l N := by
    intro k l hk hl
    simpa only [one_mul] using scalar_series_tail (Qof A N) k l N hQ hk hl
      (Decomp355a.weighted_coeff_summable k l N hk hl hodd)
  simpa only [one_mul] using mean_of_mass_bound _ A 1 C lam l₃ N hA hL
    (by norm_num) hC hlam (hm N hodd hNm) he

/-- The full major arc estimate from the three proved exact components.
Halupczok 2008 pages 7 to 12 and 18 to 19. -/
theorem major_arc_leaf : BoundE1 := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, h₁⟩ := progression_replacement A hA l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := Decomp355c.singular_integral_error A hA l₃ hl₃
  obtain ⟨C₃, N₃, h₃⟩ := singular_series_tail A hA l₃ hl₃
  refine ⟨C₁ + C₂ + C₃, max (max N₁ N₂) N₃, fun lam hlam N hodd hN => ?_⟩
  have hN₁ : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN₂ : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans hN
  have he : (fun k l => RM (Qof A N) (τof A N) k l N - M singSeries k l N) =
      fun k l => ((RM (Qof A N) (τof A N) k l N - model (Qof A N) (τof A N) k l N) +
        (model (Qof A N) (τof A N) k l N - truncatedMain (Qof A N) k l N)) +
        (truncatedMain (Qof A N) k l N - M singSeries k l N) := by
    funext k l
    ring
  unfold E1
  rw [he]
  refine (EF_add_le _ _ _ _ _ _).trans ?_
  have hs := EF_add_le
    (fun k l => RM (Qof A N) (τof A N) k l N - model (Qof A N) (τof A N) k l N)
    (fun k l => model (Qof A N) (τof A N) k l N - truncatedMain (Qof A N) k l N)
    lam l₃ (10 ^ 4 * A) N
  have hb₁ := h₁ lam hlam N hodd hN₁
  have hb₂ := h₂ lam hlam N hodd hN₂
  have hb₃ := h₃ lam hlam N hodd hN₃
  nlinarith

end LeanLab.Tolev2009.MajorArc341
