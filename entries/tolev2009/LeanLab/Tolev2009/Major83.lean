module

public import LeanLab.Tolev2009.Faithful
public import LeanLab.Tolev2009.MajorArc341

/-!
AI wrote this Lean code. Claude, route burst 2026-11-12.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669, page 4 display 9.
Tolev 1999 pages 76 to 82 displays 23 to 49.
Halupczok 2008 pages 7 to 12 and 18 to 19, proof of Theorem 3.

Split of `Decomp83.major_arc_leaf` into three faithful pieces of the published proof,
placed upstream of `Decomp83` so that `Decomp83` can import them.
The definitions `geometric`, `arcIntegral`, `model` and `truncatedMain` below are
copies, term for term, of the same names in `Decomp286a.lean`, which cannot be imported
here because it imports `Decomp83`. The downstream file `MajorArc341.lean` proves the
corresponding statements over the `Decomp286a` copies with clean axioms.
PROVE PASS 2026-11-12: `Decomp286a` now imports `PublishedTheorem` instead of `Decomp83`,
it used no declaration of `Decomp83`, so this file can import `MajorArc341` without a
cycle. The three leaves below are now proved from the downstream supplies, the copied
definitions agreeing by unfolding. Axioms: propext, Classical.choice, Quot.sound.
-/

@[expose] public section

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.Major83

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-- The finite geometric sum M of Halupczok page 7, over 1 through N. -/
noncomputable def geometric (N : ℕ) (β : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 N, ee (β * m)

/-- Halupczok page 11, the singular integral at radius 1 over q tau. -/
noncomputable def arcIntegral (τ : ℝ) (N q : ℕ) : ℂ :=
  ∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
    geometric N β ^ 3 * ee (-((N : ℝ) * β))

/-- Halupczok page 8 H, the major arc model after progression replacement. -/
noncomputable def model (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (∑ q ∈ Icc 1 ⌊Q⌋₊,
    ssTerm k l N q / (∏ i : Fin 3, ((k i).totient : ℂ)) * arcIntegral τ N q).re

/-- Halupczok page 12, the finite singular series contribution before e1. -/
noncomputable def truncatedMain (Q : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * (∑ q ∈ Icc 1 ⌊Q⌋₊, ssTerm k l N q).re /
    (2 * (k 0).totient * (k 1).totient * (k 2).totient)

/-- Tolev 1999 pages 77 to 78 displays 27 to 34 and pages 81 to 82 display 49.
Halupczok 2008 pages 8 to 11, estimates O1, O2 and O3.
Replacing the prime exponential sums on each major arc by the model, averaged over the
moduli as in Tolev 2009 page 4 display 9. PROVED 2026-11-12 PROVE PASS from
`MajorArc341.progression_replacement` over the `Decomp286a` copy of `model`. -/
theorem progression_replacement :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => RM (Qof A N) (τof A N) k l N -
            model (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  exact MajorArc341.progression_replacement A hA l₃ hl₃

/-- Tolev 1999 page 78 displays 34 to 36 and page 81 display 48.
Halupczok 2008 pages 11 to 12 and 19, the error e2.
Each finite singular integral is replaced by N squared over two. PROVED 2026-11-12 PROVE PASS from `Decomp355c.singular_integral_error`. -/
theorem singular_integral_error :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => model (Qof A N) (τof A N) k l N -
            truncatedMain (Qof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  exact Decomp355c.singular_integral_error A hA l₃ hl₃

/-- Tolev 1999 page 79 display 40 and pages 80 to 81 displays 45 to 47.
Halupczok 2008 pages 12 and 18 to 19, the error e1.
Only the tail beyond Q of the singular series is estimated. PROVED 2026-11-12 PROVE PASS from `MajorArc341.singular_series_tail`. -/
theorem singular_series_tail :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => truncatedMain (Qof A N) k l N -
            M singSeries k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  exact MajorArc341.singular_series_tail A hA l₃ hl₃

/-- Tolev 2009 page 4 display 9 from the three errors above, by subadditivity of EF
and a common threshold. Fully proved. -/
theorem major_arc_of_three : BoundE1 := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, h₁⟩ := progression_replacement A hA l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := singular_integral_error A hA l₃ hl₃
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

end LeanLab.Tolev2009.Major83
