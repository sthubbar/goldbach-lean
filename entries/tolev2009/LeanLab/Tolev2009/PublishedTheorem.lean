module

public import LeanLab.Tolev2009.FinalReduction
public import LeanLab.Tolev2009.SeriesIdentification

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009 page 2 display 5 and Halupczok 2008 pages 7 and 11.
The exact source links and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.PublishedTheorem

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.SeriesIdentification LeanLab.Tolev2009.FinalReduction

/-- Only reduced residues occur in E star, so the series identification applies to every summand. -/
theorem Estar_eq_publishedSeries (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    Estar singSeries lam l₃ B N = Estar halupczokSeries lam l₃ B N := by
  unfold Estar inner
  refine sum_congr rfl fun k₁ hk₁ => sum_congr rfl fun k₂ hk₂ => ?_
  congr 1
  funext l₁
  congr 1
  funext hl₁
  congr 1
  funext l₂
  congr 1
  funext hl₂
  congr 1
  refine sum_congr rfl fun k₃ hk₃ => ?_
  have h1 : 1 ≤ k₁ := (mem_Icc.mp hk₁).1
  have h2 : 1 ≤ k₂ := (mem_Icc.mp hk₂).1
  have h3 : 1 ≤ k₃ := (mem_Icc.mp (mem_filter.mp hk₃).1).1
  have hc1 : Nat.Coprime l₁ k₁ := (mem_filter.mp hl₁).2
  have hc2 : Nat.Coprime l₂ k₂ := (mem_filter.mp hl₂).2
  have hc3 : Nat.Coprime l₃ k₃ := (mem_filter.mp hk₃).2.symm
  have hS := singSeries_eq_halupczokSeries ![k₁, k₂, k₃] ![l₁, l₂, l₃] N
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
  simp only [Δ, M, hS]

/-- The explicit faithful main theorem transfers to the printed singular series.
Derived from MainTheorem. -/
theorem published_of_main (h : MainTheorem) : TheTheorem halupczokSeries := by
  intro A hA
  obtain ⟨B, hB, hb⟩ := h A hA
  refine ⟨B, hB, fun l₃ hl₃ => ?_⟩
  obtain ⟨C, N₀, hc⟩ := hb l₃ hl₃
  refine ⟨C, N₀, fun lam hlam N hodd hN => ?_⟩
  rw [← Estar_eq_publishedSeries]
  exact hc lam hlam N hodd hN

/-- Display 5 with the literal cited singular series.
Derived from display 9 and the supremum half of display 12 only. -/
theorem publishedTheorem_of_display9_sup12 (h9 : BoundE1) (h12 : Sup12Uniform) :
    TheTheorem halupczokSeries :=
  published_of_main (mainTheorem_of_display9_sup12 h9 h12)

end LeanLab.Tolev2009.PublishedTheorem
