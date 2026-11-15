module

public import LeanLab.Tolev2009.BlockEstimates
public import LeanLab.Tolev2009.Displays19to20
public import LeanLab.Tolev2009.DivisorMoment

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.MinorArcBound

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Displays19to20
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.BlockEstimates

/-- The elementary signed divisor moment, with no cited input. -/
theorem divisorFourthMoment (N : ℕ) (hL : 1 ≤ Real.log N) :
    DivisorFourthMoment N (2 ^ 16) := DivisorMoment.signed_fourth_moment N hL

/-- The singleton and mixed zero terms have exactly the same mass as ordinary blocks of their scales. -/
theorem W0_eq_Wzero (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) :
    W0 a Q τ lam l₃ K₃ N i j = Wzero a Q τ lam l₃ K₃ N (scale i) (scale j) := by
  have hz : ∀ x y, (nSet N x y).filter (fun n => n = 0) = {0} := by
    intro x y
    ext n
    simp only [nSet, mem_filter, mem_Icc, mem_singleton]
    constructor
    · intro h; exact h.2
    · intro h; subst n; simp
  simp only [W0, Wzero, hz, sum_singleton, sum_const, nsmul_eq_mul, block_card, Nat.card_Ioc]
  rw [show 2 * scale i - scale i = scale i by omega, show 2 * scale j - scale j = scale j by omega]

/-- Display 20 without the elementary divisor moment hypothesis.
Derived from Display12 only. -/
theorem display20_of_display12 (A cSup cL2 Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ)
    (s t : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) (ht : ∀ k ∈ t, 1 ≤ k)
    (hL : 1 ≤ Real.log N) (hcSup : 0 ≤ cSup) (hcL2 : 0 ≤ cL2)
    (h12 : Display12 A cSup cL2 Q τ lam l₃ K₃ N) :
    starSum (-1 / τ) Q τ lam l₃ K₃ N s t ≤
      Real.sqrt (2 ^ 16 : ℝ) * cSup * Real.sqrt cL2 * (N : ℝ) ^ 2 * Real.log N ^ (400 - 4 * A) :=
  display20_sets _ _ _ _ _ _ _ _ _ _ _ _ hs ht hL hcSup hcL2 (by positivity) h12
    (divisorFourthMoment N hL)

/-- The minor arc sum from the paper's display 12, with no display 10, 19 or 20 hypothesis.
Derived from Display12 only. -/
theorem E2_bound_of_display12 (lam : ℕ → ℝ) (l₃ N : ℕ) (A cSup cL2 : ℝ)
    (hA : 10 ^ 4 ≤ A) (hL : 1 ≤ Real.log N) (hcSup : 0 ≤ cSup) (hcL2 : 0 ≤ cL2)
    (h12 : Display12 A cSup cL2 (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N) :
    E2 lam l₃ A N ≤ dyadicConstant * Real.sqrt 8 *
      (Real.sqrt cL2 + Real.sqrt (Real.sqrt (2 ^ 16 : ℝ) * cSup * Real.sqrt cL2)) *
      (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  have hdy : 0 ≤ dyadicConstant := sq_nonneg _
  let H := cutoff (10 ^ 4 * A) N
  by_cases hH : H = 0
  · have he : E2 lam l₃ A N = 0 := by
      simp only [E2, EF]
      change (∑ x ∈ Icc 1 H, ∑ y ∈ Icc 1 H, _) = 0
      simp [hH]
    rw [he]
    positivity
  · have hHpos : 1 ≤ H := by omega
    apply E2_bound_without_display10 lam l₃ N A cL2
      (Real.sqrt (2 ^ 16 : ℝ) * cSup * Real.sqrt cL2) hA hL hcL2 (by positivity)
    · intro i hi j hj
      rw [W0_eq_Wzero]
      have hbound : (H : ℝ) ≤ Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)) :=
        Nat.floor_le (by positivity)
      apply display19 _ _ _ _ _ _ _ _ _ _ _ _ hL hcL2
      · have hsi : (scale i : ℝ) ≤ H := by exact_mod_cast scale_le_N H H i le_rfl hHpos hi
        exact hsi.trans hbound
      · have hsj : (scale j : ℝ) ≤ H := by exact_mod_cast scale_le_N H H j le_rfl hHpos hj
        exact hsj.trans hbound
      · exact h12
    · intro i hi j hj
      exact display20_of_display12 A cSup cL2 (Qof A N) (τof A N) lam l₃
        (cutoff3 (10 ^ 4 * A) N) N (block i) (block j)
        (fun k hk => (scale_pos i).trans (scale_le_mem i k hk))
        (fun k hk => (scale_pos j).trans (scale_le_mem j k hk)) hL hcSup hcL2 h12

/-- Uniform cited form of display 12, Tolev 1999 Lemma 12 and page 88.
Constants are uniform in the bounded real weight lambda. -/
def Display12Uniform : Prop :=
  ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
    ∃ cSup cL2 N₀ : ℝ, 0 ≤ cSup ∧ 0 ≤ cL2 ∧
      ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        Display12 A cSup cL2 (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N

/-- BoundE2 is derived from the single cited display 12. -/
theorem boundE2_of_display12 (h12 : Display12Uniform) : BoundE2 := by
  intro A hA l₃ hl₃
  obtain ⟨cSup, cL2, N₀, hcSup, hcL2, hb⟩ := h12 A hA l₃ hl₃
  refine ⟨dyadicConstant * Real.sqrt 8 *
    (Real.sqrt cL2 + Real.sqrt (Real.sqrt (2 ^ 16 : ℝ) * cSup * Real.sqrt cL2)),
    max N₀ 3, fun lam hlam N hodd hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))).trans hN3
  exact E2_bound_of_display12 lam l₃ N A cSup cL2 hA hL hcSup hcL2
    (hb lam hlam N hodd ((le_max_left _ _).trans hN))

/-- The faithful main theorem is derived from displays 9 and 12 only. -/
theorem mainTheorem_of_displays9_12 (h9 : BoundE1) (h12 : Display12Uniform) : MainTheorem :=
  mainTheorem_of_E1_E2 h9 (boundE2_of_display12 h12)

end LeanLab.Tolev2009.MinorArcBound
