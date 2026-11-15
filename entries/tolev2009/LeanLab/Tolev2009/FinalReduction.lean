module

public import LeanLab.Tolev2009.L2Bound
public import LeanLab.Tolev2009.MinorArcBound

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.FinalReduction

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Displays19to20
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.MinorArcBound

/-- The remaining cited part of display 12, adapted from Tolev 1999 Lemma 12.
The elementary full interval L2 bound is not part of this input. -/
def Sup12 (A c Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : Prop :=
  ∀ α ∈ Set.Ioo (-1 / τ) (1 - 1 / τ), α ∉ majorArcs Q τ →
    ‖Kfun lam l₃ K₃ N α‖ ≤ c * N * Real.log N ^ (350 - 4 * A)

/-- Supply the L2 part of display 12 with the proved constant 17.
Derived from Sup12 only. -/
theorem display12_of_sup (A cSup : ℝ) (lam : ℕ → ℝ) (l₃ N : ℕ) (hA : 0 ≤ A)
    (hlam : ∀ k, |lam k| ≤ 1) (hl₃ : l₃ ≤ N) (hL : 1 ≤ Real.log N)
    (hSup : Sup12 A cSup (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N) :
    Display12 A cSup 17 (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N :=
  ⟨hSup, L2Bound.display12_L2_cutoff lam l₃ N _ (by positivity) hlam hl₃ hL⟩

/-- The pointwise minor arc bound with the elementary L2 estimate discharged.
Derived from Sup12 only. -/
theorem E2_bound_of_sup12 (lam : ℕ → ℝ) (l₃ N : ℕ) (A cSup : ℝ)
    (hA : 10 ^ 4 ≤ A) (hL : 1 ≤ Real.log N) (hcSup : 0 ≤ cSup)
    (hlam : ∀ k, |lam k| ≤ 1) (hl₃ : l₃ ≤ N)
    (hSup : Sup12 A cSup (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N) :
    E2 lam l₃ A N ≤ dyadicConstant * Real.sqrt 8 *
      (Real.sqrt 17 + Real.sqrt (Real.sqrt (2 ^ 16 : ℝ) * cSup * Real.sqrt 17)) *
      (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  E2_bound_of_display12 lam l₃ N A cSup 17 hA hL hcSup (by norm_num)
    (display12_of_sup A cSup lam l₃ N (by linarith) hlam hl₃ hL hSup)

/-- Uniform cited form of the supremum half of display 12.
Constants are uniform in all real weights bounded by one. -/
def Sup12Uniform : Prop :=
  ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
    ∃ cSup N₀ : ℝ, 0 ≤ cSup ∧
      ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        Sup12 A cSup (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N

/-- The full cited display 12 follows from its supremum half alone.
Derived from Sup12Uniform. -/
theorem display12Uniform_of_sup (hSup : Sup12Uniform) : Display12Uniform := by
  intro A hA l₃ hl₃
  obtain ⟨c, N₀, hc, hb⟩ := hSup A hA l₃ hl₃
  refine ⟨c, 17, max N₀ (max l₃ 3), hc, by norm_num, fun lam hlam N hodd hN => ?_⟩
  have hlN : (l₃ : ℝ) ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : (3 : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))).trans hN3
  exact display12_of_sup A c lam l₃ N (by linarith) hlam (by exact_mod_cast hlN) hL
    (hb lam hlam N hodd ((le_max_left _ _).trans hN))

/-- BoundE2 is derived from the supremum half of display 12 only. -/
theorem boundE2_of_sup12 (hSup : Sup12Uniform) : BoundE2 :=
  boundE2_of_display12 (display12Uniform_of_sup hSup)

/-- The faithful main theorem is derived from display 9 and the supremum half of display 12. -/
theorem mainTheorem_of_display9_sup12 (h9 : BoundE1) (hSup : Sup12Uniform) : MainTheorem :=
  mainTheorem_of_displays9_12 h9 (display12Uniform_of_sup hSup)

/-- The pointwise cited input has an explicit consistent zero weight instance. -/
example : Sup12 (10 ^ 4) 0 1 1 (fun _ => 0) 1 (cutoff3 (10 ^ 8) 16) 16 := by
  intro α _ _
  simp [Kfun]

end LeanLab.Tolev2009.FinalReduction
