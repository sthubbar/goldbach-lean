module

public import LeanLab.BhowmikGrimmelt2026.Decomp84
public import LeanLab.ExceptionalSet.WeightedGallagher264

/-!
The standard Gallagher inequality used as a cited input on page 19.
Source: Gallagher 1970 Lemma 1 and Montgomery Topics Lemma 1.9.
This specializes the proved arbitrary real frequency inequality from main.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The standard Gallagher bound at natural frequencies with the explicit constant pi squared. -/
theorem gallagher_standard_explicit261 (N : ℕ) (a : ℕ → ℂ) (η : ℝ) (hη : 0 < η) :
    (∫ β in (-η)..η, ‖∑ n ∈ Finset.Icc 1 N, a n * ee (β * n)‖ ^ 2) ≤
      Real.pi ^ 2 * η ^ 2 * ∫ x : ℝ,
        ‖∑ n ∈ (Finset.Icc 1 N).filter
          (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + 1 / (2 * η)), a n‖ ^ 2 := by
  have he (β : ℝ) (n : ℕ) : ee (β * n) =
      Complex.exp ((2 * Real.pi * β * Complex.I) * (n : ℝ)) := by
    unfold ee
    congr 1
    push_cast
    ring
  simp_rw [he]
  exact LeanLab.ExceptionalSet.WeightedGallagher264.real_frequency_gallagher
    (Finset.Icc 1 N) (fun n : ℕ => (n : ℝ)) a hη

end LeanLab.BhowmikGrimmelt2026

