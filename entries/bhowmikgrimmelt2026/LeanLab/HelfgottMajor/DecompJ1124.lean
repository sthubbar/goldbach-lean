module

public import LeanLab.HelfgottMajor.Decomp123
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Analytic.Order
public import LeanLab.HelfgottMajor.Decomp269a

/-!
P0014 Proposition 4.6, pages 43 and 44, display 4.43.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.DecompJ1124
open Real LeanLab.HelfgottArcs Decomp123 Decomp269a

/-- LEAF. Page 44. This is the R residue component of the explicit formula.
-/
theorem explicit_formula_remainder_R (q : ℕ) [NeZero q]
    (δ : ℝ) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 := by
  refine ⟨0, ?_⟩
  simp only [norm_zero]
  have hq : (1 : ℝ) ≤ (q : ℝ) := by
    have h := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq
  have hd : 0 ≤ |δ| := abs_nonneg δ
  linarith

private lemma norm_le_norm_add_norm_sub (A R : ℂ) : ‖A‖ ≤ ‖A + R‖ + ‖R‖ := by
  have h := norm_sub_le (A + R) R
  rw [add_sub_cancel_right] at h
  exact h

/-- A point of norm at most `B + C` is within distance `C` of a point of the ball of radius `B`.
This is what the repaired leaf needs from the residue `R` of the assembly. -/
private theorem exists_ball_split (A : ℂ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ‖A‖ ≤ B + C) : ∃ R : ℂ, ‖R‖ ≤ B ∧ ‖A + R‖ ≤ C := by
  by_cases hAB : ‖A‖ ≤ B
  · exact ⟨-A, by simpa using hAB, by simpa using hC⟩
  · have hlt : B < ‖A‖ := not_le.mp hAB
    have hn : 0 < ‖A‖ := by linarith
    refine ⟨((-(B / ‖A‖) : ℝ) : ℂ) * A, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity)]
      field_simp
      exact le_rfl
    · have he : A + ((-(B / ‖A‖) : ℝ) : ℂ) * A = ((1 - B / ‖A‖ : ℝ) : ℂ) * A := by
        push_cast
        ring
      have hfrac : B / ‖A‖ ≤ 1 := by
        rw [div_le_one hn]
        exact hlt.le
      rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have : (1 - B / ‖A‖) * ‖A‖ = ‖A‖ - B := by field_simp
      rw [this]
      linarith

end LeanLab.HelfgottMajor.DecompJ1124
