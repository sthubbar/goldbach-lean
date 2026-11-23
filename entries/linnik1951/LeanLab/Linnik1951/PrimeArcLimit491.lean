module

public import Mathlib

/-!
P0093 pages 154 and 161. Passage from the truncated series to the full series in a
square integral over an arc. Uniform convergence, no arithmetic.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- P0093 page 154, the series S, and page 161, the series S one. A bound for
the square integral of every truncation of an absolutely convergent series of
negative frequencies passes to the full series. Proved by dominated convergence
on the arc, with the constant bound given by the square of the sum of the norms.
Standard analysis, not in the print. -/
theorem series_arc_limit491 (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (r K : ℝ)
    (hr : 0 ≤ r)
    (h : ∀ M : ℕ, (∫ z in -r..r, ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤ K) :
    (∫ z in -r..r, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤ K := by
  have hnorm : ∀ (n : ℕ) (z : ℝ),
      ‖a n * Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ = ‖a n‖ := by
    intro n z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum : ∀ z : ℝ, Summable
      (fun n : ℕ => a n * Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)) := by
    intro z
    refine Summable.of_norm ?_
    simpa only [hnorm] using ha
  have hb : ∀ (M : ℕ) (z : ℝ), ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ≤ ∑' n, ‖a n‖ := by
    intro M z
    refine (norm_sum_le _ _).trans ?_
    simp only [hnorm]
    exact ha.sum_le_tsum _ (fun i _ => norm_nonneg _)
  have hcont : ∀ M : ℕ, Continuous (fun z : ℝ => ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) := by
    intro M
    fun_prop
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -r) (b := r) (l := Filter.atTop)
    (F := fun (M : ℕ) (z : ℝ) => ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2)
    (f := fun z : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2)
    (fun _ => (∑' n, ‖a n‖) ^ 2)
    (Filter.Eventually.of_forall fun M => (hcont M).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun M => Filter.Eventually.of_forall fun z _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb M z) 2)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun z _ =>
      (((hsum z).hasSum.tendsto_sum_nat).norm).pow 2)
  exact le_of_tendsto' key h

end LeanLab.Linnik1951
