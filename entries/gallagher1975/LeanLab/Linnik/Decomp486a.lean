module

public import LeanLab.Linnik.Decomp1532b

/-!
Gallagher 1975 p.138 before display 5.
Shared finite fiber estimate for the major arc averaging route.
The original namespace and declaration text are preserved.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg)

/-- Gallagher 1975 p.138 before display 5. Auxiliary fiberwise reduction: the remainder is at
most the sum over nonzero differences of the per frequency error of Theorem 3. -/
theorem major_arc_remainder_le_fiber_sum (k L N : ℕ) (P : ℝ) (E : ℤ → ℝ)
    (hE : ∀ n : ℤ, n ≠ 0 → |(∫ α in majorArcs N P, ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) -
        LeanLab.Linnik.Decomp1532b.Jn N n *
          (LeanLab.Linnik.Decomp1532b.singSeries n).re| ≤ E n) :
    |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k L with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N P,
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
      (∑ x : LeanLab.Linnik.Decomp1532a.pairs k L with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
          LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
            (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
      ∑ x : LeanLab.Linnik.Decomp1532a.pairs k L with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0, E (LeanLab.Linnik.Decomp1532a.dif x) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x hx => ?_)
  exact hE _ (mem_filter.mp hx).2

end LeanLab.Linnik.Decomp1532c

