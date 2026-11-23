module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150
public import LeanLab.BhowmikGrimmelt2026.Coefficients150
public import LeanLab.BhowmikGrimmelt2026.Decomp502a
public import LeanLab.BhowmikGrimmelt2026.SharpArc673

/-!
ROUTE BURST 7, 20261112, repair pass. The two open leaves of the split of
`major_minor_mean_square150` in `Decomp150a.lean`, moved out of that file into this new one: an
existing file may never gain an unproved step, a new file carrying leaves may.  Nothing else lives here,
and every proof in `Decomp150a.lean` that used these two names still uses them, now through the
import of this module.

Both leaves are P0029, G. Bhowmik and L. Grimmelt 2026, "The exceptional set of the Goldbach
problem", arXiv 2607.27282 v2, Section 3, pages 11 and 12: the major arc expansion 3.5 with the
Gauss sum bound 3.6 and the zero bound 3.7, and the pointwise size of the arc tails of page 12.

AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 page 12, the arc tails pointwise.  `V² - W` is minus the sum over
`q ≤ Q = ⌊X^{1/2}⌋`, `(a, q) = 1`, of `μ(q)²/φ(q)² T(α - a/q)²` over the fractions `a/q` whose
arc does not contain `α`, with `|T(β)| ≤ min(X, 1/(2‖β‖))`.  The claim is
`|V(α)² - W(α)| ≪ X^{1+ε}` uniformly: the fractions within `1/(qQ)` of `α` but not assigned to
it have `q ≥ Q/2`, by the least denominator condition together with Farey spacing
`|a/q - a'/q'| ≥ 1/(q q')`, and there are `O(1)` of them,
each `≤ X²/φ(q)² ≪ X^{1+ε}`; the others give `Σ_{q ≤ Q} φ(q)^{-2} min(X², q²/‖qα‖²) ≪ X^{1+ε}`
by the standard count of `q` with `‖qα‖` small.  This is the `O(N^{1/2+ε})` of page 12, which
the survey states without proof. PROVED by the assigned residue cancellation in near_arc_tail502
and the dyadic inverse square estimate in far_kernel502. -/
theorem arc_tails_sup150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  -- Both near and far estimates have clean proofs in Decomp502a and Decomp504a.
  exact arc_tails_of_near_far502 near_arc_tail502 far_arc_tail502

end LeanLab.BhowmikGrimmelt2026
