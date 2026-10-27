module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0059, H. Kadiri and A. Lumley, Short effective intervals containing primes, arXiv 1407.7902,
PDF read 2026-10-16. The cited Table 2 rows of Theorem 1.1 were removed from this copy.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014
open Real

/-- Theorem 1.1 for one Table 2 row: for every `x > x0` there is a prime `p` with
`(1 - 1/Δ) x < p < x`. The theorem needs `x0 ≥ 4 · 10^18`. -/
def KLRow (x0 Δ : ℝ) : Prop :=
  ∀ x : ℝ, x0 < x → ∃ p : ℕ, p.Prime ∧ (1 - 1 / Δ) * x < p ∧ (p : ℝ) < x

end LeanLab.KadiriLumley2014
