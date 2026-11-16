module

public import Mathlib

/-!
# The Granville, van de Lune and te Riele ratio bound on a smaller range

A. Granville, J. van de Lune and H. J. J. te Riele, Checking the Goldbach conjecture on a
vector computer, in Number Theory and Applications, R. A. Mollin ed., Kluwer 1989, pages 423
to 433. A Goldbach partition of an even `n` is `n = p + q` with odd primes `p ≤ q`, and
`p(n)` is the smallest `p` over all such partitions. Section 5 of the paper conjectures
`p(n) ≪ log² n · log log n` and derives from Table 3 that `p(n) / (log² n · log log n) < 1.603`
for all even `n` up to `2 · 10^10`, the bound of their verification of the conjecture.

This file states that bound, together with the existence of `p(n)`, for every even `n` with
`6 ≤ n ≤ 323740000`. That range is much smaller than the paper's range up to `2 · 10^10`;
the paper's full range is not claimed. `minGB n` is the least prime `p` with `n - p` prime;
for even `n ≥ 6` the prime 2 never qualifies and the least such `p` is at most `n - p`, so
`minGB n` is the paper's `p(n)`. The number 4 has no partition into odd primes, and `n = 4` is
excluded.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

/-- The least prime `p` with `n - p` prime, and `0` when there is no such prime. -/
noncomputable def minGB (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, p.Prime ∧ (n - p).Prime then Nat.find h else 0

/-- For every even `n` with `6 ≤ n ≤ 323740000`, the least prime `p(n)` with `n - p(n)` prime
exists, and `p(n) < 1.603 · log² n · log log n`. -/
theorem gvltr_ratio_upTo2 : ∀ n : ℕ, Even n → 6 ≤ n → n ≤ 323740000 →
    (minGB n).Prime ∧ (n - minGB n).Prime ∧
      (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) := by
  sorry

end LeanLab.GvLtR1989
