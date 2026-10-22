module

public import Mathlib

/-!
# Dudek 2017, the even case: every even N ≥ 4 is a prime plus a square-free number

A. W. Dudek, *On the sum of a prime and a square-free number*, The Ramanujan Journal 42, 2017,
pages 233 to 240, arXiv 1410.7459, Theorem 1: every integer `N > 2` is the sum of a prime and a
square-free number `m ≥ 1`.

This entry covers only the EVEN case of that theorem. The target theorem is

* `dudek_even`: every even `N ≥ 4` is `p + m` with `p` prime and `m ≥ 1` square-free.

The odd case of Dudek's Theorem 1 is NOT covered here. The statement uses only Mathlib's
`Nat.Prime`, `Squarefree` and `Even`, so the entry has no definitions of its own. Binary
Goldbach is open; it would give a stronger statement for even `N`, with `m` prime, and nothing
here claims it. AI wrote the Lean code. Lean names keep the namespace of the lab where the
proofs were written.
-/

@[expose] public section

namespace LeanLab.Dudek2017

/-- **Dudek 2017, Theorem 1, even case**: every even `N ≥ 4` is the sum of a prime `p` and a
square-free number `m ≥ 1`. -/
theorem dudek_even : ∀ N : ℕ, Even N → 4 ≤ N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  sorry

end LeanLab.Dudek2017
