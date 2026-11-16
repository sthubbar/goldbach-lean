module

public import Mathlib

/-!
# Ternary Goldbach up to 7.303 · 10^13 from the even check to 4 · 10^11 and a prime gap bound

M. K. Sinisalo, Checking the Goldbach conjecture up to 4 · 10^11, Mathematics of Computation
61, no. 204, 1993, 931 to 934.

Sinisalo verified by computer that every even number from 4 to `4 · 10^11` is a sum of two
primes. Section 4 of the paper remarks that such a check gives ternary Goldbach on a range:
an odd `N` with a prime `p` in the interval from `N - 4 · 10^11` to `N - 4` is `p` plus an even
number from 4 to `4 · 10^11`, hence a sum of three primes. Young and Potler, First occurrence
prime gaps, Mathematics of Computation 52, 1989, found that no gap between consecutive primes up
to `7.263 · 10^13` exceeds 778, the bound Kaniecki uses on page 371 of Acta Arithmetica 72, 1995.

This file states one theorem:

* `LeanLab.Sinisalo1993.Ternary.ternary_upto_YP_S`: if every prime `p ≤ 7.263 · 10^13` is
  followed by a prime at most 778 later, `YoungPotler`, and every even number from 4 to
  `4 · 10^11` is a sum of two primes, `EvenGoldbachUpTo (4 · 10^11)`, then every odd `N` with
  `7 ≤ N ≤ 73029999999000 = 7.263 · 10^13 + 4 · 10^11 - 1000` is a sum of three primes.

Both inputs are computations printed in the cited papers, binary Goldbach to `4 · 10^11` by
Sinisalo and the maximal gap by Young and Potler. They are hypotheses here and are not
proved. The primes in a sum of three primes need not be distinct.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `n` is a sum of three primes. -/
def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- Binary Goldbach holds for every even `n` with `4 ≤ n ≤ N`. -/
def EvenGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ N → IsGoldbachSum n

end LeanLab

namespace LeanLab.Kaniecki1995
open Finset

/-- The least prime larger than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- `λ(x) = 2` for `0 < x ≤ 7`, and for `x > 7` the largest gap `nextPrime p - p` over the
primes `p ≤ x`, Kaniecki 1995, p. 371. -/
noncomputable def lam (x : ℝ) : ℕ :=
  if x ≤ 7 then 2 else ((range (⌊x⌋₊ + 1)).filter Nat.Prime).sup (fun p => nextPrime p - p)

/-- The Young and Potler 1989 computation, as cited by Kaniecki 1995 on p. 371: every prime
`p ≤ 7.263 · 10^13` has `nextPrime p - p ≤ 778`. A cited input, taken as a hypothesis. -/
def YoungPotler : Prop := (lam 72630000000000 : ℝ) ≤ 778

end LeanLab.Kaniecki1995

namespace LeanLab.Sinisalo1993.Ternary

open LeanLab LeanLab.Kaniecki1995

/-- Sinisalo 1993, Section 4, with the Young and Potler gap bound: from the maximal gap 778
below `7.263 · 10^13` and binary Goldbach for even numbers from 4 to `4 · 10^11`, every odd
`N` with `7 ≤ N ≤ 7.263 · 10^13 + 4 · 10^11 - 1000` is a sum of three primes. -/
theorem ternary_upto_YP_S (hYP : YoungPotler) (hS : EvenGoldbachUpTo (4 * 10 ^ 11)) {N : ℕ}
    (hN : Odd N) (h7 : 7 ≤ N) (hNx : N ≤ 73029999999000) : IsTernarySum N := by
  sorry

end LeanLab.Sinisalo1993.Ternary
