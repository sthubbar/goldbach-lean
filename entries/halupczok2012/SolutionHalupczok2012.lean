module

public import LeanLab.Halupczok2012.U1510Final

/-!
# Proof of the Halupczok 2012 entry, conditional on two cited results

`LeanLab/Halupczok2012/U1510Final.lean` proves `theorem2Zeroed_U1510` and `theorem2_U1510`,
Theorem 1.2 of K. Halupczok, *Goldbach's problem with primes in arithmetic progressions and in
short intervals*, JTNB 25, 2013, repaired, CONDITIONAL on `PPS1984Remark` and `PP1993Goldbach`,
which are explicit hypotheses of both theorems and not axioms. It also proves
`theorem3_of_remark` and `theorem5_of_PP1993`, which derive the paper's quoted Theorems 2.1 and
2.3 from those two hypotheses.

Route, the paper's proof of Theorem 1.2. `U1439Thm2Reduction` splits the ternary sum into a
binary part, bounded from the paper's Theorem 2.3 by Cauchy-Schwarz and an elementary divisor
moment, and a main term part. `U1452MainTermMV` to `U1462Tails` bound the main term part from the
paper's Theorem 2.1: the Chinese remainder step over moduli `lcm(q, s)`, the truncation of the
singular series `𝔖` at squarefree `s ≤ L^D`, the identification of the Euler product with `T`,
and the two tail bounds by Rankin's trick; this singular series part has no cited input.
`NonCoprime` proves that the non-coprime terms vanish, which gives the all `q` form with `T0`.
`U1495PPS` derives Theorem 2.1 from the Remark of Perelli, Pintz and Salerno, passing from `ψ`
to `θ` with Mathlib's Chebyshev bound, and `U1496PP` derives Theorem 2.3 from the Goldbach
analogue of Perelli and Pintz 1993 Theorem 3, as a difference of two of their sums, with
`U1493Theorem5Min` for the covering by short windows. AI wrote the Lean code, Claude, Anthropic;
it was checked by the Lean kernel. Binary Goldbach is open.
-/
