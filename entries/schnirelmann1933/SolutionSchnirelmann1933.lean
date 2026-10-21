module

public import LeanLab.SchnirelmannExplicit.Sharper6
public import LeanLab.SchnirelmannGoldbach.Discharged

/-!
# Proof of the Schnirelmann 1933 entry

`LeanLab/SchnirelmannGoldbach/` proves Schnirelmann's theorem along Nathanson, GTM 164,
Chapter 7: a Selberg sieve upper bound for the number of representations `r(n)` of `n` as a sum
of two primes, `S1/`, built on the Selberg sieve ported from PrimeNumberTheoremAnd, Apache 2.0,
see `PORTING.md`; a mean square bound for the singular product, `S2.lean`; Cauchy-Schwarz and
Chebyshev's bound give a positive lower density of the sums of two primes, `S3.lean`; this gives
positive Schnirelmann density of `{0, 1} ∪ G` and, by Schnirelmann's basis theorem in
`LeanLab/Schnirelmann/Inequality.lean`, the bounded number of primes, `FromDensity.lean`.
`LeanLab/SchnirelmannExplicit/` makes every constant explicit: sieve constant 33, mean square
constant 2.52, Chebyshev's bound `π(m) ≥ 0.92 m / log m` from `ChebyshevExplicit/Psi30.lean`,
and Dyson's form of the basis step from `Ramare1995/Theorem91.lean`, which yields the bound
30772 in `Sharper6.lean`. Binary Goldbach is open; nothing here claims it. AI wrote the Lean
code, Claude, Anthropic; it was checked by the Lean kernel.
-/
