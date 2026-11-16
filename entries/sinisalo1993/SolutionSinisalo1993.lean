module

public import LeanLab.Sinisalo1993.Ternary

/-!
# Proof of the Sinisalo 1993 entry

`LeanLab/Sinisalo1993/Ternary.lean` proves `ternary_upto_YP_S`: the largest prime `p` below
`min (N - 4) (7.263 · 10^13)` is odd and, by the Young and Potler gap bound, lies within 778
of it; then `N - p` is even, at least 4 and at most `4 · 10^11`, so the even check writes it as
a sum of two primes, `LeanLab/Richstein2001/Remark.lean`. Both computations stay hypotheses.
AI agents wrote the Lean code, see `PORTING.md`; it was checked by the Lean kernel.
-/
