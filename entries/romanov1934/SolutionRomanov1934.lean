module

public import LeanLab.Romanov.ErdosDensity

/-!
# Proof of the Romanov 1934 entry

`LeanLab/Romanov/Final.lean` proves Romanov's theorem with `k ≥ 0` by the second moment method:
for `N = 2^(L+1)` the pairs `(p, k)` with `p ≤ N` prime and `k < L` number at least `N/4`, and
Cauchy-Schwarz bounds the number of distinct sums `p + 2^k` from below by the square of that
count over the number of coincidences `p + 2^k = p' + 2^k'`. The coincidences are bounded by a
Selberg sieve upper bound for prime pairs with difference `2^k' - 2^k`, from the Selberg sieve
ported from PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`, and by the bound
`Σ_{k < k' < L} ∏_{p ∣ 2^k' - 2^k} (1 + 1/p) ≪ L²`, `LeanLab/Romanov/Lemma.lean`.
`LeanLab/Romanov/PositiveK.lean` removes the `k = 0` terms with Mathlib's Chebyshev bound.
`LeanLab/Romanov/Erdos.lean` and `ErdosDensity.lean` prove Erdős' covering result and its density
form. Binary Goldbach is open; nothing here claims it. AI wrote the Lean code, Claude, Anthropic;
it was checked by the Lean kernel.
-/
