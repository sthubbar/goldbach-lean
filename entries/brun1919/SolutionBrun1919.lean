module

public import LeanLab.Brun1919.LeanEvalBridge
public import LeanLab.BrunGap.Uniform

/-!
# Proof of the Brun 1919 entry

`LeanLab/Brun1919/Sieve.lean` sifts `{m (m + 2) : m < N}` by the primes up to `z` with the
Selberg sieve of `LeanLab/SchnirelmannGoldbach/S1/`, built on the Selberg sieve ported from
PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`, and gets `π₂(N) ≤ 48 N / log² z` plus an
error term. `LeanLab/Brun1919/Final.lean` takes `z = √N` for `twinUpper`, then sums the bound
over dyadic blocks `[2^k, 2^(k+1))` against `Σ 1/(k + 1)²` for `brun`.
`LeanLab/Brun1919/LeanEvalBridge.lean` derives the lean-eval form `brun_constant_converges`.
`LeanLab/BrunGap/` does the same for prime pairs `(p, p + h)` with any even `h ≠ 0`, with the
singular product `∏_{p ∣ h} (1 + 1/p)` in the bound, and averages over `h ≤ H` with the mean
square bound of `LeanLab/SchnirelmannExplicit/Constants.lean`. Binary Goldbach and the twin prime
conjecture are open; nothing here claims them. AI wrote the Lean code, Claude, Anthropic; it was
checked by the Lean kernel.
-/
