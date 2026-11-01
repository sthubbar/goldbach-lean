module

public import GoldbachLean.Chebyshev1852.Psi30
public import GoldbachLean.Chebyshev1852.Psi30Upper

/-!
# Proof of the Chebyshev 1852 entry

`GoldbachLean/Chebyshev1852/Psi30.lean` proves the lower bound `psi_ge_chebyshev30`: by
Legendre's formula the combination `C(n)` of `log n!`, `log ⌊n/2⌋!`, `log ⌊n/3⌋!`,
`log ⌊n/5⌋!` and `log ⌊n/30⌋!` is a sum over primes of Chebyshev's weight, which is at most `1`,
so `C(n) ≤ ψ(n)`, and Mathlib's two-sided bound for `log ⌊x⌋!` bounds `C(n)` from below.
`GoldbachLean/Chebyshev1852/Psi30Upper.lean` proves the upper bound `psi_le_chebyshev30`: the
weight is nonnegative and equals `1` on `1 ≤ k ≤ 5`, so `ψ(n) - ψ(⌊n/6⌋) ≤ C(n)`, and strong
induction on `n` sums the geometric series. AI wrote the Lean code, Claude, Anthropic; it was
checked by the Lean kernel.
-/
