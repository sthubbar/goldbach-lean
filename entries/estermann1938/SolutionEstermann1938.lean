module

public import LeanLab.Estermann1938.Main

/-!
# Proof of the Estermann 1938 entry

`LeanLab/Estermann1938/Main.lean` proves Estermann's bound `Q(n) = O(n log^{-a} n)` from the
bound `E(X) ≪_A X (log X)^{-A}` for the even `4 ≤ m ≤ X` that are not sums of two primes, proved
in `LeanLab/PNTPort/PsiChi/Unconditional.lean` by Heath-Brown's 1985 route from the
Siegel-Walfisz theorem. That closure is the one of this repository's `heathbrown1985` entry; the
analytic number theory of the Riemann zeta function it uses is ported from PrimeNumberTheoremAnd, Apache 2.0, with
changes listed in `PORTING.md`. AI agents, Claude by Anthropic, wrote the lab's Lean code and did
the port; it was checked by the Lean kernel.
-/
