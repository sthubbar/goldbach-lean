module

public import LeanLab.PNTPort.BVMax.PiPi

/-!
# Proof of the Bombieri-Vinogradov 1965 entry

`LeanLab/PNTPort/BV/` proves the Bombieri-Vinogradov theorem at `y = x` from the multiplicative
large sieve, `LeanLab/PNTPort/LargeSieve/`, Vaughan's identity, the Pólya-Vinogradov inequality
and the Siegel-Walfisz theorem, `LeanLab/PNTPort/PsiChi/SiegelWalfisz.lean`; the Siegel-Walfisz
theorem rests on a zero-free region and Siegel's theorem for real characters,
`LeanLab/PNTPort/DirichletZF/`, and on analytic number theory of ζ(s) ported from
PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. `LeanLab/PNTPort/BVMax/Grid.lean` moves the
maximum over `y ≤ x` inside the sum, `Uncond.lean` states the result with no hypothesis,
`Primes.lean` and `PrimesUncond.lean` pass to `θ` and `π` by partial summation, and `PiPi.lean`
replaces `liD(y)` by `π(y)`. The compared theorems are `LeanLab.PNTPort.BVMax.bombieriVinogradovMax`,
`bombieriVinogradovMax_at_x`, `bvTheta`, `bvPi` and `bvPiPi`, proved in those files. AI wrote the
lab's Lean code and did the port, Claude, Anthropic; it was checked by the Lean kernel.
-/
