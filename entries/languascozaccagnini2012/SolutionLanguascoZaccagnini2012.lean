module

public import LeanLab.GoldbachAverage.LZTheorem1RH

/-!
# Proof of the Languasco-Zaccagnini 2012 entry, conditional on RH

`LeanLab/GoldbachAverage/LZTheorem1RH.lean` proves `lz_theorem1_proved`, Languasco-Zaccagnini
Theorem 1 with `RiemannHypothesis` as an explicit hypothesis, and from it `bsp_upper_proved` and
`fujii_proved`, the weaker error terms of Bhowmik and Schlage-Puchta and of Fujii, through
`LeanLab/GoldbachAverage/Links.lean`; it also proves `lz_zeroSum_summable`, unconditionally,
from the absolute convergence of the zero sum in the explicit formula for `ψ₁`,
`LeanLab/PNTPort/ExplicitPsi1/Final.lean`. Route, the paper's own: the unconditional identity of
Goldston and Suriajaya, `LeanLab/GoldbachAverage/GSTheorem1.lean`, writes the sum as
`N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + E(N) + O(N)` with `E(N) = ∫₀¹ (Ψ − I)² I_N dα`; `E(N)` is bounded
by `N log³ N` by splitting `[−1/2, 1/2]` into dyadic layers and applying, on each, the mean square
bound of `S̃(α) − 1/z` near `0` under RH, Lemma 1 of the paper,
`LeanLab/LZCesaroShort/Lemma1Proved.lean`, proved from Selberg and Gallagher type mean value
estimates in `LeanLab/PNTPort/Selberg/`. Parts of the analytic number theory of ζ(s) are ported
from PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. AI wrote the Lean code, Claude,
Anthropic; it was checked by the Lean kernel. Binary Goldbach is open.
-/
