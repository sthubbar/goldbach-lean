module

public import LeanLab.GoldbachAverage.Converse

/-!
# Proof of the Granville 2007 entry

`LeanLab/GoldbachAverage/FromVonKoch.lean` proves RH ⇒ `AvgRH` from the lab's von Koch bound
`|ψ(X) − X| ≤ C √X log³ X` under RH, `LeanLab/PNTPort/ZetaZeros/VonKoch.lean`, through the
elementary identity `Σ_{n ≤ N} G(n) = Σ_{a ≤ N} Λ(a) ψ(N − a)`.
`LeanLab/GoldbachAverage/Converse.lean` proves `AvgRH` ⇒ RH by the route reconstructed in part by
Bhowmik, Halupczok, Matsumoto, Suzuki (arXiv 1704.06103) and completed by Bhowmik and Ruzsa
(arXiv 1711.06442): `Σ G(n) qⁿ = (Σ Λ(n) qⁿ)²`, an Abelian step to
`Σ Λ(n) e^{−nt} = 1/t + O(t^{−1/2−ε})`, a Mellin transform holomorphic on `Re s > 1/2`, and the
residue of `ζ'/ζ` at a zero. Parts of the analytic number theory of ζ(s) are ported from
PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. AI wrote the Lean code, Claude, Anthropic;
it was checked by the Lean kernel.
-/
