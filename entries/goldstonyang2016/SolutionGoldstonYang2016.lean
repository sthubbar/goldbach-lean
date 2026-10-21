module

public import LeanLab.GoldbachAverage.GYTheorem2RH

/-!
# Proof of the Goldston-Yang 2016 entry, conditional on RH

`LeanLab/GoldbachAverage/GYTheorem2RH.lean` proves `gy_theorem2_proved`, Goldston-Yang
Theorem 2 with `RiemannHypothesis` as an explicit hypothesis, and `gy_zeroSum_summable`,
unconditionally. Route: `Σ_{n ≤ N} (N − n) G(n) = Σ_{m<N} ψ(m) ψ(N − 1 − m)`; writing
`ψ(m) = m + E(m)`, the cross terms give the second Riesz mean `Σ_{a ≤ N} Λ(a)(N − a)²/2` up to
`O(N²)`, evaluated by integrating the explicit formula for `ψ₁` term by term over the zeros,
`LeanLab/LZCesaroShort/Lemma8Proof.lean`; the term `Σ_m E(m) E(N − 1 − m)` is at most
`Σ_m E(m)²`, which is `O(N²)` under RH by Cramér's mean square bound,
`LeanLab/PNTPort/Selberg/CramerSum.lean`. Parts of the analytic number theory of ζ(s) are
ported from PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. AI wrote the Lean code,
Claude, Anthropic; it was checked by the Lean kernel. Binary Goldbach is open.
-/
