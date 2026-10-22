module

public import LeanLab.GoldbachAverage.U1440Theorem1Full

/-!
# Proof of the Goldston-Suriajaya 2021 entry

`LeanLab/GoldbachAverage/U1440Theorem1Full.lean` proves `gs_theorem1_full`, Theorem 1 eq. (11) of
Goldston and Suriajaya, arXiv 2110.14250v2, unconditionally, together with `gs_theorem1_full_real`, eq. (11) in `ℝ`, and `gs_theorem1_of_full`,
eq. (13), and the derived results of this entry: `EGS_indep_r`, `EGS_im_eq_zero`,
`logDeriv_zeta_neg_one_im` and `Z1_im_eq_zero`, which show that `E(N)` does not depend on `r` and
that every term is real; `zeroSum_summable`; `trivSum_bounds`; and `gs_theorem1_full_at_two`, the case `N = 2`.

Route, the paper's own: by orthogonality, `LeanLab/GoldbachAverage/GSTheorem1.lean`,
`E(N) = Σ_{m ≤ N} Σ_{a+b=m} (Λ(a) − 1)(Λ(b) − 1)`, so `Σ_{n ≤ N} G(n) = E(N) + 2ψ₁(N) − N(N − 1)/2`;
then the exact explicit formula for `ψ₁(N) = Σ_{n ≤ N} (N − n) Λ(n)` with the trivial zeros,
Davenport chapter 17, `LeanLab/PNTPort/ExplicitPsi1/TrivialLimit.lean`, proved from the residue
theorem on rectangles, the functional equation of ζ and zero counting in
`LeanLab/PNTPort/ZetaZeros/`, with `ζ'(0)/ζ(0) = log 2π`. Parts of the analytic number theory of
ζ(s) are ported from PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. AI wrote the Lean code,
Claude, Anthropic; it was checked by the Lean kernel. Binary Goldbach is open.
-/
