module

public import LeanLab.BhowmikGrimmelt2026.Theorem31Ported1122

/-!
# Proof of the Bhowmik and Grimmelt 2026 Theorem 3.1 entry

`LeanLab/BhowmikGrimmelt2026/Theorem31Ported1122.lean` proves `theorem31_ported1122`: Theorem
3.1 of G. Bhowmik and L. Grimmelt, The exceptional set of the Goldbach problem, arXiv
2607.27282 v2, page 9. If `Θ < 3/4` and every zero of every Dirichlet L-function in the strip
`0 < Re s < 1` has real part at most `Θ`, then for every `ε > 0` the number of even integers up to
`X` that are not a sum of two primes is `≪ X^(2Θ - 1/2 + ε)`. No other hypothesis is assumed;
the explicit formula of Davenport chapter 19 for primitive characters is proved in
`LeanLab/PNTPort/ExplicitPsi1`. Binary Goldbach is open and is not claimed. AI agents wrote the
Lean code, see `PORTING.md`; it was checked by the Lean kernel.
-/
