module

public import LeanLab.HelfgottMajor.DecompJ1124

/-!
Split of `explicit_formula_remainder_E` in `DecompJ1124.lean`, page 44, display 4.43.

The single inequality is cut along the two dichotomies that the source argument itself
branches on.

The shift `δ` of the Gaussian.  At `δ = 0` the Mellin transform is that of the plain
Gaussian, every zero weight is an explicit classical value, and the two budget terms
`13.347 * |δ|` and `1 + 6 * |δ|` collapse to `0` and `1`.  For `δ ≠ 0` the mass of the
shifted Gaussian sits at height about `2 * π * |δ|`, which is what the hypothesis
`max (4 * π ^ 2 * |δ|) 100 ≤ T` buys; inside the shifted case the ranges `|δ| ≤ 1` and
`1 < |δ|` are kept apart, because below `1` the shift is absorbed by the standing height
`100` while above `1` the saddle point travels with `|δ|`.

The conductor.  For `q = 1` the main term `fhat etaHeart (-δ) * x` is present and
`log q = 0`, so the right side loses its three logarithmic terms; for `q ≠ 1` that main
term is `0` and the logarithmic budget stays.

The four regimes cover every admissible parameter point, so the assembly at the end of the
file is exactly those case splits together with the specialisations `|0| = 0` and
`log 1 = 0`.  No leaf is the target itself: each one is the target restricted to one
regime, with the right side specialised on that regime.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.DecompJ1124
open Real LeanLab.HelfgottArcs Decomp123 Decomp269a

end LeanLab.HelfgottMajor.DecompJ1124
