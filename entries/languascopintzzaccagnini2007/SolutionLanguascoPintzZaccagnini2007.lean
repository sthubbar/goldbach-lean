module

public import LeanLab.LPZ2007.ThreeInputs1123

/-!
# Proof of the Languasco, Pintz and Zaccagnini 2007 entry

`LeanLab/LPZ2007/ThreeInputs1123.lean` proves `cor42_of_three_inputs` and
`repaired_mainJ131_of_three_inputs`. They follow the paper's route through
`LeanLab/LanguascoPintzZaccagnini2007/`: the explicit formula reduction `Decomp481c`, the
exceptional moduli `Decomp481b`, the major arcs `DecompJ218`, the minor arcs and the singular
series average, assembled in `Closure383` and `LeanLab/LPZ2007/Prep1121J131FourInputs.lean`.
The real zero bound is proved in `Decomp481b` from Siegel's theorem, `LeanLab/PNTPort/DirichletZF/`.
Jutila's Theorem 1 is reduced to the density sentence of the paper in `JutilaSrc481`, and Iwaniec's
Theorem 2 to the region the paper uses in `IwaniecCells1122`. AI wrote the Lean code, Claude,
Anthropic; it was checked by the Lean kernel.
-/
