module

public import LeanLab.DensityGoldbach.U1506Vacuity
public import LeanLab.DensityGoldbach.AlsetriShaoThm11
public import LeanLab.DensityGoldbach.AlsetriShaoSharp

/-!
# Proof of the Alsetri-Shao 2024 entry

`LeanLab/DensityGoldbach/U1502Final.lean` proves `alsetriShao_1_2`, Theorem 1.2 of A. Alsetri and
X. Shao, *Density versions of the binary Goldbach problem*, arXiv 2405.18576v2, with no cited
hypothesis. `LeanLab/DensityGoldbach/AlsetriShaoThm11.lean` proves `theorem1_1`, the paper's
Theorem 1.1, and `LeanLab/DensityGoldbach/AlsetriShaoSharp.lean` proves `remark1_3`, the
sharpness of the constant `1/2` stated in the paper's Remark 1.3.
`LeanLab/DensityGoldbach/U1506Vacuity.lean` proves `hyp_satisfiable`, a derived result of this
entry, not a result of the paper: the hypothesis of Theorem 1.2 holds for `A = P`, by Dirichlet's
theorem in Mathlib.

Route for Theorem 1.2, the paper's: an almost all variant of the Fourier analytic transference
principle, the paper's Proposition 3.1, proved in `U1467Prop31`, `U1467Lemma32` and `U1467Bohr`, applied to the `W`-tricked
majorant `ν_b`. The paper cites two lemmas of Green 2005 for `ν_b`; both are proved here. The
pseudorandomness bound, Green's Lemma 6.2, is `green62` in `U1484Final`, from the lab's major arc
asymptotic with Siegel-Walfisz and Vinogradov's minor arc bound. In place of Green's restriction
estimate, Lemma 6.6, the proof uses a large spectrum bound at one exponent below `4`, which is
enough for Proposition 3.1 and is proved in `U1502Final` from the pointwise bound `nuMajorant` on
the Fourier coefficients of `ν_b`. The local count in `ZMod W` with density above `1/2` in every
class, `AlsetriShaoLocal`, and a covering by windows finish the argument.
Theorem 1.1 and Remark 1.3 use the prime number theorem in progressions, also from the lab's
Siegel-Walfisz theorem. Parts of the analytic number theory are ported from PrimeNumberTheoremAnd,
Apache 2.0, and the Selberg sieve files are by Arend Mellendijk, see `PORTING.md`. AI wrote the
other Lean code, Claude, Anthropic; it was checked by the Lean kernel. Binary Goldbach is open.
-/
