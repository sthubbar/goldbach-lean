# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Hardy-Littlewood 1923 entry needs: 143
modules, the import closure of the ten modules `LeanLab.HardyLittlewood1923.TheoremBAll`,
`TheoremBUnlike`, `TheoremB34`, `TheoremC`, `TheoremD`, `TheoremE`, `TheoremEAssigned`,
`TheoremF`, `U1503Endpoint` and `LeanLab.Verifications.U1574HLVerify`. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-27, except as follows. Binary Goldbach is
open; nothing here claims it.

Version 1 of the entry had the first 123 modules. Version 2 adds 20 modules for Theorem A, listed
in the section on version 2 below; the 123 modules of version 1 are unchanged, byte for byte.

73 of the 123 files were already in other entries of this repository. Each was compared with a
fresh conversion of the current lab file, and the only differences are the port fixes, comment
rewording and removals listed in the PORTING.md of the entry it was copied from, which apply here
unchanged: 62 files from `entries/bombierivinogradov1965/LeanLab`, among them all of
`PNTPort/StrongPNT/`, `PNTPort/DirichletZF/`, `PNTPort/LargeSieve/`, `PNTPort/PsiChi/` and the
`PNTPort/BV/` files used here; `ChenExplicit/Statements`, `HeathBrown1985/Lemma2` and
`HeathBrown1985/Statements` from `entries/heathbrown1985`; `PNTPort/BVMax/CoprimeHarm` from
`entries/renyi1948`; `GoldbachAverage/Statements` and `Sums` from `entries/granville2007`;
`ChebyshevExplicit/Psi30` from `entries/schnirelmann1933`; and `PNTSieve/AuxResults`, `Basic`,
`Selberg` and `SelbergBounds` from `entries/brun1919`.

The other 50 files are new in this repository and were converted from the lab with no change
beyond the module header, except the one fix below: 17 files of `HardyLittlewood1923/`, all
but `Section5`, which no compared theorem imports; the 20 files of `PNTPort/Vinogradov/`, the lab's unconditional circle method for three primes;
`VanDerCorput1939/Statements`, `Global`, `KBounds`, `SingLimit`, `Unweight` and
`Vinogradov1Proof`; `Routes/R0001Averaged`, `R0001Markov` and `R0001Parseval`;
`GoldbachAverage/OddSum` and `OddSumPNT`; and `PNTSieve/BrunTitchmarsh` and `BrunTitchmarshAP`.
None of them has an unfinished proof in the lab, so no declaration was removed from them.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ and the
  prime number theorem with error `x exp(-c √log x)`. Same files and same changes as in the
  Bombieri-Vinogradov 1965 and Heath-Brown 1985 entries; see their PORTING.md.
  `StrongPNT/Bridge.lean` is lab-written.
* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean`, `SelbergBounds.lean` and
  `BrunTitchmarsh.lean`, from the same commit, `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/`
  and the Brun-Titchmarsh file, Apache-2.0, written by Arend Mellendijk: the Selberg sieve, its
  bounds and the Brun-Titchmarsh inequality. Each file keeps its copyright line and carries a
  notice of the port. The first four are identical to the copies in the Brun 1919 entry, whose
  PORTING.md lists the lab's changes; `BrunTitchmarsh.lean` is new here and was ported in the lab
  the same way: declarations in `LeanLab.PNTSieve.*` namespaces and import paths renamed.
  `PNTSieve/BrunTitchmarshAP.lean` is lab-written on top of them.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later. The copied files carry the port fixes of the
  entries they come from. One new file needed a fix for rc3: in
  `VanDerCorput1939/Statements.lean`, theorem `euler_factor`, `field_simp; ring` leaves an
  inverse of `p² - 3p + 3` on rc3 and was replaced by
  `rw [one_add_div .., one_sub_div h2, one_sub_div .., div_mul_div_comm, div_eq_div_iff ..]; ring`.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* Four doc comments, in `VanDerCorput1939/Statements`, `ChenExplicit/Statements`,
  `HeathBrown1985/Statements` and `HeathBrown1985/Lemma2`, were reworded so that no file outside
  the Challenge names an unfinished proof; no code changed.
* The Challenge omits the line `open LeanLab.VanDerCorput1939 (I)` of `TheoremB34.lean`,
  `TheoremC.lean` and `TheoremD.lean`, since that namespace does not exist in the Challenge and no
  restated definition uses `I`. Every other `open` line and the local instance
  `Classical.propDecidable` of `TheoremD.lean` and `TheoremEStatements.lean` are kept, so the
  restated definitions elaborate as in the library.

## Lab-written mathematics in the closure

Theorems B to F of Hardy and Littlewood, `HardyLittlewood1923/`, with no hypothesis: the
recursion `ν_{r+1}(n) = Σ_p log p ν_r(n - p)`, the Euler product identities for the singular
series, prime sums in progressions with polynomial weights, and the averaging argument of Theorem
F. Below them: Vinogradov's three primes asymptotic, `VanDerCorput1939/Vinogradov1Proof`, from the
unconditional circle method of `PNTPort/Vinogradov/`, with Vaughan's identity, the minor arc
bound and the major arcs from Siegel-Walfisz; the Siegel-Walfisz theorem itself,
`PNTPort/PsiChi/`, with Siegel's theorem and the zero-free region for Dirichlet L-functions,
`PNTPort/DirichletZF/`; the large sieve; Brun-Titchmarsh in progressions; and an explicit
Chebyshev bound, `ChebyshevExplicit/Psi30`.

No `decide` in the closure is a heavy kernel computation: the six uses check small facts such
as `Finset.Ioc 0 2 = {1, 2}` and that `3` is a unit mod `8`. There is no `native_decide`.

## Version 2: Theorem A, eq. 3.113

Version 2 keeps every compared theorem, every restated definition and every Challenge statement
of version 1 unchanged, and adds Theorem A, `U1503.printedA_form_all_U1503_closed`, with five
derived results of the entry from `U1574HLVerify`, which are not statements of the paper.

The 20 new modules were converted from the lab, Lean and Mathlib v4.35.0 there, with
`tools/conv2.py`: 18 files of `HardyLittlewood1923/`, namely `U1438Circle`, `U1438Sing`,
`U1438TheoremA`, `U1444PrintedA`, `U1453PrintedA3`, `U1463Euler`, `U1463ThmA`, `U1468SingR`,
`U1473Explicit`, `U1479Split`, `U1482ZeroCount`, `U1489TruncB`, `U1503Contour`, `U1503Endpoint`,
`U1503Explicit`, `U1503LogDeriv`, `U1503Mellin` and `U1503ThmA`; `PNTPort/DirichletZF/U1482Jensen`;
and `Verifications/U1574HLVerify`, whose `#print axioms` lines were dropped. They are lab-written.
`U1503Contour`, `U1503LogDeriv` and `U1503Mellin` use, by import, the Borel-Caratheodory and
Jensen bounds, the rectangle integrals and the smoothing of the ported StrongPNT files, whose code
is by the PrimeNumberTheoremAnd contributors; no ported code was copied into them. They built on
v4.35.0-rc3 with no code change: none needed the rc3 fixes listed above, and none needed a private
`import Mathlib`. The 123 version 1 modules were compared with a fresh conversion of the current
lab files; the only differences are the port fixes and comment rewordings already listed.

None of the 20 files has an unfinished proof in the lab. The lab states some analytic inputs,
taken from Davenport, as cited Props, used only as hypotheses of conditional theorems. No compared
theorem depends on them, so this copy removes the six cited Props and the 23 declarations whose
statement or proof uses one of them:

* `U1438Circle`: `PsiPowerOfR`, `theoremA3_of_R`.
* `U1453PrintedA3`: `ExplicitFormulaLog`, `printedA3_upper`, `printedA3_upper_of_R`.
* `U1463ThmA`: `printedA_upper_all`, `printedA_upper_all_of_R`, `printedA_form_all`.
* `U1468SingR`: `printedA_form_all_U1468`.
* `U1473Explicit`: `ExplicitFormulaPrim`, `explicitFormulaLog_of_prim`, `printedA_form_all_U1473`.
* `U1479Split`: `ZeroCountUnit`, `TruncExplicitPrim`, `exists_zero_finset`,
  `psiChiPrimBound_of_split`, `explicitFormulaPrimNN_of_split`, `explicitFormulaLog_of_split`,
  `printedA_form_all_U1479`.
* `U1482ZeroCount`: `zeroCountUnit`, `printedA_form_all_U1482`.
* `U1489TruncB`: `TruncExplicitPrimB`, `truncExplicitPrimB_of_trunc`, `psiChiPrimBound_of_B`,
  `psiPowerLog_of_B`, `printedA_form_all_U1489`, `printedA_form_all_U1489_of_trunc`,
  `truncB_premise_nonvacuous`.
* `U1503Endpoint`: `printedA_form_all_U1489_uncond`.

The set was computed by a Lean script that walks the constants used by the compared theorems.
The module doc comments of these nine files and of `U1503ThmA` keep their lab text, which still
names the removed declarations, and each carries a packaging note saying so. Six `open` lines
that named removed declarations were shortened. Six doc comments were reworded so that
no file outside the Challenge names an unfinished proof; no code changed there.

The Challenge restates four definitions for Theorem A: `LeanLab.HeathBrown1985.ramanujan`,
`U1438.NoZerosRight`, `U1444.singR` and `U1574.GRH`, each with the `noncomputable section`, the
`open` lines and the local instance of its library file. It omits `open` lines that name
namespaces that do not exist in the Challenge, as in version 1: in `U1438TheoremA.lean`
the opens of `LeanLab.PNTPort.Vinogradov` and `LeanLab.VanDerCorput1939`, and in
`U1503Endpoint.lean` the opens of `U1453`, `U1463`, `U1468`, `LeanLab.PNTPort.Vinogradov` and
`LeanLab.PNTPort.BV`; no restated definition or compared statement uses a name they bring in.

Theorem A rests on lab-written mathematics: an explicit formula for psi of x and chi from a zero-free half
plane `Re s > Θ`, with a smooth weight, `U1503Explicit`, `U1503Contour`, `U1503LogDeriv`,
`U1503Mellin`, and zero counts by Jensen's formula, `U1482Jensen`, `U1482ZeroCount`; the major
arcs of the circle method for `r = 3` with this bound, `U1438Circle`, `U1453PrintedA3`,
`U1503Endpoint`; and the lift to every `r ≥ 3` with the singular series identities, `U1463Euler`,
`U1463ThmA`, `U1468SingR`.

No new module uses `decide` or `native_decide`. Seven theorems in the new modules raise
`maxHeartbeats` to 1000000 or 4000000, in `U1438Circle`, `U1453PrintedA3`, `U1463ThmA`,
`U1503Explicit` and `U1503Endpoint`; this is elaboration of long real-analysis estimates, not a
kernel computation. On a 2-core cloud machine `U1503Endpoint` took about 170 s and `U1503Explicit`
about 120 s to build.

