# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Alsetri-Shao 2024 entry needs: 127
modules, the import closure of `LeanLab.DensityGoldbach.U1506Vacuity`, which imports
`U1502Final`, the proof of Theorem 1.2, together with `LeanLab.DensityGoldbach.AlsetriShaoThm11`
and `LeanLab.DensityGoldbach.AlsetriShaoSharp`. AI agents, Claude by Anthropic, wrote them between
2026-10-16 and 2026-10-25, except as follows. Binary Goldbach is open; nothing here claims it.

93 of the 127 files were already in other entries of this repository and were copied from there.
Each was compared with a fresh conversion of the current lab file, and the only differences are
the module header, the port fixes, comment rewording and removals listed in the PORTING.md of the
entry it was copied from, which apply here unchanged: 88 files from
`entries/hardylittlewood1923/LeanLab`, among them all of `PNTPort/StrongPNT/`,
`PNTPort/DirichletZF/`, `PNTPort/LargeSieve/`, `PNTPort/PsiChi/`, `PNTPort/Vinogradov/`, the
`PNTPort/BV/` files used here, `PNTSieve/` except `MertensUpper`, `Routes/`,
`HardyLittlewood1923/APSums` and `APPow`, `ChenExplicit/Statements`, `HeathBrown1985/Statements`,
`Elementary`, `Lemma2` and `DivMoments`, and `Common/Goldbach`; `AlmostPrimes/DDLemma23`,
`DDLemma23Full` and `RSLogSum` and `PNTSieve/MertensUpper` from `entries/renyi1948/LeanLab`; and
`ExceptionalSet/Statements` from `entries/bombierivinogradov1965/LeanLab`.

The other 34 files are new in this repository: 33 files of `DensityGoldbach/` and
`VanDerCorput1939/Totient`. They were converted from the lab with no change to the Lean code
beyond the module header and the removal of `#print axioms` lines, except the changes listed
below. None of them needed a fix for Mathlib v4.35.0-rc3.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. Same
  files and same changes as in the Heath-Brown 1985, Bombieri-Vinogradov 1965 and Hardy-Littlewood
  1923 entries; see their PORTING.md. `StrongPNT/Bridge.lean` is lab-written.
* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean`, `SelbergBounds.lean` and
  `BrunTitchmarsh.lean`, from the same commit, Apache-2.0, written by Arend Mellendijk: the
  Selberg sieve, its bounds and the Brun-Titchmarsh inequality. Each file keeps its copyright line
  and carries a notice of the port. They are the copies in the Hardy-Littlewood 1923 entry, whose
  PORTING.md and that of the Brun 1919 entry list the changes. `PNTSieve/BrunTitchmarshAP.lean`
  and `PNTSieve/MertensUpper.lean` are lab-written.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later. The copied files carry the port fixes of the
  entries they come from.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* `DensityGoldbach/Statements.lean`: the lab keeps cited, unproved statements of published
  results next to their definitions. None is used by the compared theorems, and they were
  removed together with the definitions only they use: `shao_1_1`, `liPan`, `shao_1_3`,
  `prop_1_4` and `alsetriShao_1_1`, unproved statements of Shao 2012, of Li and Pan 2007 and of
  Theorem 1.1 of Alsetri and Shao in another form; the lab placeholder `alsetriShao_1_2` of type
  `AlsetriShao12`, replaced by the proved `U1502.alsetriShao_1_2`; and the definitions `relRatio`,
  `lowerDensity`, `IsSum3`, `LargeOddIn`, `Shao11`, `LiPan`, `Shao13`, `unitsMod`, `Prop14`, `Cor15`
  and `AlsetriShao11`. The kept definitions `P`, `lowerDensityRes` and `AlsetriShao12` are
  unchanged; the module doc comment was rewritten and the docstring of `AlsetriShao12` names the
  paper instead of a lab paper number.
* `VanDerCorput1939/Totient.lean` and `DensityGoldbach/Statements.lean`: doc comments were
  reworded so that no file outside the Challenge names an unfinished proof; no code changed.
* `DensityGoldbach/U1506Vacuity.lean`: its four `#print axioms` lines were removed; the axioms
  of the compared theorems were printed separately, propext, Classical.choice and Quot.sound
  only.
* No file in the entry other than the Challenge states anything without proof.

## Lab-written mathematics in the closure

Theorem 1.2 of Alsetri and Shao, `DensityGoldbach/U1446Thm12` to `U1502Final`, by the paper's
route: an almost all variant of the Fourier analytic transference principle, with the
`W`-trick, the majorant bound `nuMajorant`, the large spectrum bound and the local count in
`ZMod W`, `AlsetriShaoLocal`. Theorem 1.1, `AlsetriShaoThm11` with `AlsetriShaoModulus`, and the
sharpness of Remark 1.3, `AlsetriShaoSharp`, from the prime number theorem in progressions,
`PrimesAP`. Below them: the unconditional circle method of `PNTPort/Vinogradov/`, with Vaughan's
identity, the minor arc bound and the major arcs from Siegel-Walfisz; the Siegel-Walfisz theorem
itself, `PNTPort/PsiChi/`, with Siegel's theorem and the zero-free region for Dirichlet
L-functions, `PNTPort/DirichletZF/`; the large sieve; and Brun-Titchmarsh in progressions.

One `decide +kernel` in the closure checks a finite fact, `sharp_105` in `AlsetriShaoLocal`, the
sharpness example after the paper's Theorem 2.1 at `m = 105`; no compared theorem uses it. The
other uses of `decide` check small facts such as `primorial 2 = 2`. There is no `native_decide`.
