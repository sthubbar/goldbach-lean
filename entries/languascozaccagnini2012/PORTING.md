# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Languasco-Zaccagnini 2012 entry needs:
121 modules, the import closure of `LeanLab.GoldbachAverage.LZTheorem1RH`. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-21, except as follows.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ, Mellin
  calculus, residue calculus on rectangles, bounds for ζ and the strong prime number theorem.
  Each file carries a notice. These files are byte for byte the copies in the Goldston-Yang 2016,
  Granville 2007 and Heath-Brown 1985 entries of this repository, with the same changes: every
  `@[blueprint ...]` attribute, `blueprint_comment` and `import Architect` removed; import paths
  renamed to `LeanLab.PNTPort.StrongPNT.*`; and these fixes:
  1. `StrongPNT/Tactic/LinearCombinationPrime.lean` re-exports Mathlib's
     `Mathlib.Tactic.LinearCombinationPrime`, present in Mathlib v4.35.0-rc3.
  2. MellinCalculus: the lab's v4.35.0 fix `Smeas.nullMeasurableSet` is reverted to `Smeas`.
  3. EulerMaclaurin: an explicit `measurable_from_nat.comp Nat.measurable_floor` term replaces a
     `fun_prop` call.
  4. StrongPNT `BorelCaratheodoryDeriv`: the two half-differences rewritten before `field_simp`.
  5. MediumPNT: `convert this using 3; apply uIoc_of_le` became `rw [Set.uIoc_of_le ...]`.
* `StrongPNT/Bridge.lean` is lab-written, the same file as in the Heath-Brown 1985 entry.
* Everything else, including `PNTPort/ZetaZeros/`, `ExplicitPsi1/`, `Selberg/`, `Gallagher/`,
  `LargeSieve/` and `Vinogradov/`, is lab-written. No PrimeNumberTheoremAnd Selberg sieve file is
  used.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files; `#print axioms` lines
  were removed. The conversion was redone from the lab sources; every file that came out the same
  as an already ported copy in `entries/goldstonyang2016`, `entries/granville2007`,
  `entries/heathbrown1985` or `entries/schnirelmann1933` was taken from there, 64 of them from
  the Goldston-Yang entry, including that entry's rewordings of lab comments in
  `ChenExplicit/Statements`, `GoldbachAverage/Statements` and `GoldbachAverage/Sums`.
* `ChebyshevExplicit/Psi30.lean`: `Nat.Prime.dvd_factorial` is not reached through the file's
  Mathlib imports on rc3, so `public import Mathlib.Data.Nat.Prime.Factorial` was added, as in
  the Schnirelmann 1933 entry, whose copy is used.
* `GoldbachAverage/LZTheorem1RH.lean`: one theorem added, `lz_zeroSum_summable`, proving that the
  family summed by `zeroSum` in `Z1 x` is summable for every real `x > 0`, so the `tsum` in
  Theorem 1 is not the junk value. Its proof multiplies the lab's `summable_zterm` of
  `PNTPort/ExplicitPsi1/Final.lean` by `x`. A docstring that named the cited `lz_theorem1` was
  reworded.
* Imports. The four modules the lab file `LZTheorem1RH.lean` imports, and the modules below
  them, are all used by its proofs once the declarations listed next are removed, so no import was
  changed. In particular `LZCesaroShort/Lemma1Proved.lean` imports `Theorem2aShort`, and through it
  the Zinoviev, Chebyshev and Pintz-Althöfer files, for its theorem `I3_boundY_full`, which this
  entry does not use but which is proved; it was kept rather than deleting proved mathematics.
* Removed declarations. The lab keeps cited, unproved statements of published results next to
  their definitions. None is used by the compared theorems; they were deleted, as was the one
  declaration depending on them:
  - `GoldbachAverage/ZeroSums.lean`: `lz_theorem1`, `gy_theorem2`, `fujii`, `bsp_upper`, as in
    the Goldston-Yang entry, whose copy is used. The proved `lz_theorem1_proved`,
    `bsp_upper_proved` and `fujii_proved` in `LZTheorem1RH.lean` replace the cited ones.
  - `GoldbachAverage/Unconditional.lean`: `gs_theorem1`, `gs_corollary2`, `lz_cesaro`. The proved
    `gs_theorem1_proved` in `GSTheorem1.lean` replaces the first. Three comments reworded. The
    definitions `eAdd`, `PsiGen`, `IGen`, `IGenN`, `EGS`, `Theta`, `lz_cesaro_printed`, the proved
    alias `gs_theorem7_odd` and the Gamma identities stay.
  - `GoldbachAverage/GSTheorem1.lean`: the `example : type_of% gs_theorem1 := gs_theorem1_proved`
    faithfulness check, which referred to the removed `gs_theorem1`.
  - `LZCesaroShort/Lemma13Statements.lean`: `lz_lemma1`, `lz_lemma3`. The `Prop` definitions
    `Lemma1` and `Lemma3` stay; `lz_lemma1_proved` in `Lemma1Proved.lean` proves `Lemma1` from RH.
    The module comment was reworded.
  - `LZCesaroShort/Statements.lean`: `lz_theorem1`, `lz_theorem2a`, `lz_theorem2b`,
    `lz_lemma7`, `lz_lemma8`, `lz_sec5_rh`, as in the Goldston-Yang entry, whose copy is used.
* No file in the entry other than the Challenge states anything without proof.

## Lab-written mathematics in the closure

`GoldbachAverage/LZTheorem1RH.lean`, Languasco-Zaccagnini Theorem 1 under RH, and `Links.lean`,
the passage to the weaker bounds of Bhowmik and Schlage-Puchta and of Fujii;
`GoldbachAverage/GSTheorem1.lean`, the unconditional identity of Goldston and Suriajaya;
`LZCesaroShort/`, the dyadic layer bounds and Lemma 1 of the mean square of `S̃ − 1/z` under RH;
`PNTPort/Selberg/`, the mean value estimates behind it; `PNTPort/Gallagher/`,
`PNTPort/ExplicitPsi1/`, `PNTPort/ZetaZeros/`, `PNTPort/LargeSieve/`, `PNTPort/Vinogradov/`,
`Zinoviev1997/`, `ChebyshevExplicit/` and `ExceptionalSet/PintzAlthofer2026Beta.lean`.
