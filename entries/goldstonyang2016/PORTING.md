# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Goldston-Yang 2016 entry needs:
65 modules, the import closure of `LeanLab.GoldbachAverage.GYTheorem2RH` after the import
change below. AI agents, Claude by Anthropic, wrote them between 2026-10-16 and 2026-10-20,
except as follows.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ, Mellin
  calculus, residue calculus on rectangles and the smoothed Chebyshev function. Each file
  carries a notice. These files are byte for byte the copies in the Granville 2007 entry of this
  repository, `entries/granville2007/LeanLab/PNTPort/StrongPNT/`, with the same changes:
  every `@[blueprint ...]` attribute, `blueprint_comment` and `import Architect` removed; import
  paths renamed to `LeanLab.PNTPort.StrongPNT.*`; and these fixes:
  1. `StrongPNT/Tactic/LinearCombinationPrime.lean` re-exports Mathlib's
     `Mathlib.Tactic.LinearCombinationPrime`, present in Mathlib v4.35.0-rc3.
  2. MellinCalculus: the lab's v4.35.0 fix `Smeas.nullMeasurableSet` is reverted to `Smeas`.
  3. EulerMaclaurin: an explicit `measurable_from_nat.comp Nat.measurable_floor` term replaces a
     `fun_prop` call.
  4. StrongPNT `BorelCaratheodoryDeriv`: the two half-differences rewritten before `field_simp`.
  5. MediumPNT: `convert this using 3; apply uIoc_of_le` became `rw [Set.uIoc_of_le ...]`.
* `LeanLab/PNTPort/ZetaZeros/`, `ExplicitPsi1/`, `Selberg/` and `Gallagher/` are lab-written on
  top of the ported files: zero counting, the local partial fraction formula for ζ'/ζ, the
  explicit formula for `ψ₁` with its sum over zeros, and Cramér's mean square bound under RH.
  No PrimeNumberTheoremAnd Selberg sieve file is used.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files; `#print axioms` lines
  were removed. Files identical to an already ported copy in `entries/granville2007` or
  `entries/heathbrown1985` were taken from there; the three lab comments in
  `ChenExplicit/Statements`, `GoldbachAverage/Statements` and `GoldbachAverage/Sums` reworded
  there are reworded here the same way.
* `GoldbachAverage/GYTheorem2RH.lean`: the lab file imports `GoldbachAverage.LZTheorem1RH`,
  whose closure has 122 modules, but uses nothing proved there beyond `Sums`, `ZeroSums`,
  `LZCesaroShort.Lemma8Proof` and `Selberg.CramerSum`. Its imports were replaced by those four,
  which cuts the closure to 65 modules. The proofs are unchanged.
* `GoldbachAverage/GYTheorem2RH.lean`: one theorem added, `gy_zeroSum_summable`, proving that the
  family summed by `zeroSum` in Theorem 2 is summable for every `N ≥ 1`, so the `tsum` is not the
  junk value. Its proof reuses the steps of the lab lemma `integral_Wf` in the same file.
* Removed declarations. The lab keeps cited, unproved statements of published results next to
  their definitions. None is used by the compared theorems; they were deleted, as were no
  declarations depending on them, since none did:
  - `GoldbachAverage/ZeroSums.lean`: `lz_theorem1`, `gy_theorem2`, `fujii`, `bsp_upper`. The
    proved `gy_theorem2_proved` in `GYTheorem2RH.lean` replaces the cited `gy_theorem2`. A
    docstring that named `lz_theorem1` was reworded.
  - `LZCesaroShort/Statements.lean`: `lz_theorem1`, `lz_theorem2a`, `lz_theorem2b`,
    `lz_lemma7`, `lz_lemma8`, `lz_sec5_rh`. The `Prop` definitions they asserted stay;
    `lz_lemma7_proved`, `lz_lemma8_proved` and `lz_sec5_rh_proved` prove three of them in
    `Lemma7Proof`, `Lemma8Proof` and `Sec5Proof`. A section heading was reworded.
  The lab modules `GoldbachAverage/Unconditional.lean` and
  `LZCesaroShort/Lemma13Statements.lean`, which also hold cited statements, are not in the
  reduced closure and are not included.
* No file in the entry other than the Challenge states anything without proof.

## Lab-written mathematics in the closure

`GoldbachAverage/GYTheorem2RH.lean`, Goldston-Yang Theorem 2 under RH;
`LZCesaroShort/Lemma7Proof.lean`, `Lemma8Proof.lean`, `Sec5Proof.lean`, the explicit formula for
`ψ₁` and its integral; `PNTPort/Selberg/`, Cramér's mean square under RH; `PNTPort/Gallagher/`,
`PNTPort/ExplicitPsi1/`, `PNTPort/ZetaZeros/`.
