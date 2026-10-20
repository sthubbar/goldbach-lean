# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Granville 2007 entry needs: 32
modules, the import closure of `LeanLab.GoldbachAverage.Converse`. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-20, except as follows.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ, Mellin
  calculus, residue calculus on rectangles and the smoothed Chebyshev function. Each file
  carries a notice. These files are identical to the copies in the Heath-Brown 1985 entry of
  this repository, `entries/heathbrown1985/LeanLab/PNTPort/StrongPNT/`, with the same changes:
  every `@[blueprint ...]` attribute, `blueprint_comment` and `import Architect` removed; import
  paths renamed to `LeanLab.PNTPort.StrongPNT.*`; and these fixes:
  1. `StrongPNT/Tactic/LinearCombinationPrime.lean` re-exports Mathlib's
     `Mathlib.Tactic.LinearCombinationPrime`, present in Mathlib v4.35.0-rc3.
  2. MellinCalculus: the lab's v4.35.0 fix `Smeas.nullMeasurableSet` is reverted to `Smeas`.
  3. EulerMaclaurin: an explicit `measurable_from_nat.comp Nat.measurable_floor` term replaces a
     `fun_prop` call.
  4. StrongPNT `BorelCaratheodoryDeriv`: the two half-differences rewritten before `field_simp`.
  5. MediumPNT: `convert this using 3; apply uIoc_of_le` became `rw [Set.uIoc_of_le ...]`.
* `LeanLab/PNTPort/ZetaZeros/` is lab-written on top of the ported files: zero counting, the
  local partial fraction formula for ζ'/ζ, the von Koch bound under RH, and the residue of ζ'/ζ
  at a zero.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  Apart from the StrongPNT fixes above, no file needed a change for rc3.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files; `#print axioms` lines
  were removed.
* No file in this closure other than the Challenge contains `sorry`; three lab comments that
  mentioned the word were reworded. `LeanLab/ChenExplicit/Statements.lean` holds only definitions, used for
  the twin prime constant in `GoldbachAverage/Statements.lean`, which is not part of the
  Challenge.

## Lab-written mathematics in the closure

`GoldbachAverage/FromVonKoch.lean`, RH ⇒ the average asymptotic, from the von Koch bound;
`GoldbachAverage/Converse.lean`, the converse, by the route reconstructed in part by Bhowmik,
Halupczok, Matsumoto, Suzuki (arXiv 1704.06103) and completed by Bhowmik and Ruzsa
(arXiv 1711.06442); `PNTPort/ZetaZeros/`.
