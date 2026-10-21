# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Mann 1942 entry needs: 5 modules,
the import closure of `LeanLab.Schnirelmann.Mann`. AI agents, Claude by Anthropic, wrote them
between 2026-10-16 and 2026-10-17. No code is ported from another project.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  No file needed a change for rc3.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; `#print axioms` lines were removed.
* `LeanLab/Common/Goldbach.lean` and `LeanLab/SchnirelmannConstant/Defs.lean` are identical to
  the copies in the Heath-Brown 1985 entry of this repository.
* No file in this closure other than the Challenge contains `sorry`, and no declaration was
  removed; one lab comment in `Ramare1995/Section9.lean` that mentioned the word was reworded.
  `Ramare1995/Section9.lean` and `Ramare1995/Theorem91.lean` also hold the lab's work on
  Ramaré 1995, as `def ... : Prop` statements and the proved `theorem91`; they are in the
  closure because `Schnirelmann/Mann.lean` reuses their counting function `cnt`, the sumset
  predicate `Rep` and the Dyson transform lemmas.

## Lab-written mathematics in the closure

`Schnirelmann/Mann.lean`: Dyson's theorem of rank `h` with a real `δ ≤ 1`, and Mann's theorem
for Mathlib's `schnirelmannDensity`, following M. B. Nathanson, arXiv:2407.12253, Sections 3 to 5.
