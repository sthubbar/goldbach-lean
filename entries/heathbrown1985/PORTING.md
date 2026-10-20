# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Heath-Brown 1985 entry needs: 115
modules, the import closure of `LeanLab.PNTPort.PsiChi.Unconditional`. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-20, except as follows.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ and the
  prime number theorem with error `x exp(-c √log x)`. Changes: every `@[blueprint ...]`
  attribute, `blueprint_comment` and `import Architect` removed; import paths renamed to
  `LeanLab.PNTPort.StrongPNT.*`; and these fixes, made in the lab for Mathlib v4.35.0:
  1. `StrongPNT/Tactic/LinearCombinationPrime.lean` re-exports Mathlib's
     `Mathlib.Tactic.LinearCombinationPrime`, present in Mathlib v4.35.0-rc3, which this
     repository uses; the lab, on v4.35.0, carries a copy of the v4.34.0 file instead.
  2. MellinCalculus: the lab's v4.35.0 fix `Smeas.nullMeasurableSet` is reverted to `Smeas`
     for rc3.
  3. EulerMaclaurin: an explicit `measurable_from_nat.comp Nat.measurable_floor` term replaces a
     `fun_prop` call.
  4. StrongPNT `BorelCaratheodoryDeriv`: the two half-differences rewritten before `field_simp`.
* `StrongPNT/Bridge.lean` is lab-written.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  The port needed the two changes above and `set_option maxHeartbeats 1000000` on
  `BV/Hyperbolic.lean`'s `hyperbolic_large_sieve`.

* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files. Four files that needed
  lemmas outside their own Mathlib imports take a private `import Mathlib`.
* MediumPNT: `convert this using 3; apply uIoc_of_le` became `rw [Set.uIoc_of_le ...]`, since the
  module system changed how far `convert` unfolds.
* The lab states results of the literature that it has not proved with `sorry`, so other lab
  files can cite them. None of those is used by any entry, and they were removed from this
  copy together with the few declarations that depended on them, so no file here other than
  the Challenge files contains `sorry`. Some docstrings still describe the lab's convention.

## Lab-written mathematics in the closure

Siegel's theorem and the zero-free region for Dirichlet L-functions, `PNTPort/DirichletZF/`;
the large sieve, `PNTPort/LargeSieve/`; Perron's formula pieces, `PNTPort/Perron/`; the
explicit formula and Siegel-Walfisz, `PNTPort/PsiChi/`; Bombieri-Vinogradov at y = x,
`PNTPort/BV/`; and Heath-Brown's argument, `HeathBrown1985/`.
