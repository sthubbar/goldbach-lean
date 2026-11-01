# Provenance of the GoldbachLean files

`GoldbachLean/Chebyshev1852/Psi30.lean` and `GoldbachLean/Chebyshev1852/Psi30Upper.lean` are the
Lean Lab files `LeanLab/ChebyshevExplicit/Psi30.lean` and `LeanLab/ChebyshevExplicit/Psi30Upper.lean`,
written by an AI agent, Claude by Anthropic, on 2026-10-19. The lab build log
`LeanLab/ChebyshevExplicit/build/20261019T1515Z-cloud27.log` records that both compared theorems
depend only on propext, Classical.choice and Quot.sound. No code is ported from another project.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later. One change was needed for rc3: in `Psi30.lean`,
  `Nat.Prime.dvd_factorial` is not reached through the file's Mathlib imports on rc3, so
  `public import Mathlib.Data.Nat.Prime.Factorial` was added, as in the copy of `Psi30.lean` in
  the Schnirelmann 1933 entry.
* Both files were converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; `#print axioms` lines were removed.
* The namespace `LeanLab.ChebyshevExplicit` was renamed `GoldbachLean.Chebyshev1852.Explicit`,
  and the import path `LeanLab.ChebyshevExplicit.Psi30` became `GoldbachLean.Chebyshev1852.Psi30`.
* No file contains a placeholder proof. Declarations not used by the two compared theorems were
  removed from the copy: from `Psi30.lean`, `psi_ge_09212`, `pi_ge_chebyshev30` and an `example`
  checking it at 30; from `Psi30Upper.lean`, `A_upper`, `psi_le_11062` and `theta_le_11062`. The
  module doc comments were edited to stop naming them; the upper file now gives the value
  6A/5 = 1.10555... in place of the removed bound 1.1062.
* No proof was changed.
