# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Estermann 1938 entry needs: 116
modules. 115 of them are the import closure of `LeanLab.PNTPort.PsiChi.Unconditional`, byte for
byte the same files as `entries/heathbrown1985/LeanLab/` of this repository, whose PORTING.md
describes them in full. The one new module is `LeanLab/Estermann1938/Main.lean`. AI agents,
Claude by Anthropic, wrote the lab files between 2026-10-16 and 2026-10-20, except the ported
code listed below.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  contributors: the zero-free region for the Riemann zeta function and the prime number theorem
  with classical error term. The changes are those listed in
  `entries/heathbrown1985/PORTING.md`: blueprint attributes and the Architect import removed,
  import paths renamed, and small fixes for Mathlib v4.35.0-rc3. `StrongPNT/Bridge.lean` is
  lab-written.
* `LeanLab/PNTPort/Perron/Sinc.lean` and `LeanLab/PNTPort/Perron/Cauchy.lean` are narrow ports
  from the same commit, files `PrimeNumberTheoremAnd/LaplaceInversion.lean` and
  `PrimeNumberTheoremAnd/Mathlib/Topology/MetricSpace/Cauchy.lean`, Apache-2.0, by the
  PrimeNumberTheoremAnd contributors. `LeanLab/PNTPort/Perron/Cutoff.lean` contains one lemma,
  `norm_sinc_tail_le_of_pos`, copied from `LaplaceInversion.lean` with its hypothesis `1 ≤ a`
  weakened to `0 < a`. Their headers refer to a licence file in that folder; the licence is the
  repository's root LICENSE, Apache-2.0, and NOTICE records the port.
* Several lab files under `LeanLab/PNTPort/DirichletZF/` and `LeanLab/PNTPort/PsiChi/` adapt
  arguments of the StrongPNT files to Dirichlet L-functions and say so in their headers.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
* `LeanLab/Estermann1938/Main.lean` was converted to the Lean module system: a `module` header,
  `public import` of `LeanLab.ExceptionalSet.Statements` and `LeanLab.PNTPort.PsiChi.Unconditional`,
  which already carry Mathlib, and `@[expose] public section`. Its header comment was shortened
  and its proofs are unchanged.
* The lab file `LeanLab/Estermann1938/CircleRoute.lean`, a second proof of the same statement
  through the lab's circle method files, and the lab's unit files on single displays of the
  paper, `Decomp112.lean` to `Window112.lean`, are not part of this entry; the compared theorem
  does not use them.
* As in `entries/heathbrown1985`, cited results of the literature that the lab states without
  proof were removed from this copy together with the declarations that used them, so no file
  here other than the Challenge file has an unproved step. Some docstrings still describe the
  lab's convention.

## Route of the proof

The compared theorem is not proved by Estermann's own circle method text. `main` combines
Q of n ≤ E of n + 1, where E of X counts the even `4 ≤ m ≤ X` that are not sums of two primes,
with `LeanLab.PNTPort.PsiChi.goldbach_logPowerSaving`, the bound E of X ≪_A X log^-A X proved
in this repository's `heathbrown1985` entry by Heath-Brown's 1985 route from the Siegel-Walfisz
theorem.
