# Provenance of the LeanLab files

`LeanLab/` holds the four lab files that the Sinisalo 1993 entry needs. AI agents wrote them in
Steve Hubbard's Lean Lab between 2026-10-16 and 2026-10-21. No code from outside the lab is
included, so the repository NOTICE does not change for this entry. Ternary Goldbach is
Helfgott's theorem and binary Goldbach is open; nothing here claims either. The two cited
computations, binary Goldbach to 4 · 10^11 and the Young and Potler maximal gap 778 below
7.263 · 10^13, are hypotheses of the compared theorem and are not proved.

## Authors of the files

* `LeanLab/Common/Goldbach.lean`: Claude by Anthropic, 2026-10-16. The definitions of sums of
  two and three primes and of binary and ternary Goldbach up to a bound.
* `LeanLab/Kaniecki1995/Statements.lean`: Claude by Anthropic, 2026-10-18. The gap function λ
  of Kaniecki 1995, page 371, and the cited Young and Potler bound as a Prop.
* `LeanLab/Richstein2001/Remark.lean`: Claude by Anthropic, 2026-10-18, lab unit U-0937. The
  step from a prime near N and a verified even range to a sum of three primes.
* `LeanLab/Sinisalo1993/Ternary.lean`: Claude by Anthropic, 2026-10-21, lab unit U-1380. The
  largest prime below a bound under the gap hypothesis, and `ternary_upto_YP_S`.

## Changes made for this repository

* Every file was converted to module syntax: the line `module`, then `public import` lines,
  the module doc comment and `@[expose] public section`.
* `LeanLab/Common/Goldbach.lean` is the same extract as in the Helfgott and Platt 2013 entry,
  with one line of its doc comment reworded: it keeps `IsGoldbachSum`, `IsTernarySum`,
  `EvenGoldbachUpTo` and `TernaryGoldbachUpTo` and drops the statements of the full
  conjectures and a Boolean primality and Goldbach test.
* `LeanLab/Kaniecki1995/Statements.lean` is an extract of the lab file: it keeps `nextPrime`,
  `lam` and `YoungPotler` and drops the other definitions and statements of the Kaniecki
  paper, with the lab import `LeanLab.SchnirelmannConstant.Defs`. The text of `nextPrime` and
  `lam` is the same as in the registered Kaniecki 1995 entry.
* `LeanLab/Richstein2001/Remark.lean` is an extract of the lab file: it keeps
  `ternary_of_prime_near` and drops its contrapositive and the bound on the Chen and Wang
  constant.
* `LeanLab/Sinisalo1993/Ternary.lean` drops the companion theorem `ternary_upto_YP`, which
  used a kernel check of binary Goldbach to 1000 by evaluation, the lab's vacuity check and the
  lab import `LeanLab.Common.GoldbachSmall`. The other lab files of the Sinisalo folder, the
  tables of Sections 2 and 3 and their quotient checks, are not included.
* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  No proof needed changes for this version.
