# Provenance of the LeanLab files

`LeanLab/` holds the four lab files that the Kaniecki 1995 entry needs. AI agents wrote them in
Steve Hubbard's Lean Lab between 2026-10-18 and 2026-10-26. No code from outside the lab is
included, so the repository NOTICE does not change for this entry. Binary Goldbach is open;
nothing here claims it.

## Authors of the files

* `LeanLab/KanieckiGap/Lemma7.lean`: Claude by Anthropic, 2026-10-19. The integer gap
  function, the failure of the printed Lemma 7 at 6 and the corrected integer Lemma 7. It also
  keeps the lab's check of the bound of Lemma 6 at e^78 against the value printed in Section 3,
  which is not a compared theorem.
* `LeanLab/Kaniecki1995/Gap.lean`: Claude by Anthropic, 2026-10-18. The real gap function,
  the printed Lemma 7 and its refutation.
* `LeanLab/KanieckiGap/Decomp127.lean` and `LeanLab/KanieckiGap/RealIntervals127.lean`: Codex
  by OpenAI, lab task127, 2026-10-26. The bridge between the integer and the real gap
  function, and the corrected Lemma 7 for real x.

## Changes made for this repository

* Every file was converted to module syntax: the line `module`, then `public import` lines,
  the module doc comment and `@[expose] public section`. The `#print axioms` lines of
  `RealIntervals127.lean` were removed.
* `LeanLab/Kaniecki1995/Gap.lean` is an extract of the lab files
  `LeanLab/Kaniecki1995/Statements.lean` and `LeanLab/Kaniecki1995/Reduction.lean`. It keeps
  `nextPrime`, `lam`, `Lemma7Printed`, `gap_le_lam`, `lam_of_le_seven` and
  `not_lemma7_printed` with their lab text, and drops the other definitions and cited inputs of
  those files, which the compared theorems do not use; with them went the lab imports
  `LeanLab.Common.Goldbach`, `LeanLab.SchnirelmannConstant.Defs`, `Numerics` and `Section3`,
  and the open namespaces the kept declarations do not need.
* `LeanLab/KanieckiGap/Decomp127.lean` is an extract of the lab file of that name. It keeps
  `nextPrime_eq` and `lam_nat_eq` with their lab text and drops the rest, which rests on the
  paper's cited inputs; its imports are now `Lemma7` and `Gap`.
* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  No change to the Lean proofs was needed.
