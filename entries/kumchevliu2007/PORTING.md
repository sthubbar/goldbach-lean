# Provenance of the LeanLab files

`LeanLab/` holds the one lab file that the Kumchev and Liu 2007 entry needs. AI agents wrote it
in Steve Hubbard's Lean Lab. No code from outside the lab is included, so the repository NOTICE
does not change for this entry. Binary Goldbach is open; nothing here claims it.

## Authors of the files

* `LeanLab/KumchevLiu2007/PrintedConjecture.lean`: Claude by Anthropic. The definitions
  `IsPrimePlusPrimeSq` and `InH2` come from the lab file `LeanLab/KumchevLiu2007/Statements.lean`,
  2026-10-17. The lemma `sq_form`, the definition `conjecture_printed`, the family lemmas
  `inH2_family` and `not_form_family` and the theorem `conjecture_printed_false` come from the
  lab file `LeanLab/KumchevLiu2007/Novelty1612.lean`, lab unit U-1612, 2026-11-03.

## Changes made for this repository

* The file was converted to module syntax: the line `module`, then `public import Mathlib`,
  the module doc comment and `@[expose] public section`.
* It is an extract. From `Statements.lean` it keeps `IsPrimePlusPrimeSq` and `InH2` with their
  lab text and drops the other definitions, the cited statements of Theorems 2 and 3 and
  Corollary 1, and the results derived from them, which the compared theorems do not use; with
  them went the lab import `LeanLab.Common.Goldbach`, the line `open Real` and the local
  instance `Classical.propDecidable`, which the kept declarations do not need.
* From `Novelty1612.lean` it keeps the declarations listed above with their lab text, and drops
  the cited remark `kumchev_liu_thm2_03275` on the exponent 0.3275 and its target theorem,
  which have no proof, together with `thm2_of_03275`, `shortExcBound_empty`, the open repaired
  conjecture `conjecture_nonsquare`, `conj_hyp_74` and `nonsquare_of_printed`.
* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  No change to the Lean proofs was needed.
