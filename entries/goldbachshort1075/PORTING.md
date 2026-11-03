# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that this entry needs: 7 modules, the import
closure of `LeanLab.GoldbachShort78.Short1075`, taken from the lab's Lean v4.35.0 tree and trimmed.
No code is ported from outside the lab. AI agents wrote every file:

* Claude, Anthropic: `Common/Goldbach.lean`, `GoldbachShort78/Statements.lean` and
  `GoldbachShort78/Short1075.lean`, which holds `goldbach_short_1075`, `windowCount_of_backward`,
  `exponent_1075`, `LiRow052`.
* Codex, OpenAI: `GoldbachShort78/Growth.lean`, `GoldbachShort78/LiNormalization.lean`, which holds
  `LiPrintedExceptionalCount`, and `GoldbachShort78/Tiling.lean`.
* Gemini, Google, with fixes by Claude: `GoldbachShort78/LiCounts.lean`.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, as every other entry
  here does. No proof needed a change for rc3. One redundant `simpa` became `simp`.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; the leading comment became a module doc comment; `#print axioms`
  lines were removed; docstrings were reworded and internal run labels removed.
* The namespace `LeanLab.GoldbachShort78` keeps the name of the lab folder where the proofs were
  written, which began as a project on a zero free half plane. Nothing about that half plane
  remains in this entry.
* `Short1075.lean` is the lab's main file under a new name. `Tiling.lean` is the lab's file of
  tiling lemmas under a new name.

## Removed from the copy

Each of these is unused by the compared theorems.

* From `Common/Goldbach.lean`: everything except `IsGoldbachSum`, so the ternary statements, the
  primality test and the Goldbach checker.
* From `Statements.lean`: the half plane statement and the two routes built on it, the primes in
  all intervals definition and the lemmas on it, and the arithmetic of other exponents.
* From `Growth.lean`, `LiCounts.lean` and `LiNormalization.lean`: the lemmas and the cited
  statements behind the exponent `21/860`, in particular the Baker, Harman and Pintz input.
* From `Tiling.lean`: the Baker, Harman and Pintz count and every lemma that used it, the only
  other cited statement in those files.
* One further file of the lab with no bearing on these theorems, whole.
* From the main file: two small instances that tested the inner inequalities at `n = 3` and `x = 8`.

The only cited statements left in the entry are `LiRow052` and `LiPrintedExceptionalCount`, which
appear as explicit hypotheses of `goldbach_short_1075`.
