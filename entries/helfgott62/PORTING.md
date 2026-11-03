# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that this entry needs: three modules under
`LeanLab/Helfgott2013/`, namely `Decomp1538a.lean`, `Decomp1538b.lean` and `Decomp1538c.lean`,
taken from the lab's main branch on its Lean v4.35.0 tree on 2026-11-03. No code from outside the
lab is included, and no PrimeNumberTheoremAnd file.

## Authorship

All the Lean code was written by AI agents. No human wrote or reviewed a proof.

* Claude, Anthropic, lab unit U-1538, 2026-10-26: the three files as a decomposition, with every
  definition, the statements of the leaf lemmas, and the proofs of `lemma61`, `lemma61_paper`,
  `prop62` and `prop62_arcs` from the leaves.
* Codex, OpenAI, lab task 184, 2026-10-30: the nine leaves of `Decomp1538b.lean`, and the new
  theorems `nondecFTC_min`, `prop62_real`, `parseval_exp`, `prop62_real_mass`,
  `hasSum_norm_sq_exp` and `prop62_series_real`.
* Later lab prover agents, among them OMOS: the twelve leaves of `Decomp1538a.lean`, lab task 165,
  and the leaves of `Decomp1538c.lean`, including `parseval_trig`. The lab notes available to the
  packager do not name the agent of each of these leaves, so no finer credit is claimed.
* Claude Opus 5.5, packaging: the changes listed below, `ChallengeHelfgott62.lean`,
  `SolutionHelfgott62.lean` and the metadata.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0. One proof needed a
  change for rc3: in `nondecFTC_min`, `integrableOn_indicator_iff` takes a `MeasurableSet` here,
  not a `NullMeasurableSet`.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; the leading comment became a module doc comment.
* Two declarations that no compared theorem uses were removed: `nondecFTC_id` from part a, a
  vacuity check of `NondecFTC`, and `prop62_exp_real` from part b, the finite coefficient case of
  `prop62_series_real`. A closure walk over the compiled constants confirmed that every other
  declaration of the three files is used by a compared theorem.
* Comments only: the module doc comments were rewritten with the credits above, and the lab's
  status tags on docstrings were removed, since every leaf is now proved. The file `PROGRESS.md`
  of the lab is not part of this entry.
* No statement in the three files was changed.

The namespace `LeanLab.Helfgott2013.U1538` keeps the lab unit number.
