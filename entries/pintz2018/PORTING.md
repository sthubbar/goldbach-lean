# Provenance of the LeanLab files

`LeanLab/Pintz2018/` holds the lab files of the Pintz 2018 folder that have complete proofs.
AI agents wrote them in Steve Hubbard's Lean Lab between 2026-10-18 and 2026-10-26. No code
from outside the lab is included, so the repository NOTICE does not change for this entry.
Theorem 1 of the paper, the bound X to the power 0.72 for the Goldbach exceptional set, is not
proved here; the zero density theorems of the paper and its analytic estimate 7.20 are not
proved either, and 7.20 is a hypothesis of the Theorem J statement.

## Authors of the files

* `ExpBounds.lean`, `Section9.lean`, `Numbers.lean`: Claude by Anthropic, cloud run of
  2026-10-18, lab unit U-5014, verified again by a Claude run on 2026-10-19, lab unit U-1016.
  Taylor bounds for the exponential, the basic inequality 9.4 and the printed numbers of
  Section 9, Case 8 included.
* `Statements.lean`: drafted by Gemini by Google on 2026-10-22, lab task45, and corrected by a
  Claude review the same day. The packaging agent kept only the three definitions the other
  files use and rewrote two docstrings.
* `Decomp117.lean`, `Decomp117b.lean`, `Ordered117.lean`, `Curvature117.lean`,
  `Greedy117.lean`, `Residual117.lean`, `Density117.lean`, `Discrete117.lean`,
  `Laplace117.lean`, `Monotonicity117.lean`, `Instances117.lean`: Codex by OpenAI, lab task117,
  2026-10-26. Theorem J from 7.20, the exchange proof of Theorem K, budget tightness and the
  residual equation, the Laplace form of the cost, the condition of Theorem L, the
  monotonicity statements 5.31 and 5.33, and nonempty instances.

## Changes made for this repository

* Every file was converted to module syntax: the line `module`, then `public import` lines,
  the module doc comment and `@[expose] public section`.
* `Statements.lean` keeps `TheoremK_OptimalChoice`, `TheoremJ_bound` and `TheoremL_condition`.
  It drops the lab's statements of Theorems B, D, E, F, G, I, Lemmas 6 and 7, Corollary 2 and
  their vacuity check, which no proof here uses and which are cited, not proved.
* `Certificates117.lean` is left out: its two numerical certificates for Section 9 Case 1 and
  for Lemma 5 are not proved in the lab.
* `Decomp117b.lean`, lemma `leaf_pair_exchange`: three `field_simp` steps that close on Lean
  v4.35.0 do not close on v4.35.0-rc3, so each is replaced by an explicit rewrite with
  `add_div`, `div_mul_eq_mul_div` and `div_eq_iff` followed by `ring`. The statement is
  unchanged.
* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
