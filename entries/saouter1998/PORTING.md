# Provenance of the Lean files

`GoldbachLean/Saouter1998/` is the part of Steve Hubbard's Lean Lab that this entry needs, taken from
the lab's Lean v4.35.0 tree, 11 files. AI agents wrote them between 2026-10-16 and 2026-11-01:
Claude by Anthropic for most files, Codex agents for Theorem 1 and the statement of Lemma 1, and
Gemini and Antigravity agents for parts of the Lemma 1 proof. No PrimeNumberTheoremAnd code and no
other outside code enters this entry, so the root NOTICE needs no line for it.

## Where each file comes from

* `Goldbach.lean`: lab `Common/Goldbach.lean`, without the two conjecture definitions, which are unused.
* `ModPow.lean`: `pm` and `pm_cast` of lab `Verifications/PrattCertificates.lean`, plus the new lemma
  `castHom_neg_one`. The Pratt certificates of that file and the tables it serves are not included.
* `Proth.lean`: lab `HelfgottPlatt/Proth.lean`, without the top rung of Helfgott and Platt.
* `Ladder.lean`: `ternary_step` and `getLastD_cons'` of lab `HelfgottPlatt/Ladder.lean`, and `Step2`
  and the sharp ladder lemma of lab `HelfgottPlatt/HelfgottPlattU6816Sharp.lean`. The Section 4 ranges
  and the unused B - 4 ladder lemma are removed, which also removes the import of
  `Verifications/Top50/FastCheck`.
* `Paper.lean`, `Theorem1.lean`, `Theorem2.lean`, `Lemma1.lean`: the lab files of those names.
  The unused Prop `MainResult` is removed; `TernaryGoldbachUpTo (10 ^ 20)` says the same.
* `Lemma1Proof.lean`: lab `Saouter1998/DecompJ345.lean`, renamed.
* `Table1.lean`: lab `Saouter1998/Table1.lean` and `Table1Thm2.lean` together. The Lucas certificates
  are removed, since the test of Theorem 2 certifies the same 100 rungs.
* `ProthLadder.lean`: lab `Saouter1998/ProthLadder1597.lean`, renamed.

The lab's kernel chain to 10^14, its `Block`, `Chk`, `B9` and `Prefix73` files and `Lucas.lean` are not
in this entry, and no compared theorem depends on them.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, as every other entry does.
* Namespaces moved from `LeanLab.*` to `GoldbachLean` and `GoldbachLean.Saouter1998.*`:
  `Verifications.Pratt` became `ModPow`, `HelfgottPlatt.Proth` became `Proth`,
  `HelfgottPlatt.U6816` became `Ladder`, `ProthLadder1597` became `ProthLadder`.
* Every file is in the Lean module system: a `module` header, `public import`,
  `@[expose] public section`, and a module doc comment. `#print axioms` lines are removed. Doc
  comments were reworded and lab bookkeeping removed; statements are unchanged.
* Proof changes for rc3: on v4.35.0-rc3 a `Fact p.Prime` in context makes `ring`, `norm_num`,
  `linear_combination` and `map_neg` fail on `-1` in `ZMod p`, as the field instance does not unify
  with `ZMod.commRing` at reducible transparency. `two_pow_dvd` of Theorem 2 and `proth` now use
  `castHom_neg_one`, `neg_add_cancel`, `neg_one_sq` and `neg_ne_zero` as terms.

## Kernel cost

Primality proofs use `decide +kernel`, never `native_decide`. The 25 Proth rungs, the 100 Table 1
rungs and the first and last primes each cost one modular power on numbers below 2^67.
