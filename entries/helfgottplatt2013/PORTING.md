# Provenance of the LeanLab files

`LeanLab/` holds the five lab files that the Helfgott and Platt 2013 entry needs. AI agents
wrote them in Steve Hubbard's Lean Lab between 2026-10-16 and 2026-10-22. No code from outside
the lab is included, so the repository NOTICE does not change for this entry. Ternary Goldbach
is Helfgott's theorem and binary Goldbach is open; nothing here claims either.

## Authors of the files

* `LeanLab/Common/Goldbach.lean`: Claude by Anthropic, 2026-10-16. The definitions of sums of
  two and three primes and of binary and ternary Goldbach up to a bound.
* `LeanLab/HelfgottPlatt/Ladder.lean`: Claude by Anthropic, 2026-10-17, lab unit U-0341. One
  step of the ladder reduction.
* `LeanLab/HelfgottPlatt/Proth.lean`: Claude by Anthropic, 2026-10-18, lab unit U-0950.
  Proth's theorem in the direction the computation uses, and the bound T of Theorem 4.1.
* `LeanLab/HelfgottPlatt/HelfgottPlattU6816Sharp.lean`: Claude by Anthropic, 2026-10-21, lab
  unit U-6816. The sharp ladder lemma, the Section 3 algorithm step, the range structure of
  Section 4 and `theorem4_1_of_ranges`.
* `LeanLab/HelfgottPlatt/HelfgottPlattU1455ProthIff.lean`: Claude by Anthropic, 2026-10-22,
  lab unit U-1455. Theorem 2.3 with the Jacobi hypothesis, its converse and `proth_iff`.

## Changes made for this repository

* Every file was converted to module syntax: the line `module`, then `public import` lines,
  the module doc comment and `@[expose] public section`.
* `LeanLab/Common/Goldbach.lean` is an extract of the lab file: it keeps `IsGoldbachSum`,
  `IsTernarySum`, `EvenGoldbachUpTo` and `TernaryGoldbachUpTo` and drops the statements of the
  full conjectures and a Boolean primality and Goldbach test, which no compared theorem uses.
* `LeanLab/HelfgottPlatt/Ladder.lean` is an extract of the lab file: it keeps `ternary_step`
  and `getLastD_cons'` and drops the ladder lemma with gaps at most B - 4 and its Boolean
  checks; with them went the lab import `LeanLab.Verifications.Top50.FastCheck`.
* `LeanLab/HelfgottPlatt/Proth.lean` is an extract of the lab file: it keeps `proth` and `T`
  and drops the Boolean Proth test, its soundness lemma and a kernel checked Proth prime just
  below T; with them went the lab import `LeanLab.Verifications.Pratt`.
* `LeanLab/HelfgottPlatt/HelfgottPlattU6816Sharp.lean` drops `step2_of_ladderStep` and
  `chain_step2_of_chain`, which link the sharp rung condition to the dropped weaker one, and
  the unused import `LeanLab.HelfgottPlatt.PaperNumbers`.
* `LeanLab/HelfgottPlatt/HelfgottPlattU1455ProthIff.lean` is unchanged apart from module
  syntax.
* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  Under rc3, `ring`, `norm_num`, `linear_combination` and a `simp only` with `map_neg` did not
  close goals such as 1 + -1 = 0 in `ZMod p` when `Fact p.Prime` is in scope, so four steps of
  `proth` were rewritten with `rw`, `neg_add_cancel`, `neg_one_sq` and `neg_eq_zero`. No
  statement changed.
