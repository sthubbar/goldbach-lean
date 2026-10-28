# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Halupczok 2012 entry needs: 16
modules, the import closure of `LeanLab.Halupczok2012.U1510Final` after the import change below,
namely 15 files of `Halupczok2012/` and `PrimePowerWindow/Count`. AI agents, Claude by
Anthropic, wrote all of them between 2026-10-17 and 2026-10-25. There is no ported code from
another project in this entry, so the repository NOTICE does not list it. Binary Goldbach is
open; nothing here claims it.

All 16 files are new in this repository. They were converted from the lab with no change to the
Lean code beyond the module header and the removal of `#print axioms` lines, except the changes
listed below.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`.
* `Halupczok2012/U1496PP.lean`, lemma `logpow_le`: one `by positivity` side goal, which hits the
  maximum recursion depth on v4.35.0-rc3, was replaced by the term `pow_nonneg hu0 _`. This is
  the only change to a proof.
* `Halupczok2012/Statements.lean`: the lab keeps cited, unproved statements of the paper's other
  results next to its definitions. None is used by the compared theorems, and they were removed
  together with the definitions and small lemmas only they use:
  - the unproved statements `theorem_6`, `theorem_7`, `theorem_7_max`, `theorem_2`,
    `theorem_2_max`, `corollary_1`, `corollary_2`, `corollary_3` and `corollary_4`: Theorems 6
    and 7 and Corollaries 1 to 4 of the paper in its arXiv numbering, a supplement to each of
    Theorems 2 and 7, and the lab placeholder for Theorem 2, which the proved `theorem2_U1510`
    replaces;
  - the definitions `IsP`, `Sqa`, `thm6LHS`, `Theorem6`, `thm7Inner`, `Theorem7`,
    `Theorem7Max`, `Theorem2Max`, `Cor1Sol`, `Corollary1`, `cor2Exc`, `Corollary2`, `Cor3Sol`,
    `Corollary3`, `Λ3`, `Cor4Range`, `Cor4Sol` and `Corollary4`;
  - the proved lemmas `isP_mono`, `isP_prime`, `isP_mul`, `cor1Sol_of_cor3Sol`,
    `ternary_of_cor1Sol`, `ternary_of_cor3Sol`, `ternary_of_cor4Sol`, `goldbach_of_cor2_sol`,
    `three_used_ternary`, `three_used_binary`, `S_odd`, `Sqa_noncoprime`, `cor3Sol_45`,
    `cor1Sol_45` and one `example` checked by `decide`.
  With them gone the file no longer needs `LeanLab.Common.Goldbach`, so that import was removed.
  The kept definitions `kRange`, `binSumAP`, `binSum`, `twinC`, `S`, `T`, `ternSum`, `Thm2Hyp`
  and `Theorem2` and the lemma `prime_cong_noncoprime` are unchanged; the module doc comment was
  rewritten.
* `Halupczok2012/NonCoprime.lean`: the file was renamed from its lab name, its
  import in `U1439Thm2Reduction` updated, and its module doc comment and one docstring were
  rewritten to state the defect and the repair from the published text alone; no other code
  changed.
* `Halupczok2012/U1510Final.lean`: the module doc comment and one docstring were rewritten; no
  code changed.
* `Halupczok2012/U1439Thm2Reduction.lean`: three doc comments that called `MainTermMV` and
  `Theorem3` unproved or unused were updated, since later files of the closure derive
  `MainTermMV` from `Theorem3`; no code changed.
* Comments that cite a numbered display of a paper write it as display 2 rather than with the
  number in parentheses; no code changed.
* No file in the entry other than the Challenge states anything without proof. The two cited
  results are `Prop` definitions, `PPS1984Remark` and `PP1993Goldbach`, taken as hypotheses of
  the compared theorems.

## Lab-written mathematics in the closure

The paper's proof of its Theorem 1.2: `U1439Combin` and `U1439Thm2Reduction` split the ternary
sum into a binary part, bounded from the paper's Theorem 2.3 by Cauchy-Schwarz and an elementary
divisor moment, without the paper's Lemma 1, and a main term part; `U1452MainTermMV`,
`U1457SingSeries`, `U1460SingSeriesProof`, `U1460Reduction`, `U1462Analytic`, `U1462Pointwise`
and `U1462Tails` bound the main term part from the paper's Theorem 2.1 by the Chinese remainder
theorem, the truncation of the singular series, the identification of its Euler product with
`T` and Rankin's trick, with no cited input for the singular series. `NonCoprime` proves that
the non-coprime terms vanish. `U1495PPS` derives the paper's Theorem 2.1 from the Remark of
Perelli, Pintz and Salerno 1984, and `U1493Theorem5Min` with `U1496PP` derive its Theorem 2.3
from the Goldbach analogue of Theorem 3 of Perelli and Pintz 1993. `PrimePowerWindow/Count`
counts prime powers in a window. There is no `native_decide` in the closure.
