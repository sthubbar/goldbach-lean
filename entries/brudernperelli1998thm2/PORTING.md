# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Brüdern and Perelli 1998 Theorem 2
entry needs: 4 modules under `LeanLab/ExceptionalSet/`, taken from lab main at commit 1669bdd,
the tree that the lab build receipt
`LeanLab/LeanLab/ExceptionalSet/build/20261119T0802Z-29270-dq5.log` checked on Lean and Mathlib
v4.35.0. They prove `U1539.theorem2_of_named_dq5`, Theorem 2 of J. Brüdern and A. Perelli,
Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48, 1998, pages 353 to 378, page 354,
from the paper's Lemma 10 on pages 370 and 371, which is Theorem 1 of A. A. Karacuba,
Estimates for trigonometric sums by Vinogradov's method, and some applications, Proc. Steklov
Inst. Math. 112, 1973, as the paper cites it. Lemma 10 is the explicit hypothesis `Lemma10DQ5`.
Goldbach's problem remains open; nothing here claims it.

The files are `BrudernPerelli1998`, the definition of F and the paper's Theorem 1 as a `Prop`;
`State1539Data264`, the definitions and the statements of the paper's lemmas as `Prop`s;
`Decomp1539a`, the proof of section 8; and `DQ5Decisions`, the conditional theorem. None of
them was in an earlier entry of this repository. No file carries ported code or a private
person's name.

## Who wrote the code

* Claude by Anthropic wrote `BrudernPerelli1998` on 2026-10-17, `State1539Data264` and the
  decomposition of section 8 in `Decomp1539a` in lab unit U-1539, as their headers say.
* Codex by OpenAI, GPT-6 Codex, wrote the proof bodies of the 25 leaf lemmas of `Decomp1539a`
  in lab task 140, with the statements unchanged, as the file header says.
* `DQ5Decisions` comes from the lab run 20261119T0802Z-29270, design queue item DQ5; its
  header says only that AI wrote the Lean code. The lab's architect and design sessions run
  Claude.
* Claude did the packaging for this repository.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  These four files build on rc3 with no change to any proof or statement.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; `#print axioms` lines were dropped.
* The lab states results it has not proved with placeholder proofs, so that other lab files can
  cite them. None is used by the compared theorem, and they were removed from this copy:
  * `ExceptionalSet/BrudernPerelli1998.lean`: `brudernPerelli`, the lab's cited form of the
    paper's Theorem 1. Nothing in this copy used it; the `Prop` `Theorem1` and the proved
    results that take it as an argument stay.
  * `ExceptionalSet/DQ5Decisions.lean`: the two open leaves `leaf_large_value_shift_dq5` and
    `leaf_shift_minor_dq5` of the new split of Lemma 9, the match checks
    `lemma10_named_match_dq5`, `lemma4_named_match_dq5` and `pointwise_named_match_dq5`, which
    use unproved lab statements, and, as not needed for Theorem 2, the proved
    `vacuity_dq5_leaves`, `height_below_window_dq5`, `lemma9_of_dq5_leaves`, `PhiDQ5`, the
    named hypotheses `Lemma4DQ5` and `PointwiseMajorCharacterDQ5` with `lemma4_named_eq_dq5`,
    and `pointwise_lower_of_named_dq5`. The copy keeps `Lemma10DQ5`, `lemma10_named_eq_dq5`,
    which shows by `rfl` that `Lemma10DQ5` is the lab's statement `Lemma10`, and
    `theorem2_of_named_dq5`.
* With those removals `DQ5Decisions` imports `Decomp1539a` directly instead of the lab's
  `State1539` and `UpJ200.Decomp527a`, so `State1539`, which holds the lab's cited forms of the
  paper's Theorem 2 and lemmas, and the 125 other modules that `Decomp527a` brings in are not
  included.
* Comments only: the module comment of `DQ5Decisions` now describes this copy, and lab comments
  of `BrudernPerelli1998` and `Decomp1539a` that spoke of placeholder proofs were reworded.
  Docstrings in `Decomp1539a` still carry the lab's history marks LEAF, ASSEMBLY, CITED and
  CONDITIONAL ON; every such theorem is proved here, as the axiom check of the compared theorem
  shows.

## What is proved and what is assumed

`theorem2_of_named_dq5` assumes exactly `Lemma10DQ5`, Lemma 10 of the paper. Everything else
on its route is proved in `Decomp1539a`: Lemmas 11 to 16 of section 8 on the polynomials
`Q_{s,t}` and `q_s` and the derivatives of F, the choice of the parameters, and the application
of Lemma 10 in `theorem2_of_leaves`. Two slips of section 8 are repaired there, as the file
header says: the lower end of display 56 on page 377 lacks a term `log 2 / log N` that display 53
needs, and the choice `C < γ(1 - θ)` on page 377 must read `1 + C < γ(1 - θ)`. `#print axioms` on
the compared theorem gives exactly `propext`, `Classical.choice` and `Quot.sound`.
