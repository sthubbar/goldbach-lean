# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Kumchev and Liu 2007 Theorem 1 entry
needs: 112 modules, the import closure of `LeanLab.KumchevLiu2007.Thm1Written` after the removals
listed below, taken from the lab tree of 2026-11-18 that the lab build receipt
`LeanLab/KumchevLiu2007/build/20261118T0802Z-4078.log` checked on Lean and Mathlib v4.35.0. They
prove `Task129W.thm1_written_of_eq33`, Theorem 1 of A. V. Kumchev and J. Y. Liu, Sums of primes
and squares of primes in short intervals, arXiv 0801.0130, display 9 on page 2, on the range
X to the 7/18 + ε at most H at most X to the 1 - ε that the proof on page 16 writes, from the
paper's Proposition 1, display 33, which is the explicit hypothesis `Eq33Hyp`. The same file
proves `thm1_full_of_written_small_eps` and `written_range_nonempty`. Goldbach type questions
remain open; nothing here claims them.

By folder: 27 files of `KumchevLiu2007/`, 72 of `PNTPort/`, 4 of `HeathBrown1985/`, 4 of
`PNTSieve/`, 3 of `AlmostPrimes/`, and one each of `ChenExplicit` and `Common`.

85 of the 112 files were already in other entries of this repository and were copied from
there: 78 from `entries/tolev2009/LeanLab` and 7 from `entries/renyi1948/LeanLab`, the three
files of `AlmostPrimes/` and the four of `PNTSieve/`. Each was compared with a fresh conversion of
the current lab file. 80 differ only in the module header and comments. The other 5 carry the
port fixes listed in the PORTING.md of the Tolev 2009 entry and of the entries it names, which
apply here unchanged: `PNTPort/StrongPNT/MediumPNT`, `MellinCalculus`,
`ResidueCalcOnRectangles` and `Tactic/LinearCombinationPrime`, which only re-exports Mathlib's
`Mathlib.Tactic.LinearCombinationPrime`, and `PNTPort/BV/Hyperbolic`. No copied file carries a
private person's name. The 27 files of `KumchevLiu2007/` are new in this repository and were
converted from the lab with no change to the Lean code beyond the module header and the removal
of `#print axioms` lines, except the changes listed below.

## Who wrote the code

* Claude by Anthropic wrote `KumchevLiu2007/Statements` on 2026-10-17 and the three
  `Decomp1534` files in lab unit U-1534, as their headers say, and the lab's decomposition of the
  proof into leaf lemmas.
* The other `KumchevLiu2007/` files come from lab tasks 129, 506, 516, 542 and 634 and the route
  bursts of 2026-11-12 to 2026-11-18, and `Thm1Written` from the lab run 20261118T0802Z-4078.
  Their headers say only that AI wrote the Lean code and do not name the agent. The lab's
  architect and burst sessions run Claude; leaf lemmas of the lab are also closed by Codex by
  OpenAI and other lab prover agents, so some of these leaves may be theirs.
* Claude also wrote the earlier lab files of `HeathBrown1985/`, `PNTSieve/`, `AlmostPrimes/`
  and `PNTPort/` outside `StrongPNT/` and the Perron ports, as the entries they come from say,
  and did the packaging for this repository.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 17 files, 16 of them from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. Same
  files and same changes as in the Tolev 2009, Bombieri-Vinogradov 1965 and Alsetri-Shao 2024
  entries; see their PORTING.md. `StrongPNT/Bridge.lean` is lab-written.
* `LeanLab/PNTPort/Perron/Sinc.lean`, `Cauchy.lean` and one lemma of `Cutoff.lean` are narrow
  ports from the same PrimeNumberTheoremAnd commit, as the repository NOTICE says.
* The Vaughan identity and Siegel-Walfisz machinery come from the lab's own Heath-Brown 1985
  formalization, and the Bombieri-Vinogradov theorem from `PNTPort/BV/` and `PNTPort/BVMax/`, both
  lab-written and published in earlier entries of this repository. The residual estimate of
  Proposition 2 uses them.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  On rc3 the Mathlib instance `instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent`, which makes a
  simple nilpotent additive group commutative, is found for `ZMod p` under `Fact p.Prime`, and
  the resulting negation is not seen as the ring's negation by `ring`, `simp` and `simpa`. The
  fix removes that instance locally with `attribute [-instance]`: for the three theorems
  `locSol3_large` and `locSol2_large` of `Decomp1534b` and `A2_prime_dvd` of `Decomp1534c`, and
  for the whole file in `Decomp129a`, `Decomp129s`, `Decomp506a`, `Decomp506bBase`,
  `Decomp506d`, `Decomp506g`, `Decomp542a` and `PrimeError634Base`, each with a comment. No
  proof or statement was changed otherwise.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* The lab states results it has not proved with placeholder proofs, so that other lab files can
  cite them, and states the paper's other results as cited `Prop` definitions. The lab receipt
  shows that `Task129W.thm1_written_from_leaves`, `Task129.thm1_from_leaves` and
  `Task129.eq53_prop1` depend on `sorryAx`, through the unproved leaves of the display 33 route
  in `BlockInputs628`, `LargeEpsilon628`, `Decomp556a`, `Decomp556b`, `Eq33RouteB` and
  `Eq33RouteD`. None is used by the compared theorems, and they were removed from this copy
  together with the declarations that used them:
  * `KumchevLiu2007/Thm1Written.lean`: `thm1_written_from_leaves`, Theorem 1 on the written range
    from the lab's unproved display 53 leaf.
  * `KumchevLiu2007/Decomp129.lean`: `kumchev_liu_thm1`, the lab's cited form of Theorem 1 on
    the printed range H at most X for every ε, and its only proof `thm1_from_leaves`; the leaves
    `eq53_prop1` and `eq53_large_eps`, and `eq53_full_range` and `circle_input`, which used them.
  * `KumchevLiu2007/Decomp516a.lean`: `eq33_weighted_mean_square`, `eq53_prop1` and
    `eq53_large_eps`, which rest on the unproved block inputs, and with them the import of
    `LargeEpsilon628`.
  * `KumchevLiu2007/Statements.lean`: the cited statements `kumchev_liu_thm2`,
    `kumchev_liu_thm3` and `kumchev_liu_cor1` of Theorems 2 and 3 and Corollary 1, which have no
    proof, and the ten results derived from them, `thm1_consequence_of_thm2`,
    `zhan_liu_E2_of_thm2`, `thm3_consequence_of_thm3`, `mikawa_peneva_E3_of_thm3`,
    `cor1_consequence_of_cor1`, `exists_H2_of_thm2`, `exists_H3_of_thm3`, `exists_H4_of_cor1`,
    `exists_H3_eps_of_thm3` and `exists_H4_eps_of_cor1`, with the empty section header above
    them.
* With the import of `LargeEpsilon628` gone, 35 modules of the lab closure are no longer
  imported and are not included: the display 33 route `Block628`, `BlockInputs628`,
  `BlockKernel628`, `Decomp556a`, `Decomp556b`, `Decomp556d`, `Eq33RouteA`, `Eq33RouteB`,
  `Eq33RouteD`, `Eq33Window1117`, `Gallagher634`, `InitialRange634`, `Kernel634Base` and
  `LargeEpsilon628` of `KumchevLiu2007/`, and `BHP1997/Gallagher605`, four files of `Linnik/`,
  `PNTPort/Gallagher/Basic`, two files of `PNTPort/LargeSieve/`, ten of `PNTPort/Vinogradov/`
  and three of `Routes/`.
* Comments only: the module comment of `Thm1Written` now describes this copy, a comment in
  `Leaves129` says its three leaves are proved, and lab comments that spoke of placeholder
  proofs were reworded. Some docstrings of proved leaves in `Decomp129` still carry the lab's
  history marks SPLIT LEAF and CITED; every such theorem is proved here, as the axiom check of
  the compared theorems shows.

## What is proved and what is assumed

`thm1_written_of_eq33` assumes exactly `Eq33Hyp`, display 33 of Proposition 1 on page 8 with
the weights of page 15, on the written range. Everything else on its route is proved: the
Chebyshev step from display 33 to display 53, `eq53_of_eq33`; the singular series lower bound
from displays 48 and 49 and Lemma 3.8, `eq48_49_series_lower`; the residual estimate of
Proposition 2 on pages 16 and 17, `residual_input`; and the circle method assembly of displays
53 to 55, `circle_input_of_estimates`. `#print axioms` on each compared theorem gives exactly
`propext`, `Classical.choice` and `Quot.sound`.
