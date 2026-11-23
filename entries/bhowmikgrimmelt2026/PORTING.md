# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Bhowmik and Grimmelt 2026 Theorem 3.1
entry needs: 349 modules, the import closure of `LeanLab.BhowmikGrimmelt2026.Theorem31Ported1122`,
taken from the lab tree of 2026-11-22 on Lean and Mathlib v4.35.0, lab branch
`BhowmikGrimmelt2026-integrate1122b`. They prove `theorem31_ported1122`, Theorem 3.1 on page 9
of G. Bhowmik and L. Grimmelt, The exceptional set of the Goldbach problem, arXiv 2607.27282 v2,
from its three hypotheses `Θ < 3/4`, `ZeroBound Θ` and `0 < ε` and nothing else. Binary
Goldbach remains open; nothing here claims it.

Only 108 of the 349 modules contain a declaration that the compared theorem uses, by a
transitive walk of the constants in its statement and proof. The other modules come in through
the lab's import lines and are kept so that every file is the lab file with only the changes
listed here.

182 of the 349 files are, apart from comments and the module header, the same as a file already
in another entry of this repository or of the entries packaged alongside it, and were copied from
there: 57 from `entries/alsetrishao2024`, 42 from `entries/dudek2014`, 21 from
`entries/gallagher1975`, 15 from `entries/goldbachintervalsrh445`, 6 from
`entries/bombierivinogradov1965`, 4 from `entries/bordignonstarichkova2024grh`, 31 from
`entries/kadirilumley2014`, 5 from `entries/linnik1951` and 1 from `entries/song2020`. Six more
files were copied from `entries/gallagher1975` in the state that entry publishes, with its rc3
fixes, listed below. `MinimalPartition/Basic.lean` is the Heath-Brown 1985 copy, see below. The
other 160 files were converted from the lab with no change to the Lean code beyond the module
header and the removal of `#print axioms` lines, except the changes listed below.

## Who wrote the code

* Claude by Anthropic wrote most files: the statements of the paper in
  `BhowmikGrimmelt2026/Statements.lean` on 2026-10-18, the decomposition of Theorem 3.1 into
  leaves and their proofs in `BhowmikGrimmelt2026/`, the circle method mean square, the zero
  expansion of the major arcs and the final wiring in `Prep1121BGFinish.lean` and
  `Theorem31Ported1122.lean`, and the explicit formula of Davenport, Multiplicative Number
  Theory, chapter 19, for primitive characters in `PNTPort/ExplicitPsi1/Char*1122*.lean`.
  The folder name `PNTPort` is a lab name; those files are lab code built on the ported
  residue calculus.
* Codex by OpenAI, lab tasks 64, 92, 259 and 301: the files of `KadiriLumley2014/` that say so;
  task 193: the section of concrete instances in `DERZ1997/Decomp1529a.lean`; task 69:
  `Zinoviev1997/TotientTail.lean`; task 46: edits to `BhowmikGrimmelt2026/Statements.lean`;
  task 219: the port of `BakerHarmanPintz1997/PortedVanDerCorput.lean`, as the file headers say.
* Some files come from the lab's route runs and repairs, whose headers say only that AI wrote
  the Lean code. The lab's architect and route sessions run Claude; leaves of the lab are also
  closed by Codex and other lab prover agents, so some of these proofs may be theirs.
* Claude did the packaging for this repository.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: Mellin calculus, residue calculus on rectangles, bounds for ζ, the
  conjugation symmetry of ζ'/ζ and the strong prime number theorem. Each file carries a notice;
  `Tactic/LinearCombinationPrime.lean` only re-exports Mathlib's tactic. They are the files and
  changes of the Gallagher 1975 and Dudek 2014 entries.
* `LeanLab/PNTPort/Perron/Sinc.lean` and `Cauchy.lean`, narrow ports from the same commit,
  files `LaplaceInversion.lean` and `Mathlib/Topology/MetricSpace/Cauchy.lean`, as in the
  Estermann 1938 and Bombieri-Vinogradov 1965 entries.
* `LeanLab/Ported/Zeta23/RvM/ReZeroCount.lean`, a narrow port of one lemma,
  `finite_zeros_closedBall`, from anthropics/formal-math, commit
  e1a4e6508154ea59f030480661590a9fe3018011, file `zeta23/Zeta23/RvM/ReZeroCount.lean`, Copyright
  2026 Anthropic, PBC, Apache-2.0. Two sections of `LeanLab/Routes/Decomp1551b.lean`, the
  digamma series and the harmonic logarithm limit, port or adapt code from the files
  `zeta23/Zeta23/GammaFacts/Series.lean` and `StirlingVert.lean` of the same commit, with the
  same copyright and license. Each carries its notice.
* `LeanLab/BakerHarmanPintz1997/PortedVanDerCorput.lean`, the Kusmin-Landau inequality and van
  der Corput's second derivative test, from the Prove2Me submission
  `ExponentialSums.vdC_second_derivative`, Prove2Me id 1038fb61-45dc-46e6-9a1c-862d2aa8430c,
  https://beta.prove2.me, Copyright 2026 Jason Hickey, authors Jason Hickey with Claude,
  Apache-2.0. It is the copy of the Song 2020 entry and keeps its notice.
* One local lemma in `LeanLab/Routes/Decomp1551a.lean`, inside `left_edge_limit`, adapts
  Mathlib's `Mathlib/NumberTheory/LSeries/RiemannZetaLogDeriv.lean`, Apache-2.0, and says so.
* No file of Arend Mellendijk's Selberg sieve, `PNTSieve`, is included.

Proposed paths for the repository NOTICE, to add to the existing paragraphs:
`entries/bhowmikgrimmelt2026/LeanLab/PNTPort/StrongPNT/` to the PrimeNumberTheoremAnd list;
`entries/bhowmikgrimmelt2026/LeanLab/PNTPort/Perron/Sinc.lean` and `Cauchy.lean` to the
paragraph on the narrow Perron ports; and two new paragraphs:

> The file entries/bhowmikgrimmelt2026/LeanLab/Ported/Zeta23/RvM/ReZeroCount.lean and two
> sections of entries/bhowmikgrimmelt2026/LeanLab/Routes/Decomp1551b.lean port code from
> anthropics/formal-math, https://github.com/anthropics/formal-math, commit
> e1a4e6508154ea59f030480661590a9fe3018011, files zeta23/Zeta23/RvM/ReZeroCount.lean,
> zeta23/Zeta23/GammaFacts/Series.lean and StirlingVert.lean, Copyright 2026 Anthropic, PBC,
> licensed under the Apache License, Version 2.0; each carries its copyright and license notice.
>
> The file entries/bhowmikgrimmelt2026/LeanLab/BakerHarmanPintz1997/PortedVanDerCorput.lean is
> ported from the Prove2Me submission ExponentialSums.vdC_second_derivative, Copyright 2026
> Jason Hickey, licensed under the Apache License, Version 2.0; the file carries its copyright
> and license notice.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  Six files are the Gallagher 1975 copies with their rc3 fixes: `BhowmikGrimmelt2026/Minor84`,
  `ExceptionalSet/WindowParseval264`, `PNTPort/StrongPNT/MediumPNT`, `MellinCalculus`,
  `ResidueCalcOnRectangles` and `Tactic/LinearCombinationPrime`. Six new files needed a fix for
  rc3; no statement of the paper changed:
  1. `BhowmikGrimmelt2026/Decomp540a.lean`: rc3 has no `completedRiemannZeta_conj`. Two lemmas
     were added before `completedZeta_half_conj_540`: `completedRiemannZeta_conj_of_re_pos`, the
     conjugation symmetry of the completed zeta function for `0 < Re s`, proved from
     `riemannZeta_conj` and `Gamma_conj`, and `conj_completedRiemannZeta_half_add_mul_I`, that it
     is real on the critical line, from the functional equation. The one use of the missing
     lemma now calls the first.
  2. `BhowmikGrimmelt2026/Decomp515a.lean`: rc3 has no Hardy Z function `hardyZ`. The two lemmas
     stated with it, `hardyZ_phase515` and `hardyZ_phase_real515`, which nothing uses, were
     removed, and `hardyXi_eq_zero_iff515` is reproved from the completed zeta function and
     `Gammaℝ`, with its statement unchanged.
  3. `PNTPort/ExplicitPsi1/CharRect1122.lean`: rc3 has no `Set.preimage_singleton`; the last
     step of the finiteness of the zeros in a rectangle now uses `Set.Finite.subset`.
  4. `HelfgottMajor/StripBound123.lean`: `set_option maxHeartbeats 1000000 in` on
     `strip_bound_of_le`.
  5. `HelfgottMajor/DQSaddleSegmentBound.lean`: in `c1_mul_radius` and twice in the proofs of
     the A.26 bounds, `field_simp` on rc3 leaves a goal `a * b / a = b` or `a * b / b = a`, now
     closed with `mul_div_cancel_left₀` or `mul_div_cancel_right₀`.
  6. `HelfgottMajor/Decomp639Contour.lean`: in `a33_c1_mul_rho_u`, the factors
     `v ^ 2 - v` and `v ^ 2 - 1` are factored before `field_simp`.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* The lab module `KaiScaffolding/MinimalPartition` carries a private person's first name. It is
  replaced by the Heath-Brown 1985 copy `LeanLab/MinimalPartition/Basic.lean`, with namespace
  `LeanLab.MinimalPartition`, and `Verifications/Statements.lean` imports it under that name. The
  compared theorem does not use it.
* The lab states results of the literature that it has not proved with placeholder proofs, so
  that other lab files can cite them. None is used by the compared theorem. Every declaration
  whose proof depends on one, found by a walk of the constants of the built library, was removed
  with its exact source range, 166 in all:
  * `BhowmikGrimmelt2026/Statements.lean`: `theorem31`, the lab's cited form of Theorem 3.1,
    which the compared theorem replaces; `meanSquare38`, `theorem51`, `prop52`, `theorem61`,
    `theorem62`, `theorem63`, `lemma73`, `lemma74`, `prop75`, `prop81`, `theorem82`, and
    `prop64_consequence`, which used them. The definitions `ZeroBound` and `Theorem31` of the
    Challenge are in this file and unchanged.
  * `BhowmikGrimmelt2026/`, the older route of Theorem 3.1 through the cited explicit formula,
    which the compared theorem replaces by the proved one: `Decomp150a.lean`:
    `theorem31_decomposed150`, `mean_square150`, `major_minor_mean_square150`,
    `mean_square150_even_part`, `meanSquare38_even_energy`, `meanSquare38_split`;
    `Decomp508a.lean`: `primitive_psi_zero_expansion508`, `psi_zero_expansion504`;
    `MeanSquareLeaves150.lean`: `major_arc_uniform150`; `RouteMode508.lean`:
    `oscillatory_zero_modes508_route`; `SPLIT_davenport_integer_formula592.lean`:
    `davenport_integer_half_formula592`, the cited formula that
    `davenport_integer_half_formula592_ported` proves, and `davenport_integer_formula592`;
    `SPLIT_oscillatory_zero_modes508.lean`: `zero_mode_large_frequency508`,
    `zero_reciprocal_multiplicity508`, `oscillatory_zero_modes508_split`;
    `SPLIT_primitive_psi_zero_expansion508.lean`: `nonprincipal_psi_zero_bound508`,
    `primitive_psi_zero_expansion508_split`; `Theorem31Inputs150.lean`:
    `majorArcUniform150_of_leaf`. `Prep1121BGFinish.lean` keeps its proved copies of these
    steps, which take the explicit formula as an argument.
  * `DERZ1997/Statements.lean`: `zinoviev`, `derz_lemma`, `dtr`, `derz_main`.
    `DERZ1997/Decomp1529a.lean`: `rosser_strict193`, `zetaZeros_eq_empty`, `rvm_upper`,
    `rvm_lower`, `primitive_zero_count193`, `zetaZeros_four_eq_empty193`, `zeta_small_nonreal193`,
    `zeta_count_envelope193`, `LZeros_count`, `LZeros_recip_sum`, `window_count`,
    `zero_recip_sum`, and one `example` that used `zetaZeros_eq_empty`.
    `DERZ1997/Decomp1529b.lean`: `explicit_formula_zeta`, `good_height`, and one such `example`.
  * `ExceptionalSet/Statements.lean`: `montgomeryVaughan`, `li`, `lu`, `pintz`, `zhao`.
    `GRHComputations/Statements.lean`: `platt`.
  * `HelfgottArcs/Statements.lean`: `minorArcs_small`, `minorArcs_large`, `major_1_1`,
    `major_1_1'`, `major_1_2`, `major_1_3`, `major_1_4`, `major_1_4_q1`, `helfgottInput`.
  * `HelfgottMajor/`: `Decomp123.lean`: `gaussian_explicit_estimate`, `theorem_1_1`;
    `Decomp269a.lean`: `explicit_formula_remainder`, `low_zero_bound`, `high_zero_bound`,
    `gaussian_explicit_estimate`; `Decomp457b.lean`: `principal_log_weight_budget`,
    `principal_log_weight_L2`, `principal_contour_bound`; `Decomp526a.lean`:
    `signed_count_bound`, `middle_mass_small_product`, `middle_mass_small_height`,
    `middle_mass_bound`, `middle_mass_large`; `DecompJ1124.lean`: `explicit_formula_remainder_E`,
    `explicit_formula_remainder`; `Gaussian123Base.lean`: `lemma_4_1_gaussian`,
    `residue_log_derivative_bound`, `tail_mass_of_corollary`, `tail_mass_summable_of_corollary`,
    `tail_mass_integral`, `tail_shell_count_le_quadratic`, `explicit_formula_of_pieces`,
    `residueMain_bound`, `middle_mass_bound`, `very_low_mass_bound`;
    `Lemma41Corrected123.lean`: `gaussian_explicit_estimate_corrected`, `low_zero_bound_slack`,
    `explicit_formula_remainder_corrected`, `residue_main_conj_bound_of_zeros`;
    `Lemma41Leaf123.lean`: `lemma_4_1_gaussian_corrected`; `MiddleSlack123.lean`:
    `middle_mass_bound_slack`; `PolyaVinogradov123.lean`: `polya_vinogradov_4_20`;
    `Residue123.lean`: `charSumMax_le`, `log_derivative_norm_le_of_zeros`;
    `ResidueZeros123.lean`: `residueMain_bound_of_zeros`, `explicit_formula_of_pieces_of_zeros`,
    `residue_log_derivative_bound_of_zeros`; `SPLIT_explicit_formula_remainder_E.lean`: five
    declarations `explicit_formula_remainder_E_split` and `..._principal_conductor`,
    `..._small_shift`, `..._large_shift`, `..._zero_frequency`;
    `SPLIT_residue_log_derivative_bound.lean`: `log_derivative_norm_le`,
    `residue_log_derivative_bound_split`; `SplitGaussian123.lean`: `low_zero_bound`,
    `high_zero_bound`, `explicit_formula_remainder`; `ZeroCount1623.lean`: `book_zero_count`,
    `arxiv_zero_count`, `zero_count_two_sided`, `very_low_count`, `strip_count`.
  * `KadiriLumley2014/`: `CostaSplit.lean`: `dusart_theta_k2_005`, `costa_pereira_of_leaf`;
    `Decomp92.lean`: `table_endpoint_budget`, `table_zero_budget`, `table_psi_margin`,
    `table_row_from_leaves`, `brun_titchmarsh_pointwise`, `brun_titchmarsh_tail`,
    `costa_pereira`; `MVInput.lean`: `mv_brun_titchmarsh`; `RowInputs.lean`: `row_45`, `row_60`,
    `row_150`, `row_4e18`; `Statements.lean`: `corollary1_2`.
  * `LanguascoPerelli1996/Statements.lean`: `theorem1`, `estimate3`, `theorem2`, `theorem3`,
    `hardyLittlewood`, `theorem4`, `chain_of_GMC`, `lab_HL`, `corollary1`,
    `lab_powerBound_of_GMC`. `LanguascoPerelli1996/Decomp597a.lean`: `ramanujan_divisor_envelope`,
    `large_divisor_moment`, `small_divisor_moment`, `corrected_major_arc_raw`,
    `corrected_major_arc`, `corrected_display18`, `display17`, `exceptional_energy_lower`,
    `energy_bound`, `lemma2`, `theorem2_decomposed`.
  * `Routes/Decomp1551b.lean`: `hadamard_logDeriv_order_one`, `hadamard_re_sum_of`,
    `hadamardK_gZ_of_RH`.
  * `Verifications/Statements.lean`: `oesilva_even`, `helfgott_platt_ternary`, `richstein`,
    `dtrs`, `sinisalo`, `saouter`, `gvltr_max`, `gvltr_ratio`. `Verifications/OeSHPTables.lean`:
    `minGB_le_9781`, `maxGap`.
* Comments only: the module doc comment and the two docstrings of
  `BhowmikGrimmelt2026/Theorem31Ported1122.lean` said that the theorem was conditional on one
  leaf of the port, the contour shift at a good height; that leaf is proved in
  `PNTPort/ExplicitPsi1/CharContour1122.lean`, so they now say that the theorem is proved from
  its three hypotheses only. Comments of 17 files that named an unfinished proof by the Lean
  keyword were reworded, and three license notes that pointed at license files in the lab tree
  now point at the LICENSE file at the root of this repository. Elsewhere docstrings keep the
  lab's marks such as LEAF, CITED and CONDITIONAL ON; every theorem that remains is proved, as
  the axiom check of the compared theorem shows. No file in the entry other than the Challenge
  states anything without proof. There is no `native_decide`.

## What is proved and what is assumed

`theorem31_ported1122 : Theorem31` takes `Θ`, `Θ < 3/4`, `ZeroBound Θ`, `ε` and `0 < ε` and
proves `PowerBound (2 * Θ - 1 / 2 + ε)`. `#print axioms` gives exactly `propext`,
`Classical.choice` and `Quot.sound`. The route: the explicit formula for `ψ(x, χ)` with a
primitive nonprincipal character, Davenport chapter 19 pages 115 to 118, in
`PNTPort/ExplicitPsi1/`, with the Perron formula of chapter 17, the good heights of chapter 16,
the trivial zeros and the constant `b(χ)`; the expansion of the major arcs over the zeros under
`ZeroBound Θ` in `Prep1121BGFinish.lean` and the `Route*508` files; the mean square of the
minor arcs and the singular series in `Decomp150a`, `Decomp84` and their leaves;
the count of the exceptional set, `card_calE`; and Hardy's zero on the critical line in
`Decomp515a` and `Decomp540a`, used to see that `Θ ≥ 1/2` whenever `ZeroBound Θ` holds.

## Build notes

`Routes/Decomp1551c.lean`, which the compared theorem does not use but which is in the import
closure, took about 600 seconds to build with two threads: it checks a finite certified
computation of `ζ(1/2 + it) ≠ 0` for `0 ≤ t < 14` by `interval_cases` and `decide +kernel` under
`maxHeartbeats` up to 80000000. No other file took more than 3 minutes.
