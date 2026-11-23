# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Linnik 1951 entry needs: 522
modules, the import closure of `LeanLab.Linnik1951.Burst1122RouteFinal`, which proves the
compared theorem `linnik1951_decomposed_final_b1122`. AI agents wrote them between 2026-10-16
and 2026-11-22, Claude by Anthropic and Codex by OpenAI as listed below, except the ported code
listed under Ported code. Binary Goldbach is open; nothing here claims it.

Only 156 of the 522 modules contain a declaration that the compared theorem uses, by a
transitive walk of the constants in its statement and proof: 77139 constants, 2567 of them in
`LeanLab`, with no placeholder axiom among them. The other modules come in through the lab's
import lines and are kept so that every file is the lab file with only the changes listed here,
as in the other entries of this repository.

## Where the files come from

* 303 files were already in other entries of this repository and were copied from there. Each
  was compared with a fresh conversion of the current lab file; for 284 of them the Lean code
  is the same and only the module header and comment wording differ. The other 19 carry the
  port fixes or the removals of the entry they come from, listed below. By source: 87 from
  `entries/alsetrishao2024/LeanLab`, 45 from `entries/dudek2014/LeanLab`, 42 from
  `entries/gallagher1975/LeanLab`, 41 from `entries/bombierivinogradov1965/LeanLab`, 24 from
  `entries/goldbachintervalsrh445/LeanLab`, 18 from `entries/goldstonyang2016/LeanLab`, 16 from
  `entries/brun1919/LeanLab`, 8 each from `entries/languascozaccagnini2012/LeanLab` and
  `entries/bordignonstarichkova2024grh/LeanLab`, 7 from `entries/heathbrown1985/LeanLab`, 5
  from `entries/goldstonsuriajaya2021/LeanLab`, and 1 each from
  `entries/kumchevliu2007thm1/LeanLab` and `entries/estermann1938/LeanLab`.
* 31 files under `KadiriLumley2014/` are the conversions prepared for the Kadiri and Lumley 2014
  entry of this repository; their Lean code is the same as a fresh conversion of the lab file.
* The other 188 files were converted from the lab with no change to the Lean code beyond the
  module header and the removal of `#print axioms` lines, except the changes listed below. 93
  of them are the Linnik 1951 files of `Linnik1951/`. For 7 of them, statement files and
  certificate files of other papers, a copy in another entry differs from the current lab file,
  and the lab file was converted afresh.
* `MinimalPartition/Basic.lean` is the Heath-Brown 1985 copy of a lab module whose name carried
  a private person's first name; the module was renamed there to
  `LeanLab.MinimalPartition.Basic` and the import of `Verifications/Statements.lean` follows it.
  The compared theorem does not use it.

## Who wrote the code

* Claude by Anthropic wrote the statement files, the decomposition of Linnik's proof into
  leaves, and the final route: the files `Linnik1951/Prep1121*.lean` and `Burst1122*.lean`,
  including the proof of the Mellin transfer estimate of page 159 from GRH in
  `Burst1122GrhTransfer519.lean`, `Burst1122LogBound.lean`, `Burst1122CahenMellin.lean` and
  `Burst1122LineShift.lean`, the repaired mixed bound in `Prep1121MixedRepair520.lean` with
  `Prep1121DL51Fourier.lean` and `Prep1121DL51Damped.lean`, and the assembly twins in
  `Prep1121RouteWiring.lean` and `Burst1122RouteWiring.lean`.
* Codex by OpenAI, lab tasks 111 to 555: most `Linnik1951/Decomp*.lean` files and their support
  files, such as `CircleSplit111`, `SecondMoment111`, `Supply470`, `Data491` and the files with
  task numbers 280 to 552 in their names, as the lab's `Linnik1951/STATEMENTS.md` records task by
  task. Codex tasks also wrote or edited files of `ChenExplicit/`, `KadiriLumley2014/`,
  `Grimmelt2019/`, `PerelliPintz1992/Decomp1519.lean`, `ExceptionalSet/Lu2010Gauss.lean` and
  `Verifications/OeSHPTables.lean`, as their comments say.
* The `Linnik1951/SPLIT*.lean` files come from the lab's passes that cut a leaf into smaller
  leaves and prove them. The lab's `STATEMENTS.md` records Claude for most units, and some
  leaves from other lab prover runs, under the OMOS pipeline and one with a MiniMax model.
* Claude did the packaging for this repository.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. Same
  files and same changes as in `entries/alsetrishao2024`, `entries/gallagher1975` and
  `entries/heathbrown1985`; see their PORTING.md. `StrongPNT/Bridge.lean` is lab-written.
* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean` and `SelbergBounds.lean`,
  from the same commit, Apache-2.0, written by Arend Mellendijk: the Selberg sieve and its
  bounds. Each file keeps its copyright line and carries a notice of the port. They are the
  copies in `entries/gallagher1975`. `PNTSieve/MertensLower.lean`, `MertensUpper.lean` and
  `MertensProduct.lean` are lab-written.
* `LeanLab/PNTPort/Perron/Sinc.lean` and `Cauchy.lean` are narrow ports from the same commit,
  files `PrimeNumberTheoremAnd/LaplaceInversion.lean` and
  `PrimeNumberTheoremAnd/Mathlib/Topology/MetricSpace/Cauchy.lean`, Apache-2.0, by the
  PrimeNumberTheoremAnd contributors, and `Perron/Cutoff.lean` copies one lemma from
  `LaplaceInversion.lean`, as in `entries/estermann1938`. Their headers refer to a licence file
  in that folder; the licence is the repository's root LICENSE, Apache-2.0, and NOTICE records
  the port.
* Several lab files under `LeanLab/PNTPort/DirichletZF/`, `PsiChi/`, `ExplicitPsi1/` and
  `ZetaZeros/` use or adapt arguments of the StrongPNT files and say so in their headers.
* No code from anthropics/zeta-23-lean is in this entry.

For the root NOTICE, the ported files of this entry are under
`entries/linnik1951/LeanLab/PNTPort/StrongPNT/`, except the lab-written `Bridge.lean`; the
Selberg sieve files by Arend Mellendijk under `entries/linnik1951/LeanLab/PNTSieve/`, except the
lab-written `MertensLower.lean`, `MertensUpper.lean` and `MertensProduct.lean`; and the narrow
ports `entries/linnik1951/LeanLab/PNTPort/Perron/Sinc.lean`, `Cauchy.lean` and `Cutoff.lean`.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  The copied files carry the port fixes of the entries they come from: `Smeas` in place of
  `Smeas.nullMeasurableSet` in `StrongPNT/MellinCalculus.lean`, the re-export of Mathlib's
  `Mathlib.Tactic.LinearCombinationPrime` in `StrongPNT/Tactic/LinearCombinationPrime.lean`,
  the rc3 forms of `memLp_indicator_const` and `MemLp.indicator` in
  `ExceptionalSet/WindowParseval264.lean` and `BhowmikGrimmelt2026/Minor84.lean`, and the fixes
  of `PNTPort/BV/Hyperbolic.lean`, `StrongPNT/MediumPNT.lean`,
  `StrongPNT/ResidueCalcOnRectangles.lean`, `Schnirelmann/Inequality.lean` and
  `SchnirelmannGoldbach/S1/MainTerm.lean`. Three new files needed a change for rc3 or for the
  module system:
  1. `ChenExplicit/At32155.lean`: `set_option maxHeartbeats 1000000 in` on `cAb_geP`, which
     exceeds the default on rc3. The compared theorem does not use it.
  2. `Linnik1951/PrimeArcRadius520.lean` opens private lemmas of `PrimeArcPartial491` and
     `PrimeArcLeaf491` with `open private`. Under the module system private declarations are
     not exported, so the file also takes `import all` of those two modules; its code is
     unchanged.
  3. `Akeno2026/Decomp86.lean`: the route uses one lemma of this lab file,
     `card_divisors_le_rpow`, the divisor bound d of n at most C n^ε, in
     `Linnik1951/SingularSize111.lean`. The rest of the lab file, a proof of Theorem 2.1 of
     Akeno 2026 through fourteen support modules of `Akeno2026/`, does not build on Mathlib rc3:
     it uses `Real.one_add_pow_mul_norm_fourier_le`, which rc3 lacks, and several rewrites fail.
     The file here keeps only that lemma, word for word, under its own name and namespace, with
     `public import Mathlib`, and the fourteen support modules are not in the entry.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* The lab states results of the literature that it has not proved, and some leaves of its own
  decompositions, with placeholder proofs, so that other lab files can cite them. None is used
  by the compared theorem. They were removed from this copy together with every declaration
  that used them, found by a walk of the references and checked by the build:
  * `Linnik1951/Decomp111.lean`: the lab's first assembly `linnik1951_decomposed111`, whose
    statement the compared theorem repeats word for word, and `error_bound111`,
    `covered_square_split111`, `exceptional_square_split111`, `lemma7_split111`,
    `major_truncated_split111`, `major_error_split111`, `exceptional_error_split111`. They rest
    on the old leaves of `Decomp519a` and `Decomp520a` below.
  * `Linnik1951/Decomp519a.lean`: the leaves `grh_mellin_transfer519`, the Mellin transfer of
    page 159, and `lemma2_outer_square519`, and `lemma2_positive_square519`, `lemma2_square519`,
    `nonprincipal_mass519`, `system_character_bound519`, `system_mass519`. The rest of the file
    is used by the route.
  * `Linnik1951/Decomp520a.lean`: the leaves `mixed_bound520`, display 5.5 of page 160 with
    log N to the power 6, and `residue_square_mean520`, and `local_expansion520`,
    `major_expansion520`. The rest of the file is used by the route.
  * `Linnik1951/Prep1121MixedRepair520.lean`: the leaves `principal_fourier_coeff_sq_prep1121`
    and `damped_from_count_prep1121`, and `principal_parseval_prep1121`,
    `prime_damped_chebyshev_prep1121`, `mixed_bound520_repaired_prep1121`. The route uses the
    proved twins of these in `Burst1122RouteWiring.lean`.
  * `Linnik1951/Prep1121RouteWiring.lean`: the twins with suffix `_w1121` of the removed
    declarations above, from `nonprincipal_mass519_w1121` to
    `linnik1951_decomposed_prep1121`.
  * `Linnik1951/Prep1121ResidueMean.lean`: `residue_square_mean1121`.
  * `Linnik1951/Burst1122RouteWiring.lean`: `linnik1951_decomposed_b1122` and
    `local_arc_small_residual_supply552_inst_b1122`, which call the leaf
    `grh_mellin_transfer519` in place of its proof.
  * `Linnik1951/Decomp552e.lean`: `local_arc_small_residual_supply552`.
    `Linnik1951/Lemma6Split111.lean`: `system_mass_split111`.
    `Linnik1951/Major81Split111.lean`: `major_local_expansion_m111`.
  * Older decompositions of the same steps, off the route: `Decomp280b`: `mellin_bound280`,
    `major_error280`, `exceptional_error280`, `error_bound_decomposed280`; `Decomp357a`:
    `mellin_near357`, `mellin_positive_far357`, `mellin_negative_far357`,
    `mellin_bound_decomposed357`; `Decomp357b`: `major_to_truncated357`,
    `major_error_decomposed357`; `Decomp357c`: `exceptional_prime_mass357`,
    `exceptional_error_decomposed357`; `Decomp376b`: `central_pointwise376`,
    `mellin_near_decomposed376`; `Decomp376d`: `major_expansion_remainder376`,
    `major_to_truncated_decomposed376`; `Decomp376f`: `outer_to_kernels376`,
    `mellin_positive_far_decomposed376`; `Decomp442b`: `abstract_outer_kernels442`,
    `outer_to_kernels_decomposed442`, `lemma2_outer_decomposed442`; `Decomp487a`:
    `central_pointwise487`, `mellin_near487`, `mellin_central_general487`; `SPLIT1622_mellin`:
    `mellin_transfer1622`, `lemma2_outer1622`, `mellin_central_general1622`,
    `mellin_outer_general1622`, `mellin_outer_negative1622`, `mellin_radius1622`,
    `mellin_near_recut1622`, `mellin_positive_far_recut1622`, `mellin_bound_recut1622`;
    `SPLIT_abstract_outer_kernels442`: `outer_kernel_mass_bound442`,
    `abstract_outer_kernels442_split`; `SPLIT_grh_mellin_transfer519`: `line_bound_lnL519`,
    `mellin_log_expansion519`, `grh_mellin_transfer519_split`; `SPLIT_lineBound_lnL1622`:
    `continuous_lnL_line1622`, `lineBound_lnL1622_split`; `SPLIT_mellin_transfer1622`:
    `lineBound_lnL1622`, `mellin_lnL_expansion1622`, `mellin_transfer1622_split`.
  * `Linnik/Statements.lean`: `heathBrownPuchta`, `pintzRuzsa1`, `pintzRuzsa2`,
    `johnstonTrudgian_GRH`, and `heathBrownPuchta_GRH`, `gallagher` and `linnik1951`, which used
    them, as in `entries/gallagher1975`. That `linnik1951` is the lab's cited form of the
    statement of this entry; the definitions `LinnikExact`, `LinnikAtMost` and `AllLargeEven` of
    the Challenge are in this file and unchanged.
  * `DERZ1997/Statements.lean`: `zinoviev`, `derz_lemma`, `dtr`, `derz_main`, as in
    `entries/heathbrown1985`. The definition `GRH` of the Challenge is in this file and
    unchanged.
  * Files of other papers, as in the entries they were copied from where they are there:
    `BhowmikGrimmelt2026/Statements.lean`: `theorem31`, `meanSquare38`, `theorem51`, `prop52`,
    `theorem61`, `theorem62`, `theorem63`, `prop64_consequence`, `lemma73`, `lemma74`, `prop75`,
    `prop81`, `theorem82`; `ExceptionalSet/BhowmikGrimmelt2026.lean`: `theorem31`, `theorem51`,
    `prop64_E`, `theorem82`; `ExceptionalSet/Statements.lean`: `montgomeryVaughan`, `li`, `lu`,
    `pintz`, `zhao`; `ChirreHagen2025/Statements.lean`: `theorem1`, `theorem2`, `theorem3`,
    `section5_upper`, `noGoldbach_lower`, `lemma2_4`, `lemma2_1`;
    `RamareSaouter2003/Statements.lean`: `theorem1_stmt`, `theorem3_stmt`,
    `theorem2_row59_stmt`, `corollary1_stmt`; `Tao2012/Statements.lean`: `Theorem1_5`,
    `Theorem1_6`, `theorem1_4`; `Ternary/Statements.lean`: `helfgott_analytic`, `helfgott`,
    `liuWang`, `chenWang`; `Verifications/Statements.lean`: `oesilva_even`,
    `helfgott_platt_ternary`, `richstein`, `dtrs`, `sinisalo`, `saouter`, `gvltr_max`,
    `gvltr_ratio`; `Verifications/OeSHPTables.lean`: `minGB_le_9781`, `maxGap`;
    `LanguascoPerelli1996/Statements.lean`: `theorem1`, `estimate3`, `theorem2`, `theorem3`,
    `hardyLittlewood`, `theorem4`, `corollary1`, `lab_powerBound_of_GMC`, `lab_HL`,
    `chain_of_GMC`; `LanguascoPerelli1996/Decomp597a.lean`: `ramanujan_divisor_envelope`,
    `large_divisor_moment`, `small_divisor_moment`, `lemma2`, `display17`,
    `corrected_major_arc_raw`, `corrected_major_arc`, `corrected_display18`,
    `exceptional_energy_lower`, `energy_bound`, `theorem2_decomposed`;
    `PerelliPintz1992/Statements.lean`: `perelliPintz`, `hardyLittlewood`, `corollary`,
    `zhaoStrength_of_GRH`; `Perelli1996/Statements.lean`: `perelli_theorem1`, `perelli_cor1b`;
    `Perelli1996/Decomp88.lean`: `leaf_weyl`, `leaf_character`, `theorem1`;
    `Perelli1996/Decomp103b.lean`: `leaf_differencing`, `weyl`;
    `ChenExplicit/Decomp1552a.lean`: `prime_reciprocal_eq7`, `prime_reciprocal_quarter`,
    `hP_prime_sum_le`, `chen_log_weight_sum_le`, `eq109_pi`, `eq112_main`, `eq112_tail_abel`,
    `eq112_tail`, `eq116_sum`; `ChenExplicit/Decomp1552b.lean`: `thm31_upper_applied`,
    `eq43_V1`, `eq118`, `lemma72`; `ChenExplicit/Decomp94.lean`: `prime_counting_bounds`,
    `lemma42`; `ChenExplicit/MertensProduct260.lean`: `dusart_mertens_upper`,
    `odd_sieve_product_upper`; `KadiriLumley2014/CostaSplit.lean`: `dusart_theta_k2_005`,
    `costa_pereira_of_leaf`; `KadiriLumley2014/MVInput.lean`: `mv_brun_titchmarsh`;
    `KadiriLumley2014/Decomp92.lean`: `costa_pereira`, `brun_titchmarsh_pointwise`,
    `brun_titchmarsh_tail`, `table_endpoint_budget`, `table_zero_budget`, `table_psi_margin`,
    `table_row_from_leaves`; `KadiriLumley2014/RowInputs.lean`: `row_4e18`, `row_45`, `row_60`,
    `row_150`; `KadiriLumley2014/Statements.lean`: `corollary1_2`.
* Doc comments of 28 files were reworded so that no file outside the Challenge names an
  unfinished proof by the Lean keyword; no code changed. The module doc comment and the
  docstring of `Linnik1951/Burst1122RouteFinal.lean` were rewritten as plain mathematics. Other
  lab docstrings keep the lab's paper numbers, P0093 for Linnik 1951, and its words CONDITIONAL
  ON, which there name the lemmas a proof uses; where those are theorems in this entry, they are
  proved.
* No file in the entry other than the Challenge states anything without proof. There is no
  `native_decide`.

## Route of the proof

The compared theorem has the statement of the lab's `linnik1951_decomposed111`: GRH implies
that some K makes every sufficiently large even number a sum of two primes and at most K powers
of two. Its proof is `linnik1951_decomposed_of_transfer_b1122` of `Burst1122RouteWiring.lean`,
applied to the Mellin transfer estimate of page 159 before equation 5.1, which
`Burst1122GrhTransfer519.lean` proves from GRH with a uniform bound for log L of s and χ in the
strip, page 159, the Cahen-Mellin integral on the line Re s = 2 and a shift of the line of
integration.

The rest follows Linnik's circle method: the character expansion on the major arcs, Lemma 1
of page 156, and Lemma 2, pages 156 to 159, on the Mellin transform of the prime series under
GRH, in `Decomp519a`, `Decomp501a` and `CircleSplit111`; the local expansion of equation 6.4 on
page 161 and the singular series of section 10, in `Decomp520a`, `SingularSize111`, `Decomp111`
and `Burst1122RouteWiring`; the measure of the set where the exponential sum over powers of two
is large, with Gallagher's Lemmas 1 and 2 in `Linnik/Gallagher1975Lemma1.lean` and
`Gallagher1975Lemma2.lean` and the Romanov second moment in `SecondMoment111`; Lemma 6 of
page 166 on Dirichlet approximation; and the conclusion of pages 168 and 169.

The bound for the mixed integral that the route uses, `mixed_bound520_repaired_b1122`, has
log N to the power 7 where display 5.5 on page 160 prints the power 6, and the local expansion
then carries log N to the power 13. The lab could not derive the printed power 6: the printed
display appears to drop a factor q over φ of q. The extra logarithm is absorbed by the power
saving of the major arc error term, so the conclusion is unchanged.

## Build notes

The longest module build is `Dudek2014/SmallRange.lean`, 224 s on two threads, with 34 kernel
`decide` checks of small prime facts; the compared theorem does not use it. No module takes
more than 5 minutes. The largest resident memory seen in the packaging build was 4.7 GB.
