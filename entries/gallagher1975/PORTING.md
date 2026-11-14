# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Gallagher 1975 entry needs: 366
modules, the import closure of `LeanLab.Linnik.Decomp1532c`, lab commit cb28c013f, which proves
`theorem1_of_leaves` and `theorem2_of_leaves`. AI agents wrote them between 2026-10-16 and
2026-11-05, Claude by Anthropic except as listed below. Binary Goldbach is open; nothing here
claims it.

Only 187 of the 366 modules contain a declaration that the two compared theorems use, by a
transitive walk of the constants in their statements and proofs. The other modules come in
through the lab's import lines and are kept so that every file is the lab file with only the
changes listed here; trimming the imports file by file would have meant editing many more files.

163 of the 366 files were already in other entries of this repository and were copied from
there. Each was compared with a fresh conversion of the current lab file, and the only
differences are the module header and comment rewordings: 53 files from
`entries/renyi1948/LeanLab`, 29 from `entries/hardylittlewood1923/LeanLab`, 27 from
`entries/goldstonsuriajaya2021/LeanLab`, 18 from `entries/alsetrishao2024/LeanLab`, 15 from
`entries/schnirelmann1933/LeanLab`, 11 from `entries/romanov1934/LeanLab`, 6 from
`entries/heathbrown1985/LeanLab`, 2 from `entries/dudek2017/LeanLab`, and 1 each from
`entries/languascozaccagnini2012/LeanLab` and `entries/mann1942/LeanLab`.

22 more files were copied from other entries in the state those entries publish, with the port
fixes, removals and comment rewordings listed in the PORTING.md of the entry they come from,
which apply here unchanged: 8 from `entries/hardylittlewood1923/LeanLab`, files of
`HardyLittlewood1923/` and `VanDerCorput1939/Statements`; 4 from
`entries/goldstonsuriajaya2021/LeanLab`, the StrongPNT files `MediumPNT`, `MellinCalculus`, with
`Smeas` in place of the lab's `Smeas.nullMeasurableSet`, `ResidueCalcOnRectangles` and
`Tactic/LinearCombinationPrime`, which re-exports Mathlib's `Mathlib.Tactic.LinearCombinationPrime`,
present in rc3; 4 from `entries/heathbrown1985/LeanLab`, the Statements files of `DERZ1997/`,
`ExceptionalSet/`, `Tao2012/` and `Verifications/`; 4 from `entries/schnirelmann1933/LeanLab`;
and 1 each from `entries/brun1919/LeanLab` and `entries/bordignonstarichkova2024grh/LeanLab`. `Verifications/Statements` and
`MinimalPartition/Basic` are the Heath-Brown 1985 copies: the lab module of that content carries a
private person's first name and was renamed `LeanLab.MinimalPartition.Basic` there, and it is not
used by the compared theorems.

`HardyLittlewood1923/U1479Split` and `U1482ZeroCount` were converted afresh from the lab, since
the Hardy-Littlewood 1923 copies lack `ZeroCountUnit` and `zeroCountUnit`, which
`Linnik/ExplicitFormula/` uses. The other 179 files are new in this repository and were converted
from the lab with no change to the Lean code beyond the module header and the removal of
`#print axioms` lines, except the changes listed below.

## Who wrote the code

* Claude by Anthropic wrote the statements, the decomposition of Gallagher's proof into leaves,
  and most proofs, in lab units such as U-1532, files `Linnik/Decomp1532a`, `Decomp1532b` and
  `Decomp1532c`, and U-6810 to U-6834, files `Linnik/Gallagher1975*.lean`.
* Codex by OpenAI, lab task507: the three leaves that Gallagher cites from Montgomery and Vaughan
  1975, the Gauss sum estimate behind display 5 and the two singular series estimates of display
  11, in `Linnik/Decomp507a.lean`.
* Codex, lab tasks 189 and 195: proof additions in `Linnik/Decomp1532b.lean`; task 262:
  `Linnik/Decomp1532b2.lean`; task 69: `Zinoviev1997/TotientTail.lean`; tasks 46 and 48: edits to
  `BhowmikGrimmelt2026/Statements.lean` and `LPZ2007/Statements.lean`, as their comments say.
* A later lab prover run under OMOS repaired one leaf statement in `Linnik/Decomp1532b.lean`,
  `gallagher_zero_detector_of_turan`, lab unit U-1619, as its docstring says.
* Claude did the packaging for this repository.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. Same
  files and same changes as in the Heath-Brown 1985 and Hardy-Littlewood 1923 entries; see their
  PORTING.md. `StrongPNT/Bridge.lean` is lab-written.
* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean`, `SelbergBounds.lean` and
  `BrunTitchmarsh.lean`, from the same commit, Apache-2.0, written by Arend Mellendijk: the
  Selberg sieve, its bounds and the Brun-Titchmarsh inequality. Each file keeps its copyright line
  and carries a notice of the port. They are the copies in the Hardy-Littlewood 1923 entry.
  `PNTSieve/BrunTitchmarshAP.lean`, `MertensUpper.lean` and `MertensProduct.lean` are
  lab-written.
* `LeanLab/Linnik/HilbertCosecant.lean` adapts the matrix proof skeleton of the files
  Quadratic, EigenIdentity, Eigen and Duality of anthropics/zeta-23-lean, commit
  16a5ce41304fcdaea4e0be7c132e1c361dc26da5, `zeta23/Zeta23/MV`, Apache-2.0, Copyright Anthropic,
  PBC, to the Hilbert inequality of Montgomery and Vaughan 1974. The file keeps its copyright and
  license notice.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  The copied files carry the port fixes of the entries they come from. Five new files needed a
  fix for rc3:
  1. `Linnik/Decomp1532b2.lean`, `summable_poisson_twist`: the lemma
     `LSeries.abscissaOfAbsConv_logPowMul` is spelled `LSeries.absicssaOfAbsConv_logPowMul` in
     rc3.
  2. `RieselVaughan1983/Lemma13Red.lean`: in `odd_of_primitive_three`, `simp` after
     `rw [← map_mul]` became `rw [← map_mul, show ((-1 : ZMod 3) * -1) = 1 by decide, map_one]`;
     in `term_three_nonneg`, `rw [hsum]` became `erw [hsum]`.
  3. `ExceptionalSet/WindowParseval264.lean`: two calls of `memLp_indicator_const` take
     `measurableSet_Ico` in place of `measurableSet_Ico.nullMeasurableSet`, as rc3's signature
     asks.
  4. `BhowmikGrimmelt2026/Minor84.lean`: the same for `MemLp.indicator`, with
     `(measurableSet_majorArc84 X R).compl`.
  5. `Linnik/MajorArcEnergy/Display1517.lean`: `set_option maxHeartbeats 1000000 in` on
     `major_arc_energy_exceptional_split`, which exceeds the default on rc3.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* The lab states results of the literature that it has not proved with placeholder proofs, so
  that other lab files can cite them. None is used by the compared theorems, and they were
  removed from this copy together with the declarations that used them:
  * `BhowmikGrimmelt2026/Statements.lean`: `theorem31`, `meanSquare38`, `theorem51`, `prop52`,
    `theorem61`, `theorem62`, `bound65`, `theorem63`, `lemma73`, `lemma74`, `lemma76`, `prop75`,
    `facts81`, `prop81`, `theorem82`, and `prop64_consequence`, which used them.
  * `LPZ2007/Statements.lean`: `eq3`, `minorBound`, `minorL2`, `eq7`, `jutila`, `lemma41`,
    `cor42`, `realPrimitiveModulus`, `iwaniec`, `kpBound`, `gallagherAsymp`. The definitions
    `tuples` and `pow2sum` of the Challenge are in this file and unchanged.
  * `LanguascoPerelli1996/Statements.lean`: `theorem1`, `estimate3`, `theorem2`, `theorem3`,
    `hardyLittlewood`, `theorem4`, and `chain_of_GMC`, `lab_HL`, `corollary1` and
    `lab_powerBound_of_GMC`, which used them.
  * `LanguascoPerelli1996/Decomp381a.lean`: the leaf `partial_remainder_mean_square` and
    `theorem4_decomposed`, which used it.
  * `Linnik/Statements.lean`: `heathBrownPuchta`, `pintzRuzsa1`, `pintzRuzsa2`,
    `johnstonTrudgian_GRH`, and `heathBrownPuchta_GRH`, `gallagher` and `linnik1951`, which used
    them. That `gallagher` is the lab's cited form of a different statement, at most `K` powers
    of 2 for two primes, not the theorems of this entry.
  * `Linnik/Decomp486c.lean`: the off-route leaf `short_interval_mean_decay_exceptional`.
  * `Linnik/MajorArcEnergy/Leaves1517.lean`: the off-route leaf `exceptional_weight_bound`,
    which the lab proves in another form in `Display17.lean`.
  * `HardyLittlewood1923/U1479Split.lean`: `explicitFormulaLog_of_split` and
    `printedA_form_all_U1479`, which use cited statements of the Hardy-Littlewood 1923 lab files
    that are removed in the copies used here; `ExplicitFormulaLog` was dropped from an `open`
    line. `HardyLittlewood1923/U1482ZeroCount.lean`: `printedA_form_all_U1482`, for the same
    reason.
* Doc comments of 20 files were reworded so that no file outside the Challenge names an
  unfinished proof by the Lean keyword; no code changed. In `Linnik/Decomp1532c.lean` the module
  doc comment and the docstrings of `display6Large_of_leaves`, `theorem1_of_leaves` and
  `theorem2_of_leaves` said "CONDITIONAL ON the leaves"; every leaf is proved, so they now say
  the assembly is from the proved leaves. Elsewhere "CONDITIONAL ON" in a lab docstring names the
  lemmas a proof uses; where those are theorems, they are proved.
* No file in the entry other than the Challenge states anything without proof. There is no
  `native_decide`.

## Lab-written mathematics in the closure

Gallagher's proof for g = 2, `Linnik/`: the major arcs of Section 1, display 2 to display 17,
with the character expansion, the zero density estimate near 1 of Gallagher 1970, Page's theorem,
Siegel's theorem and the exceptional character, `Decomp1532b`, `Decomp466a` to `Decomp486c`,
`MajorArcEnergy/` and `ExplicitFormula/`; Lemma 2 on the large values of
`G(α) = Σ e(2^ν α)`, `Gallagher1975Lemma2`, with the digit Lemmas 1 and 3,
`Gallagher1975Lemma1` and `Gallagher1975Lemma3`; Lemma 11 on the minor arcs, with Vinogradov's
bound from `PNTPort/Vinogradov/`; Lemma 12, from the lab's Romanov second moment,
`Romanov/GallagherBridge.lean`; display 6 on page 139 and Theorems 1 and 2,
`Linnik/Decomp1532c.lean`, `U7204Theorem1`, `U7206Display6` and `Gallagher1975Thm2*.lean`. The
inputs below them include the multiplicative large sieve, `PNTPort/LargeSieve/`, the Hilbert
inequality of Montgomery and Vaughan 1974, `Linnik/HilbertCosecant.lean`, the three estimates of
Montgomery and Vaughan 1975 that Gallagher cites, `Linnik/Decomp507a.lean`, the zero-free region
for Dirichlet L-functions, `PNTPort/DirichletZF/`, and the prime number theorem with classical
error term, `PNTPort/StrongPNT/`.

The uses of `decide` in the modules used by the compared theorems check small facts such as
`Nat.log 2 8 = 3`, `#(oddPairs 10) = 5` or membership in finite sets of small numbers. Elsewhere
in the closure, `MinimalPartition/Basic.lean` checks with three `decide +kernel` calls that 751
is the smallest prime p with 3807404 - p prime; no compared theorem uses it, and it builds in a
few seconds.
