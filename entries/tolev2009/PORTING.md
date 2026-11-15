# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Tolev 2009 entry needs: 181
modules, the import closure of `LeanLab.Tolev2009.Decomp83` and
`LeanLab.Tolev2009.FinishAssembly1112`, taken from the lab tree of 2026-11-15 that the lab build
receipt 20261115T0803Z-26991 checked on Lean and Mathlib v4.35.0. They prove
`Decomp83.published_assembly` and `FinishAssembly1112.published_assembly_finished`, the main
Theorem of D. I. Tolev, arXiv 0902.2669, display 5 on page 2, with Halupczok's printed singular
series. Binary Goldbach is open; nothing here claims it.

By folder: 64 files of `Tolev2009/`, 76 of `PNTPort/`, 28 of `HeathBrown1985/`, 4 of
`ChenExplicit/`, 2 of `Tao2012/`, and one each of `Common`, `DERZ1997`, `ExceptionalSet`,
`MinimalPartition`, `SchnirelmannConstant`, `Ternary` and `Verifications`.

117 of the 181 files were already in other entries of this repository and were copied from
there: 69 from `entries/alsetrishao2024/LeanLab` and 47 from
`entries/bombierivinogradov1965/LeanLab`, and `MinimalPartition/Basic.lean` from
`entries/heathbrown1985/LeanLab`. Each was compared with a fresh conversion of the current lab
file. 107 differ only in the module header and comments. The other 10 carry the port fixes and
removals listed in the PORTING.md of the entry they come from, which apply here unchanged:
`PNTPort/StrongPNT/MediumPNT`, `MellinCalculus`, `ResidueCalcOnRectangles` and
`Tactic/LinearCombinationPrime`, `PNTPort/BV/Hyperbolic`, and the Statements files of
`DERZ1997/`, `ExceptionalSet/`, `Tao2012/`, `Ternary/` and `Verifications/`. The lab module
with the content of `MinimalPartition/Basic` carries a private person's first name; the
Heath-Brown 1985 entry renamed it, and `Verifications/Statements` imports it under the new name.
The 64 files of `Tolev2009/` are new in this repository and were converted from the lab with no
change to the Lean code beyond the module header and the removal of `#print axioms` lines,
except the changes listed below.

## Who wrote the code

* Codex by OpenAI wrote most of `Tolev2009/`, in lab tasks: task45, the faithful restatement,
  the dyadic and L2 bookkeeping, the minor arc reduction and the identification with
  Halupczok's printed series, files `BlockEstimates`, `Displays19to20`, `DivisorMoment`,
  `Dyadic`, `FinalReduction`, `L2Bound`, `MinorArcBound`, `PublishedTheorem` and
  `SeriesIdentification`; task83, `Decomp83`; task286, `Decomp286a` and `Decomp286b`;
  task310, `Decomp310a` and `Decomp310c`; task314, `ArcGeometry314`, `Base314a`,
  `CoefficientMoment314`, `Decomp314b`, `Decomp314c` and `Integral314`; task336, the three
  `Decomp336` files; task341, the twelve files ending in 341; task346, the twelve files ending in
  346; task355, the five files ending in 355; task424, the three `Decomp424` files.
* A Lean Lab prover agent running Mistral's leanstral model, lab task151: `Decomp310b`.
* Claude by Anthropic wrote the statement file `Statements`, `Faithful`, `Displays14to16`, and in
  the route burst of 2026-11-12 `Major83`, `Sup83Group`, `Sup83Heath`, `Sup83Split` and
  `FinishAssembly1112`. Claude also wrote the earlier lab files of `HeathBrown1985/`, `PNTPort/`
  outside `StrongPNT/`, and the other folders, as their entries say, and did the packaging for
  this repository.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 17 files, 16 of them from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. Same
  files and same changes as in the Bombieri-Vinogradov 1965 and Alsetri-Shao 2024 entries; see
  their PORTING.md. `StrongPNT/Bridge.lean` is lab-written.
* Several lab-written files under `PNTPort/DirichletZF/`, `PNTPort/Perron/` and `PNTPort/PsiChi/`
  apply results of those ported files, as their comments say.
* The Vaughan identity and Siegel-Walfisz machinery come from the lab's own Heath-Brown 1985
  formalization, `HeathBrown1985/`, and the Bombieri-Vinogradov theorem from `PNTPort/BV/` and
  `PNTPort/BVMax/`, both lab-written and published in earlier entries of this repository.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  Three new files needed a fix for rc3: in `Tolev2009/Decomp286a`, `CoefficientMoment314` and
  `Decomp314b`, the proof of `seven_reciprocal_moments`, and of `seven_reciprocal_moments_cm`
  in `Decomp314b`, used `gcongr` and `ring` on powers such as `Hn N ^ 4096`, which time out on
  rc3. Both steps are replaced by explicit terms, `mul_le_mul` with `pow_le_pow_left₀`, and
  `rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]`. The statements are unchanged.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* The lab states results it has not proved with placeholder proofs, so that other lab files can
  cite them. None is used by the compared theorems, and they were removed from this copy together
  with the declarations that used them:
  * `Tolev2009/Statements.lean`: `the_theorem`, the lab's cited form of the Theorem at an opaque
    constant `halupczokS`, and that opaque constant itself. The explicit series of the compared
    theorems is `SeriesIdentification.halupczokSeries`.
  * `Tolev2009/Decomp83.lean`: `legacy_transfer` and `legacy_assembly`, and
    `Tolev2009/FinishAssembly1112.lean`: `legacy_assembly_finished`, which state the Theorem for
    the opaque `halupczokS` under an identity hypothesis.
  * `Tolev2009/Decomp286a.lean`: the off-route leaf `progression_replacement` and the lemma
    `major_arc_leaf` of that file, which used it. The compared theorems use the proved
    `MajorArc341.progression_replacement` instead, through `Major83`.
  * The Statements files of `DERZ1997/`, `ExceptionalSet/`, `Tao2012/`, `Ternary/` and
    `Verifications/` are the copies of the earlier entries named above, with the removals listed
    in their PORTING.md.
* Doc comments of 10 `Tolev2009/` files were reworded so that no file outside the Challenge names
  an unfinished proof by the Lean keyword, and the docstrings of `Decomp83`,
  `published_assembly`, `major_arc_leaf`, `minor_arc_sup_leaf` and the module doc of
  `FinishAssembly1112` now say that both analytic inputs are proved; no code changed. In the
  `Tolev2009/` doc comments the lab's old work labels, which marked inputs as open or results as
  conditional while the work was in progress, were reworded to say the input is proved or the
  result is derived from the named lemmas; only comments changed. The compared theorems depend
  on the axioms `propext`, `Classical.choice` and `Quot.sound` only, so every input they use is
  proved.
* No file in the entry other than the Challenge states anything without proof. There is no
  `native_decide`. The uses of `decide` in `Tolev2009/` check facts about `Fin 3`; elsewhere in
  the closure, `MinimalPartition/Basic.lean` checks with three `decide +kernel` calls that 751 is
  the smallest prime p with 3807404 - p prime; no compared theorem uses it, and it builds in a
  few seconds.

## Lab-written mathematics in the closure

Tolev's proof follows the circle method with `Q = L^{20A}` and `τ = N Q^{-1}`. The major arcs,
display 9 on page 4, are `MajorArc341` and `Major83`, with the progression replacement, the
singular integral error and the tail of the singular series, after Tolev 1999 and Halupczok 2008,
and a quantitative Bombieri-Vinogradov theorem in `QuantitativeBV346` built on `PNTPort/BV/`. The
minor arcs, display 12, are `L2Bound`, `Displays19to20`, `MinorArcBound`, `FinalReduction` and
the supremum bound of `Sup83Split`, from the Type I and Type II estimates of Tolev 1999 pages 83 to
86 and the prime decomposition of page 71 Lemma 4, with the Vaughan identity of `HeathBrown1985/`.
`SeriesIdentification` proves that the lab's singular series equals Halupczok's printed one, page
11 of Halupczok 2008, on positive moduli and reduced residues, which are the only ones in `𝓔*`.
