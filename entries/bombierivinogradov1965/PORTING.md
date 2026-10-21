# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Bombieri-Vinogradov 1965 entry
needs: 117 modules, the import closure of `LeanLab.PNTPort.BVMax.PiPi`. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-21, except as follows. Binary Goldbach is
open; nothing here claims it.

112 of the 117 files are the files of the Heath-Brown 1985 entry of this repository,
`entries/heathbrown1985/LeanLab`, unchanged apart from comment wording, see below; each was
compared with a fresh conversion of the current lab file, and the only differences are the
port fixes and removals listed here. The five files of `LeanLab/PNTPort/BVMax/`, `Grid`,
`Uncond`, `Primes`, `PrimesUncond` and `PiPi`, are new in this entry and were converted from the
lab with no change beyond the module header.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ and the
  prime number theorem with error `x exp(-c √log x)`. Changes: every `@[blueprint ...]`
  attribute, `blueprint_comment` and `import Architect` removed; import paths renamed to
  `LeanLab.PNTPort.StrongPNT.*`; and these fixes, made in the lab for Mathlib v4.35.0:
  1. `StrongPNT/Tactic/LinearCombinationPrime.lean` re-exports Mathlib's
     `Mathlib.Tactic.LinearCombinationPrime`, present in Mathlib v4.35.0-rc3, which this
     repository uses; the lab, on v4.35.0, carries a copy of the v4.34.0 file instead.
  2. MellinCalculus: the lab's v4.35.0 fix `Smeas.nullMeasurableSet` is reverted to `Smeas`
     for rc3.
  3. EulerMaclaurin: an explicit `measurable_from_nat.comp Nat.measurable_floor` term replaces a
     `fun_prop` call.
  4. StrongPNT `BorelCaratheodoryDeriv`: the two half-differences rewritten before `field_simp`.
* `StrongPNT/Bridge.lean` is lab-written.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  The port needed the two changes above and `set_option maxHeartbeats 1000000` on
  `BV/Hyperbolic.lean`'s `hyperbolic_large_sieve`.

* Comments that described the lab's placeholder convention were reworded so that the word for
  a placeholder proof no longer appears in any file outside the Challenge file; no Lean code
  changed.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files. Some files that needed
  lemmas outside their own Mathlib imports take a private `import Mathlib`.
* MediumPNT: `convert this using 3; apply uIoc_of_le` became `rw [Set.uIoc_of_le ...]`, since the
  module system changed how far `convert` unfolds.
* The lab states results of the literature that it has not proved with a placeholder proof,
  so other lab files can cite them. None of those is used by this entry, and they were removed
  from this copy together with the declarations that depended on them, so no file here other
  than the Challenge file has an unfinished proof. Removed, as in the Heath-Brown 1985 entry:
  `DERZ1997.zinoviev`, `derz_lemma`, `dtr`, `derz_main`; `ExceptionalSet.montgomeryVaughan`,
  `li`, `lu`, `pintz`, `zhao`; `HeathBrown1985.sigma3_eventually_of_siegelWalfisz`,
  `boundSigma3_of_siegelWalfisz`; `Tao2012.theorem1_5`, `theorem1_6`, `theorem8_2`,
  `small_range`, `theorem1_4`; `Ternary.chenWang`, `liuWang`, `helfgott_analytic`, `helfgott`;
  `Verifications.oesilva_even`, `helfgott_platt_ternary`, `richstein`, `dtrs`, `sinisalo`,
  `saouter`, `gvltr_max`, `gvltr_ratio`. The lab's scaffolding module for least Goldbach
  partitions is renamed `MinimalPartition.Basic`.

## Lab-written mathematics in the closure

Siegel's theorem and the zero-free region for Dirichlet L-functions, `PNTPort/DirichletZF/`;
the large sieve, `PNTPort/LargeSieve/`; Perron's formula pieces, `PNTPort/Perron/`; the
explicit formula and Siegel-Walfisz, `PNTPort/PsiChi/`; Bombieri-Vinogradov at y = x,
`PNTPort/BV/`; the maximum over y <= x and the passage to θ and π, `PNTPort/BVMax/`; and
Heath-Brown's argument, `HeathBrown1985/`, which the closure contains through shared
definitions such as `HeathBrown1985.psi`.
