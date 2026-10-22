# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Goldston-Suriajaya 2021 entry needs:
60 modules, the import closure of `LeanLab.GoldbachAverage.U1440Theorem1Full`. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-21, except as follows.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. These
  files are byte for byte the copies in the Languasco-Zaccagnini 2012, Goldston-Yang 2016,
  Granville 2007 and Heath-Brown 1985 entries of this repository, with the same changes: every
  `@[blueprint ...]` attribute, `blueprint_comment` and `import Architect` removed; import paths
  renamed to `LeanLab.PNTPort.StrongPNT.*`; and these fixes:
  1. `StrongPNT/Tactic/LinearCombinationPrime.lean` re-exports Mathlib's
     `Mathlib.Tactic.LinearCombinationPrime`, present in Mathlib v4.35.0-rc3.
  2. MellinCalculus: the lab's v4.35.0 fix `Smeas.nullMeasurableSet` is reverted to `Smeas`.
  3. EulerMaclaurin: an explicit `measurable_from_nat.comp Nat.measurable_floor` term replaces a
     `fun_prop` call.
  4. StrongPNT `BorelCaratheodoryDeriv`: the two half-differences rewritten before `field_simp`.
  5. MediumPNT: `convert this using 3; apply uIoc_of_le` became `rw [Set.uIoc_of_le ...]`.
* `StrongPNT/ZetaConj.lean`, one of those 16 files, gives `logDerivZeta_conj`, used here to show
  that `(ζ'/ζ)(-1)` is real.
* `StrongPNT/Bridge.lean` is lab-written, the same file as in the Heath-Brown 1985 entry.
* Everything else, including `PNTPort/ZetaZeros/` and `PNTPort/ExplicitPsi1/`, is lab-written.
  `ExplicitPsi1/TrivialRect.lean` applies the ported residue theorem
  `RectangleIntegral'_eq_sumResiduesIn` but is itself lab-written.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files; `#print axioms` lines
  were removed.
* 55 of the 60 files are byte for byte the copies already in `entries/languascozaccagnini2012`,
  whose PORTING.md lists their changes from the lab; the removals that concern files of this
  entry are repeated below. The other five are new here:
  - `PNTPort/ExplicitPsi1/LeftZeta.lean`, `TrivialRect.lean` and `TrivialLimit.lean`, the
    explicit formula for `ψ₁` with the trivial zeros, converted from the lab sources with no change
    to the Lean code.
  - `PNTPort/ExplicitPsi1/TrivialTerms.lean`, new: the declarations `tb`, `tterm_eq`, `tb_nonneg`,
    `y_tb_le`, `summable_tb` and `y_tsum_tb_bounds`, taken unchanged from the lab file
    `PNTPort/ExplicitPsi1/DudekLemma4.lean`. The rest of that file concerns Dudek 2014 and is
    not needed, so the entry does not import the Dudek 2014, Helfgott 2013 and `ZetaTwo` files.
  - `GoldbachAverage/U1440Theorem1Full.lean`, the lab proof of Theorem 1 eq. 11. Changes: its
    import of `DudekLemma4` became `TrivialTerms`, and `StrongPNT/ZetaConj` and
    `ExplicitPsi1/Log2Pi` are imported directly; the faithfulness check
    `example : type_of% gs_theorem1` refers to the removed cited `gs_theorem1` and now reads
    `example : type_of% gs_theorem1_proved`; the `open` line naming lab namespaces was moved below
    the definition `trivSum`, so that the Challenge can restate `trivSum` with the same `open`
    lines; docstrings were reworded; the lemma `trivSum_bounds` became a documented theorem; and six
    theorems were added: `gs_theorem1_full_real`, the identity of `gs_theorem1_full` in real
    numbers, and five derived results of this entry, not statements of the paper,
    `EGS_indep_r`, `EGS_im_eq_zero`, `logDeriv_zeta_neg_one_im`, `Z1_im_eq_zero` and
    `zeroSum_summable`. `zeroSum_summable` has the
    proof of `lz_zeroSum_summable` in the Languasco-Zaccagnini entry.
* Removed declarations, as in the Languasco-Zaccagnini entry, whose copies are used. The lab keeps
  cited, unproved statements of published results next to their definitions. None is used by the
  compared theorems; they were deleted:
  - `GoldbachAverage/ZeroSums.lean`: `lz_theorem1`, `gy_theorem2`, `fujii`, `bsp_upper`.
  - `GoldbachAverage/Unconditional.lean`: `gs_theorem1`, `gs_corollary2`, `lz_cesaro`. The proved
    `gs_theorem1_proved` in `GSTheorem1.lean` replaces the first.
  - `GoldbachAverage/GSTheorem1.lean`: the `example : type_of% gs_theorem1 := gs_theorem1_proved`
    faithfulness check, which referred to the removed `gs_theorem1`.
  - `LZCesaroShort/Statements.lean`: `lz_theorem1`, `lz_theorem2a`, `lz_theorem2b`,
    `lz_lemma7`, `lz_lemma8`, `lz_sec5_rh`.
* No file in the entry other than the Challenge states anything without proof.

## Lab-written mathematics in the closure

`GoldbachAverage/U1440Theorem1Full.lean`, Theorem 1 eq. 11 and the derived results;
`GoldbachAverage/GSTheorem1.lean`, the orthogonality identity for `E(N)` and the form eq. 13;
`PNTPort/ExplicitPsi1/`, the explicit formula for `ψ₁` with nontrivial and trivial zeros;
`PNTPort/ZetaZeros/`, zero counting, Perron's formula and bounds for ζ'/ζ; `LZCesaroShort/`, the
files the explicit formula imports; and `GoldbachAverage/`, `Common/` and `ChenExplicit/`
definitions.
