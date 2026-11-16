# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that this entry needs: 78 modules, the import
closure of `LeanLab.Dudek2014.SigmaHSWDownstream`, `LeanLab.Dudek2014.Theorem1HSW`,
`LeanLab.Dudek2014.AbstractC3HSW` and, since version 2, `LeanLab.Dudek2014.IntervalOne`, taken
from the lab's Lean v4.35.0 tree. AI agents, Claude by
Anthropic, wrote them between 2026-10-16 and 2026-10-21, except as follows.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice. These
  files are byte for byte the copies in `entries/goldstonsuriajaya2021` and
  `entries/goldbachintervalsrh445`, whose PORTING.md lists their changes: `@[blueprint ...]`
  attributes and `import Architect` removed, import paths renamed,
  `Tactic/LinearCombinationPrime.lean` re-exporting Mathlib's
  `Mathlib.Tactic.LinearCombinationPrime`, MellinCalculus `Smeas` restored, an explicit
  measurability term in EulerMaclaurin, and the `Set.uIoc_of_le` rewrite in MediumPNT.
* Everything else is lab-written.

For the root NOTICE, the ported files of this entry are under
`entries/dudek2014/LeanLab/PNTPort/StrongPNT/`.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, as every other entry
  here does. No lab-written proof needed a change for rc3.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files; the leading comment
  became a module doc comment; `#print axioms` lines were removed.
* 65 files are byte for byte the copies in `entries/goldbachintervalsrh445`, which already
  carry the rc3 port and the removals listed in its PORTING.md, among them the cited statements
  of Chirre and Hagen in `ChirreHagen2025/Statements.lean`.
* `PNTPort/ExplicitPsi1/DudekTrudgian.lean` is the copy there, trimmed as below.
* Eight files are newly ported from the lab with the same conversion and are otherwise
  unchanged: `Dudek2014/Theorem1Small.lean`, `Dudek2014/Theorem1HSW.lean`,
  `Dudek2014/AbstractC3HSW.lean` and the four files of `PrimePowerWindow/`, Count, Window,
  Holds and Display, which prove the prime power window `window_holds` that replaces
  Schoenfeld's ψ - θ bounds; and `Dudek2014/SigmaHSWDownstream.lean`, trimmed as below.
* Declarations removed from this copy, none used by a compared theorem:
  - `Dudek2014/SigmaHSWDownstream.lean`: `goldbach_gap_1478_RH_hsw`, `kaniecki_lemma6_RH_hsw`
    and `RamareSaouter2003.theorem1_of_RH_hsw`, lab corollaries of Theorem 2; its import of
    `PrimePowerWindow.Downstream` became imports of `PrimePowerWindow.Display`,
    `PNTPort.ExplicitPsi1.DudekTrudgian` and `Dudek2014.SigmaHSW`.
  - `PNTPort/ExplicitPsi1/DudekTrudgian.lean`: `theorem2_of_RH_trudgian`, Theorem 2 from the
    zero count of Trudgian 2014, whose constant is reported to be in error, and from
    Schoenfeld's bounds as hypotheses. Its imports of `Dudek2014.SigmaTrudgianDownstream` and
    `RamareSaouter2003.Theorem1Lemma4` became one import of `Dudek2014.SigmaTrudgian`. The file
    keeps `ZIdx`, `gZ`, `Zr_eq_Zreal` and its helper lemmas.
  These two edits drop 20 modules of the shared library from the closure: the Kaniecki,
  Goldbach gap, Ramaré-Saouter, DERZ, Tao and Kadiri-Lumley files.
* Comments that mentioned the placeholder keyword were reworded in
  `Dudek2014/AbstractC3HSW.lean`. No statement or proof was changed.

## Version 2

Version 2 adds one compared theorem, `LeanLab.Dudek2014.IntervalOne.dudek_interval_one`, a
derived result that is not a statement of the paper, and four lab-written modules, ported with
the same conversion. No earlier file, statement or proof changed, apart from the new import in
`SolutionDudek2014.lean`, the new section at the end of `ChallengeDudek2014.lean` and its
mention in the module doc comment.

* `Dudek2014/MaxGap.lean`: the cited hypothesis `MaxGap1476` and the lemmas `gaps_huge`,
  `upTo_of_maxGap` and `theorem2_of_maxGap`, unchanged; its import of
  `KadiriLumley2014.Corollary` now names the trimmed copy below, and its doc comment was
  rewritten.
* `Dudek2014/IntervalOne.lean`: the lab file `Dudek2014/Novelty1612.lean`, renamed with its
  namespace, from `LeanLab.Dudek2014.Novelty1612` to `LeanLab.Dudek2014.IntervalOne`. Removed:
  `dudek_interval_0556`, an open target for the constant 0.556 that has no proof, so no
  placeholder proof enters the repository. Kept: `PrimeInC`, `dudek_interval_one`,
  `dudek_interval_eps`, `not_primeInC_055`, `primeInC_two` and their helper lemmas, with
  docstrings reworded and no proof changed.
* `KadiriLumley2014/Corollary.lean`: only the Lucas certificates of 777448979, 13994081623
  and 3999999999999999761, `p777448979`, `p13994081623` and `pBig`, unchanged. The rest of
  the lab file, Kadiri and Lumley's Corollary 1.2 and its ladder, is removed: it is not used
  by a compared theorem and imports their table rows.
* `Verifications/PrattCertificates.lean`: the binary modular power `pm`, `pm_cast`, Lucas'
  test `pratt` and `pB`, unchanged. The certificates of other record primes in the lab file
  are removed as unused.

## Kernel computations

The closure has only small `decide +kernel` checks, no `native_decide`: a prime gap scan to
67000 in `Dudek2014/SmallRange.lean`, about 3.5 minutes, the largest; three Lucas certificates
in `KadiriLumley2014/Corollary.lean`, a few seconds; two harmonic number bounds in
`Helfgott2013/GammaFine.lean`; and small checks in `ChenExplicit/GammaBounds.lean` and
`Common/Goldbach.lean`. The `ChirreHagen2025/` files are short lemmas closed by
`norm_num` and `linarith`.
