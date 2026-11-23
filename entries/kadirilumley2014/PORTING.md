# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Kadiri and Lumley 2014 entry needs:
88 modules, the import closure of `LeanLab.KadiriLumley2014.PalomarEntry57`,
`LeanLab.KadiriLumley2014.PalomarKL45` and `LeanLab.KadiriLumley2014.PalomarSummable`, taken from the lab's Lean v4.35.0 tree on 2026-11-22.
They prove three conditional theorems about H. Kadiri and A. Lumley, Short effective intervals
containing primes, Integers 14, 2014, A61, arXiv 1407.7902: one row of Table 2 of Theorem 1.1,
`row_of_inputs`; row 45 of Table 2 in a natural number form, `kl45_of_inputs`; and the ternary
Goldbach range of Corollary 1.2 with row 57 of Table 2 in place of row 60,
`corollary57_of_inputs`. Two more compared theorems, `zeroError_hasSum` and
`row_zeroError_hasSum`, are unconditional and prove that the zero series in display 2.64
converges. Ternary Goldbach is known unconditionally by Helfgott's work, so the
interest of the corollary here is the method. Binary Goldbach remains open; nothing here
claims it. AI agents wrote all the Lean code, as listed below.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: Mellin and residue calculus on rectangles, bounds for ζ, the conjugation
  symmetry of ζ'/ζ, the zero free region and the strong prime number theorem. Each file carries
  a notice of the port. These files are byte for byte the copies in `entries/dudek2014`, which
  are the copies in `entries/goldstonsuriajaya2021` and `entries/goldbachintervalsrh445`; their
  PORTING.md lists the changes: `@[blueprint ...]` attributes and `import Architect` removed,
  import paths renamed, `Tactic/LinearCombinationPrime.lean` re-exporting Mathlib's
  `Mathlib.Tactic.LinearCombinationPrime`, MellinCalculus `Smeas` restored, an explicit
  measurability term in EulerMaclaurin, and the `Set.uIoc_of_le` rewrite in MediumPNT.
* `LeanLab/PNTPort/ZetaZeros/` and `LeanLab/PNTPort/ExplicitPsi1/`, 22 files, are lab-written
  by Claude, as their headers say. They apply the ported results, for example the ported
  Borel Carathéodory bound and the ported residue theorem, to prove the zero counting lemmas and
  the explicit formula for ψ₁ with a sum over the zeros of ζ; they contain no copied code.
* Everything else is lab-written.

For the root NOTICE, the ported files of this entry are under
`entries/kadirilumley2014/LeanLab/PNTPort/StrongPNT/`.

## Who wrote the code

* Codex by OpenAI wrote 29 of the 35 files under `LeanLab/KadiriLumley2014/` in the lab's
  Codex tasks from 2026-10-25, as their headers say: the table of the paper and its
  arithmetic, the weight and its moments, the smoothing transform, the explicit formula with the
  zero sum, and the steps of section 2 in `Decomp92`. Some lemmas of `Decomp92` were added on
  2026-11-12 by a later lab session whose comments say only that AI wrote them.
* Claude by Anthropic wrote `CostaSplit`, which proves the Costa Pereira bound of the paper's
  Lemma 2.1 from Dusart's explicit θ bound, and `Corollary`, the arithmetic of the corollary.
  `BrunTitchmarshMV`, `PalomarEntry`, `PalomarEntry57` and `PalomarKL45` come from the lab's
  Claude sessions of 2026-11-22; their headers say only that AI wrote the Lean code.
* Claude wrote the shared lab files outside `KadiriLumley2014/`, as their headers say, except
  `RamareSaouter2003/Theorem4Parts.lean`, whose header says only that AI wrote it and which
  supplies the named input `MVBrunTitchmarsh`.
* Claude did the packaging for this repository.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0. No lab-written file
  new to this repository needed a change for rc3.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files; the leading comment
  became a module doc comment; `#print axioms` lines were removed.
* 49 files are byte for byte the copies in `entries/dudek2014`, which carry the rc3 port: the 16
  ported files, the 22 files under `PNTPort/ZetaZeros/` and `PNTPort/ExplicitPsi1/`, six files of
  `Dudek2014/`, `ChebyshevExplicit/Psi30`, `ChenExplicit/GammaBounds`, `Helfgott2013/GammaFine`,
  `Common/Goldbach` and `Verifications/PrattCertificates`.
* `KadiriLumley2014/Corollary.lean` keeps from the lab file `goldbach_top`, the partition
  `4 · 10^18 + 2 = 241 + 3999999999999999761`, `exp60_le` and `kl45_of_row`, unchanged. The
  primality proofs `p777448979`, `p13994081623` and `pBig` are the ones of `entries/dudek2014`,
  Lucas certificates through `prattZ` and `zmod_ne_one` with every modular power proved by
  `reduce_mod_char`, so no kernel unfolds a large `decide`. Its import of the lab's
  `Verifications.Pratt` became an import of `Verifications.PrattCertificates`, which drops the
  lab files `Verifications/Pratt`, `Verifications/OeSHPTables`, `Verifications/Statements`,
  `Tao2012/Statements`, `Tao2012/SmallRange`, `SchnirelmannConstant/Defs` and a scaffolding file
  from the closure.
* The lab states results it has not proved with placeholder proofs, so that other lab files can
  cite them. None is used by a compared theorem, and they were removed from this copy with the
  declarations that used them:
  - `KadiriLumley2014/MVInput.lean`, the whole file: the lab's unproved statement of Montgomery
    and Vaughan 1973 Theorem 2. Here that theorem is the hypothesis `hMV`.
  - `KadiriLumley2014/CostaSplit.lean`: `dusart_theta_k2_005`, the lab's unproved statement of
    Dusart 2010 Theorem 5.2 at `η = 0.05`, and `costa_pereira_of_leaf`, which used it. The proved
    `costa_of_dusart` stays; here Dusart's bound is the hypothesis `hDus`.
  - `KadiriLumley2014/Decomp92.lean`: `table_endpoint_budget`, the lab's unproved statement of
    display 2.64 at every row of Table 2, and the declarations that used it or the two leaves
    above, `costa_pereira`, `brun_titchmarsh_pointwise`, `brun_titchmarsh_tail`,
    `table_zero_budget`, `table_psi_margin` and `table_row_from_leaves`. `row_of_inputs` repeats
    the proof of `table_row_from_leaves` with these inputs as hypotheses.
* Removed as not needed by a compared theorem, though proved: from `PalomarEntry.lean`,
  `corollary1_2_of_inputs`, Corollary 1.2 with the printed range, from display 2.64 at rows
  `log 4 · 10^18` and 60; from `Corollary.lean`, `step` and `corollary1_2_of`, the same ladder
  from the rows `log 4 · 10^18` and 60. The lab's uncertified floating point check of display
  2.64, with the computed low zeros of ζ and the paper's zero density bound above height
  3.061 · 10^10, found it negative at row 60 by about 0.02, so the row 60 hypothesis is not known
  to follow from published data by the paper's method, and that version is not offered here.
* Comments only: module and declaration comments of the files of `KadiriLumley2014/`, of
  `Common/PsiTheta/Bound.lean` and of `ChebyshevExplicit/Psi30Upper.lean` were reworded to drop
  lab bookkeeping, run and task labels and mentions of removed declarations. No statement or
  proof was changed by this.

## What is proved and what is assumed

`corollary57_of_inputs` assumes exactly five inputs, each an explicit hypothesis:

1. `hEven`, even Goldbach up to `4 · 10^18`, the verification of Oliveira e Silva, Herzog and
   Pardi 2014;
2. `hMV`, Montgomery and Vaughan 1973 Theorem 2, the Brun Titchmarsh inequality;
3. `hDus`, `|θ(t) - t| < 0.05 t / log² t` for `t ≥ 122568683`, Dusart 2010 Theorem 5.2 at
   `η = 0.05`, from which `costa_of_dusart` proves the Costa Pereira bound that the paper cites as
   Lemma 2.1;
4. `h0`, display 2.64 of the paper at the Table 2 row `log 4 · 10^18`;
5. `h57`, display 2.64 at the Table 2 row 57.

Inputs 4 and 5 are forms of the paper's own numerical display 2.64, with the true absolute
sum over the nontrivial zeros of ζ in place of the paper's bounds for it, at
`X = x0 / e^u / (1 + δ)`, slightly below the paper's `X0 = x0 / e^u / (1 + δ(1 - a))`, and with
the printed `a` raised by one unit of its last digit, since `a` is printed rounded down. These
two changes make each input slightly stronger than the display at the paper's exact `a` and `X0`. The paper checks them by computation; they are not
proved here. The lab's uncertified floating point check found both positive from published zero
data alone, with margins about 0.27 and 0.011. The range `1886389443 · 4 · 10^18` is about 4
percent below the printed range `1966196911 · 4 · 10^18` of Corollary 1.2.

`kl45_of_inputs` assumes inputs 2, 3 and display 2.64 at row 45. `row_of_inputs` assumes the
Costa Pereira bound `CostaEstimate` itself, input 2, membership of the row in Table 2, and
display 2.64 at that row. Everything else is proved: the smoothing argument of section 2, the
explicit formula for ψ with the sum over zeros, the bounds on the trivial zero terms, the
weight integrals of section 3.1, the rounding of the printed table, and the ladder of the proof
of Corollary 1.2 with a Lucas certificate for the top partition.

## Summability of the zero series, in response to review

Palomar's review asked that the weighted zero series be shown summable at the row parameters
and connected to `zeroError`, or that summability be assumed in each numerical input. Each
display 2.64 input uses `zeroError`, a `tsum` over the nontrivial zeros of ζ, and a `tsum` of a
series that is not summable is 0 in Lean, so without summability such an input could omit the
zero contribution. Summability is proved, so no input needs to assume it. The new file
`LeanLab/KadiriLumley2014/PalomarSummable.lean`, written by Claude for this entry, proves
`zeroError_hasSum`: for `m > 0`, `δ > 0`, `u > 0` and `X > 0` the series of `zeroSummand m δ u X`
has sum `zeroError m δ u X`. It rests on `absolute_zero_summable` in `Kernel259`, which comes
from the zero counting bound behind the convergent explicit formula for ψ. It also proves
`row_zeroError_hasSum`, the same at every row of `tableTwo` at `rowEndpointX r`, the very
point and parameters at which each display 2.64 input is stated. Both are compared theorems,
restated in the Challenge. `#print axioms` on each
compared theorem gives exactly `propext`, `Classical.choice` and `Quot.sound`.

## Kernel computations

No `native_decide`. The largest kernel computation is the prime gap scan to 67000 in
`Dudek2014/SmallRange.lean`, about 3 minutes, which enters through the explicit formula files
and is the same file as in `entries/dudek2014`. The table checks in
`KadiriLumley2014/TableArithmetic.lean`, `TableRounding.lean` and `TableCertificates259.lean`
use `decide +kernel` over the twenty rows of Table 2 and the ten rows of the zero density table, Table 1 of the paper,
a few seconds each. No file takes over 5 minutes to build.
