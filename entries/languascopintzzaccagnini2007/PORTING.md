# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Languasco, Pintz and Zaccagnini
2007 entry needs: 126 modules, the import closure of `LeanLab.LPZ2007.ThreeInputs1123`, which
proves the three compared theorems `cor42_of_three_inputs`, `repaired_mainJ131_of_three_inputs`
and `global_primes_of_three_inputs`. AI agents wrote them between 2026-10-16 and 2026-11-23,
as listed below, except the ported code listed under Ported code. Binary Goldbach is open;
nothing here claims it.

## Where the files come from

* 90 files were already in `entries/linnik1951/LeanLab` of this repository and were copied
  from there: the 16 ported StrongPNT files, the Selberg sieve files, and lab files under
  `PNTPort/`, `PNTSieve/`, `ChenExplicit/`, `HeathBrown1985/`, `SchnirelmannGoldbach/` and
  others. Each was compared with a fresh conversion of the current lab file; the Lean code is
  the same apart from the port fixes of that entry, and only the module header and comment
  wording differ.
* 35 files were converted from the lab at lab commit f063f74496 with no change to the Lean code
  beyond the module header and the removal of `#print axioms` lines, except the changes listed
  below: 32 files of `LanguascoPintzZaccagnini2007/`, `LPZ2007/D4Limits.lean`,
  `LPZ2007/Prep1121J131FourInputs.lean` and `SchnirelmannGoldbach/LoglogUpper.lean`.
* `LPZ2007/ThreeInputs1123.lean` is new, written for this entry. It discharges the real zero
  input of the lab's four input theorem `Prep1121J131FourInputs` by the proved
  `real_zero_bound481`, takes Jutila's and Iwaniec's theorems in their printed form, and adds
  the prime existence corollary on all of `[1, X]`.

## Who wrote the code

* Claude by Anthropic wrote the statement files of `LanguascoPintzZaccagnini2007/`, the
  decomposition of the paper's proof into leaves, the four input assembly
  `LPZ2007/Prep1121J131FourInputs.lean`, the proof of the real zero bound from Siegel's theorem
  in `Decomp481b.lean`, the source reductions `JutilaSrc481.lean`, `Density481.lean` and
  `IwaniecCells1122.lean`, and the new `LPZ2007/ThreeInputs1123.lean`.
* The lab's Open Math OS prover pipeline, with DeepSeek V4.1 Flash, proved some leaves: in
  `Decomp481b.lean` the section `RZB481` that shows the Riemann zeta function has no zero in
  the real interval from 0 to 1, lab commit 9cd9b875f7, and two leaves of `DecompJ218.lean`;
  other of its leaves were proved in the lab's SPLIT files and copied into `Decomp481b.lean` by
  Claude, as the comments there say.
* Google's Jules agent made the first decomposition of `major_asymptotic131` in
  `DecompJ218.lean`, lab tasks 218 and 257.
* Claude did the packaging for this repository.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0, written by the PrimeNumberTheoremAnd
  project contributors: the zero-free region for ζ, Mellin calculus, residue calculus on
  rectangles, bounds for ζ and the strong prime number theorem. Each file carries a notice.
  Same files and same changes as in `entries/linnik1951` and `entries/heathbrown1985`; see their
  PORTING.md.
* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean` and `SelbergBounds.lean`,
  from the same commit, Apache-2.0, written by Arend Mellendijk: the Selberg sieve and its
  bounds. Each file keeps its copyright line and carries a notice of the port.
  `PNTSieve/MertensUpper.lean` and `MertensProduct.lean` are lab-written.
* Lab files under `LeanLab/PNTPort/DirichletZF/`, Siegel's theorem and the zero-free region
  for Dirichlet L-functions, use arguments of the StrongPNT files and say so in their headers.

For the root NOTICE, the ported files of this entry are under
`entries/languascopintzzaccagnini2007/LeanLab/PNTPort/StrongPNT/` and the Selberg sieve files by
Arend Mellendijk under `entries/languascopintzzaccagnini2007/LeanLab/PNTSieve/`, except the
lab-written `MertensUpper.lean` and `MertensProduct.lean`.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  The copied files carry the port fixes of `entries/linnik1951`. Two of the fresh files needed
  a change for rc3:
  1. `LanguascoPintzZaccagnini2007/Fourier131.lean`: `MemLp.indicator` takes the measurable set
     itself on rc3, so `.compl.nullMeasurableSet` became `.compl`, as in
     `BhowmikGrimmelt2026/Minor84.lean`.
  2. `LanguascoPintzZaccagnini2007/Dyadic131.lean`: in `allPrimeExceptions_bound131` the step
     `field_simp` needs the fact that `1 - q` is not zero on rc3, so one line
     `have h1q : (1 : ℝ) - q ≠ 0 := by linarith` was added before it.
* `LanguascoPintzZaccagnini2007/IwaniecCells1122.lean` imports `Decomp481b` in place of the lab
  file `SPLIT_iwaniec_zero_free481`, whose only contents it used come from `Decomp481b`; the
  lab file holds an unproved leaf and is not in the entry. Its code is unchanged.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
  Four copied files, `StrongPNT/ZetaBounds.lean`, `StrongPNT/MediumPNT.lean`,
  `DirichletZF/Growth.lean` and `DirichletZF/Estermann.lean`, need lemmas outside their own
  Mathlib imports and take a private `import Mathlib`, as in `entries/linnik1951`.
* The lab states results of the literature that it has not proved, and some leaves of its own
  decompositions, with placeholder proofs, so that other lab files can cite them. None is used
  by the compared theorems. They were removed from this copy together with every declaration
  that used them, found by the build:
  * `Statements.lean`: `lpz_lemma61_bound`, the bound 1.9378 of Khalfallah and Pintz for the
    series of Lemma 6.1.
  * `Decomp481a.lean`: `pintz_explicit_formula481` and `jutila_density481`, the cited leaves
    whose statements `Lemma41Statement481` and `JutilaStatement481` are now hypotheses, the
    second through Jutila's printed theorem.
  * `Decomp481b.lean`: `iwaniec_zero_free481`, the cited leaf whose statement
    `IwaniecStatement481` now follows from Iwaniec's printed theorem.
  * `DecompJ218.lean`: `cor42_published131` and `cor42_window_extension131`, and
    `major_arcs_j1_131` and `major_asymptotic131_assembly`, which used them.
  * `Assembly481.lean`: `cor42_published131_of_leaves`. `Closure481.lean`:
    `repaired_mainJ131_of_leaves481`. `Decomp131.lean`: `repaired_mainJ131` and
    `major_asymptotic131`. `PrimeRepresentations131.lean`:
    `almost_all_prime_representations131`. `Dyadic131.lean`:
    `almost_all_prime_representations_global131`. All of these call the removed leaves; the
    compared theorems prove the same conclusions from the three hypotheses instead.
* Doc comments of 4 files were reworded so that no file outside the Challenge names an
  unfinished proof by the Lean keyword, and the docstring of `real_zero_bound481` now says that
  it is proved; no code changed. Other lab docstrings keep the lab's paper number, P0045 for
  this paper, and its words CITED and CONDITIONAL ON, which there name the inputs of the lab's
  own leaves; the hypotheses of the compared theorems are the three listed in the Challenge.
* No file in the entry other than the Challenge states anything without proof. There is no
  `native_decide`.

## Route of the proof

`cor42_of_three_inputs` is the lab's `cor42_of_four_inputs1121`, with the real zero bound
supplied by `real_zero_bound481`, Jutila's input by `jutilaStatement481_of_theorem18` and
Iwaniec's by `iwaniecStatement481_of_printed1122`. The four input proof combines the explicit
formula reduction of `Decomp481c` with the exceptional moduli of `Decomp481b`: real characters
through the conductor classification of Davenport Chapter 5 and the real zero bound, nonreal
characters through Iwaniec's region. `repaired_mainJ131_of_three_inputs` passes Corollary 4.2
through `repaired_main_cor42_supply383` of `Closure383`, which uses the major arc evaluation of
`DecompJ218`, the singular series average of `Decomp383a`, Lemma 6.2 and the minor arc bound.
`global_primes_of_three_inputs` is `global_primes_cor42_supply383`, the dyadic covering of
`[1, X]` by the intervals `J(Y)` in `Dyadic131`.
