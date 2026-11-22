# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Song 2020 Theorem 1 entry needs: 31
modules, the import closure of `LeanLab.Song2020.Palomar1122Song` after the removals listed
below, taken from the lab tree of 2026-11-22 on Lean and Mathlib v4.35.0. They prove Theorem 1
of Yanbo Song, The ternary Goldbach-Vinogradov theorem with almost equal Piatetski-Shapiro
primes, arXiv 2012.06322 v1, 2020, by the deduction of Section 4 on page 9, from the paper's
Lemma 3, which is Theorem 3 of C. D. Pan and C. B. Pan, Goldbach Conjecture, Science Press,
Beijing, 1988, as the paper cites it. Lemma 3 at the exponent 7/8 is the explicit hypothesis
`Lemma3` at the exponent 7/8. Binary Goldbach remains open; nothing here claims it. Ternary Goldbach is a
theorem of Helfgott 2013.

By folder: 28 files of `Song2020/`, and one each of `Akeno2026/`, `BakerHarmanPintz1997/` and
`Common/`. None of them was in an earlier entry of this repository. No file carries a private
person's name.

## Who wrote the code

* Claude by Anthropic wrote `Song2020/Statements` on 2026-10-17, `Song2020/State1562` apart
  from the two sections named below, `Common/CircleOrth` on 2026-10-20, `Prep1121FourierS2` on
  2026-11-21, and `Audit1122FourierDQ`, `Wire1122Lemma4` and `Palomar1122Song` on 2026-11-22, as
  their headers say.
* Codex by OpenAI wrote `Characteristic139`, `Decomp139`, `Decomp139b`, `Consequences139` and
  the mean square and singular series sections of `State1562` in lab task 139,
  `Repair591Margin` and `Repair591FourierMajorant` in lab task 591, and the port of
  `PortedVanDerCorput` in lab task 219, as the file headers said before the rewording below.
* The `Route` files and `SPLIT_typeII_per_RS` come from the lab's route runs of 2026-11-15, and
  `SPLIT_lambda_sum_per_h` and `SPLIT_vaughan_per_u` from repairs of 2026-11-13 on the Open Math
  OS platform; `Flag1734` comes from a lab review of 2026-11-20, and `Akeno2026/Vaughan86` from
  the lab's work on Akeno 2026. Their headers say only that AI wrote the Lean code and do not
  name the agent. The lab's architect and route sessions run Claude; leaves of the lab are also
  closed by Codex by OpenAI and other lab prover agents, so some of these proofs may be theirs.
* Claude did the packaging for this repository.

## Ported code

* `LeanLab/BakerHarmanPintz1997/PortedVanDerCorput.lean`, the Kusmin-Landau inequality and van
  der Corput's second derivative test, is ported from the Prove2Me submission
  `ExponentialSums.vdC_second_derivative`, Prove2Me id 1038fb61-45dc-46e6-9a1c-862d2aa8430c,
  https://beta.prove2.me, Copyright 2026 Jason Hickey, authors Jason Hickey with Claude,
  Apache-2.0. The port moved its declarations into a separate namespace and fixed it for Lean
  4.35; the file keeps its copyright and license notice. Proposed text for the repository
  NOTICE: The file entries/song2020/LeanLab/BakerHarmanPintz1997/PortedVanDerCorput.lean is
  ported from the Prove2Me submission ExponentialSums.vdC_second_derivative, Copyright 2026 Jason
  Hickey, licensed under the Apache License, Version 2.0; the file carries its copyright and
  license notice.
* No PrimeNumberTheoremAnd code is included.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later. One rc3 fix was needed: in
  `Song2020/Prep1121FourierS2.lean`, three uses of `field_simp` that cancel
  the factor 1 - γ against its reciprocal need the fact `1 - γ ≠ 0`
  stated, which v4.35.0 found by itself; two now use `one_div_mul_cancel` and one states the fact before `field_simp`.
  No statement changed.
* Every file is in the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; `#print axioms` lines were dropped.
* The lab states results it has not proved with placeholder proofs, so that other lab files can
  cite them. Those in this closure, and the declarations that used them, were removed:
  * `Song2020/State1562.lean`: `song_lemma3`, the lab's cited form of Lemma 3. The `Prop`
    `Lemma3` stays and is the hypothesis of every compared theorem.
  * `Song2020/Decomp139.lean`: the unproved step `fourier_approximation`, and with it
    `song_lemma4_decomposed` and `State1562.song_lemma4`, the lab's first assembly of Lemma 4.
    Lemma 4 is proved instead by `Wire1122Lemma4.song_lemma4_of_leaves`, which takes the same
    step from `Prep1121FourierS2`, where it is proved.
  * `Song2020/Decomp139b.lean`: the unproved step `logarithmic_transfer139`, which is the
    transfer at the exact threshold, and with it `song_asymptotic_decomposed` and
    `State1562.song_asymptotic`. The same step is the explicit hypothesis
    `Flag1734.LogTransferDQ` of `songTheorem1_of_lemma3_logTransfer`.
  * `Song2020/DecompJ1132.lean`, the whole file: the unproved step `fourier_error` and the
    assembly `fourier_approximation` that used it. `Flag1734` no longer imports it.
  * `Song2020/Flag1734.lean`: `logTransferMargin`, which used `song_lemma4_decomposed`. The
    proved `logTransferMargin_of`, from Lemmas 4 and 5 as arguments, stays.
  * `Song2020/Audit1122FourierDQ.lean`: `fourier_approximation_type_of_leaves`, which named the
    removed step.
* `Song2020/Statements.lean` no longer imports the lab's `Ternary` files, which carry
  unproved citations of Helfgott and of Matomäki, Maynard and Shao and bring in further lab
  folders, among them one with a private person's name. The proved links to them that nothing
  here uses were removed: `IsAlmostEqualPSTernary.toAlmostEqual`,
  `isAlmostEqualPSTernary_one_iff`, `almostEqualVinogradov_of_songWindow`,
  `songWindow_one_of_almostEqualVinogradov`, `songWindow_one_of_mms` and
  `almostEqualVinogradov_of_songTheorem1`. The definitions of Theorem 1 are unchanged.
* Comments only: lab history marks in module headers and docstrings, such as run and unit
  numbers, task numbers, status labels and agent session names, were reworded as plain
  mathematics, and comments about placeholder proofs were dropped or reworded.

## What is proved and what is assumed

`songWindow_margin_of_lemma3` and `asymptotic_margin_of_lemma3` assume exactly
`Lemma3` at the exponent 7/8, Lemma 3 of the paper. Everything else on their route is proved: Lemma 1, the
Vaaler construction, in `Repair591FourierMajorant`; the Vaughan identity of Lemma 2 in
`Akeno2026/Vaughan86`; Lemma 4 through `Decomp139`, the `Route` and `SPLIT` files,
`Prep1121FourierS2` and `Wire1122Lemma4`; Lemma 5 and the lower bound for the singular series in
`State1562`; the transfer with a positive window margin and the deduction of Theorem 1 in
`Repair591Margin` and `Consequences139`.

`songTheorem1_of_lemma3_logTransfer` gives Theorem 1 at the paper's exact window and assumes
`Lemma3` at the exponent 7/8 and `Flag1734.LogTransferDQ`, the transfer step of page 9 at the exact
threshold. Lemma 4 holds only with a factor n to the epsilon, and at the threshold
y equal to n to the power 52 - 45γ over 8, the product of Lemma 4 and Lemma 5 leaves exactly that factor,
not the saving of log⁴ n the step needs. An independent check of the lab could not prove the
step, so Theorem 1 at the exact window remains open here, and the headline result of the entry
is the margin version. `#print axioms` on each compared theorem gives exactly `propext`,
`Classical.choice` and `Quot.sound`.
