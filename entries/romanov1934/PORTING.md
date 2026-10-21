# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Romanov 1934 entry needs: 33
modules, the import closure of `LeanLab.Romanov.ErdosDensity`. AI agents, Claude by Anthropic,
wrote them between 2026-10-16 and 2026-10-20, except as follows.

## Ported code

* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean` and `SelbergBounds.lean`, from
  PrimeNumberTheoremAnd commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
  `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/`, Apache-2.0, written by Arend Mellendijk:
  the Selberg sieve and its bounds. Each file keeps its copyright line and carries a notice of
  the port. Changes, made in the lab for Mathlib v4.35.0: the declarations moved into the
  namespaces `LeanLab.PNTSieve.Aux`, `LeanLab.PNTSieve.SelbergSieve` and
  `LeanLab.PNTSieve.Sieve`, so that they do not clash with Mathlib's own
  `Mathlib.NumberTheory.SelbergSieve`; import paths renamed to `LeanLab.PNTSieve.*`; and a few
  dot notation calls such as `s.selbergBoundingSum_pos` written as explicit applications.
  `PNTSieve/MertensUpper.lean` is lab-written.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  One proof needed a change for rc3: in `SchnirelmannGoldbach/S1/MainTerm.lean`, lemma
  `harmonic_avoid_step`, the last step of a `calc`, a `field_simp` that leaves a goal on rc3,
  became `rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul]`.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`. `LeanLab/Common/Goldbach.lean` is identical to the copy in the
  Heath-Brown 1985 entry.
* No file in this closure contains a placeholder proof, so no declaration was removed. The
  Statements files in `Brun1919/` and `SchnirelmannGoldbach/` hold only definitions; two of their
  comments were reworded so that they do not mention placeholder proofs by the Lean keyword.

## Lab-written mathematics in the closure

Romanov's theorem, `Romanov/`: the bound `singProd n ≤ e^13 log y` for `n` with at most `y` prime
factors, `SingProd.lean`; Romanov's lemma `Σ_{m ≤ K} singProd(2^m - 1) ≪ K`, `Lemma.lean`; the
Cauchy-Schwarz collision count, `Count.lean`; the assembly, `Theorem.lean` and `Final.lean`; the
form with `k ≥ 1`, `PositiveK.lean`; Erdős' covering congruences, `Erdos.lean`, and their density
form, `ErdosDensity.lean`. The uniform upper bound for prime pairs with a given even gap,
`BrunGap/`, rests on the Selberg sieve upper bound of `SchnirelmannGoldbach/S1/`, built on the
ported `PNTSieve/` files, and on the explicit Mertens-type bound of `AlmostPrimes/RSLogSum.lean`
and `PNTSieve/MertensUpper.lean`.

`Romanov/Erdos.lean` checks its covering congruences with `decide`: 24 residues and 120 pairs of
small numbers, and `2^24 ≡ 1 mod 2^24 - 1`. These are small kernel computations on numerals.
