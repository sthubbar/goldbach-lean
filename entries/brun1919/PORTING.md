# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Brun 1919 entry needs: 22 modules,
the import closure of `LeanLab.Brun1919.LeanEvalBridge` and `LeanLab.BrunGap.Uniform`. AI agents,
Claude by Anthropic, wrote them between 2026-10-16 and 2026-10-20, except as follows.

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
  These four files are identical to the copies in the Romanov 1934 entry.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  One proof needed a change for rc3: in `SchnirelmannGoldbach/S1/MainTerm.lean`, lemma
  `harmonic_avoid_step`, the last step of a `calc`, a `field_simp` that leaves a goal on rc3,
  became `rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul]`.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`. The 21 modules other than `Brun1919/LeanEvalBridge.lean` are
  identical to the copies in the Romanov 1934 entry; each was checked against the lab source.
* No file in this closure contains a placeholder proof, so no declaration was removed. The
  Statements files in `Brun1919/` and `SchnirelmannGoldbach/` hold only definitions; two of their
  comments were reworded so that they do not mention placeholder proofs by the Lean keyword.

## Lab-written mathematics in the closure

`Brun1919/Sieve.lean` applies the Selberg sieve upper bound of `SchnirelmannGoldbach/S1/`, which
rests on the ported `PNTSieve/` files, to the set `{m (m + 2) : m < N}` and gets
`π₂(N) ≤ 48 N / log² z + z (1 + log z)^6 + z + 1`. `Brun1919/Final.lean` takes `z = √N` for
`twinUpper`, `π₂(N) ≤ (192 + 5 · 17^8) N / log² N`, and sums over dyadic blocks for `brun`.
`Brun1919/LeanEvalBridge.lean` restates the lean-eval problem `brun_constant_converges`, its
definitions copied from github.com/leanprover/lean-eval `LeanEval/NumberTheory/BrunConstant.lean`,
and derives it from `brun`. `BrunGap/` repeats the sieve for `{m (m + h) : m < N}` with any even
`h ≠ 0`, giving `brun_gap` and the uniform bound `gapUpper_uniform`, and averages over gaps in
`sum_gapCount_le` with the mean square bound of `SchnirelmannExplicit/Constants.lean`.

No `native_decide` is used, and no proof in the closure runs `decide` on a kernel certificate.
