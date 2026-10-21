# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Schnirelmann 1933 entry needs: 32
modules, the import closure of `LeanLab.SchnirelmannExplicit.Sharper6`, 29 modules, together with
`LeanLab.SchnirelmannGoldbach.Discharged`. AI agents, Claude by Anthropic, wrote them between
2026-10-16 and 2026-10-21, except as follows.

## Ported code

* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean` and `SelbergBounds.lean`, from
  PrimeNumberTheoremAnd commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
  `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/`, Apache-2.0, written by Arend Mellendijk:
  the Selberg sieve and its bounds. Each file keeps its copyright line and carries a notice of
  the port. Changes, made in the lab for Mathlib v4.35.0: the declarations moved into the
  namespaces `LeanLab.PNTSieve.Aux`, `LeanLab.PNTSieve.SelbergSieve` and
  `LeanLab.PNTSieve.Sieve`, so that they do not clash with Mathlib's own
  `Mathlib.NumberTheory.SelbergSieve`; import paths renamed to `LeanLab.PNTSieve.*`; and a few
  dot notation calls written as explicit applications. These four files are identical to the
  copies in the Romanov 1934 entry of this repository.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
  Two files needed a change for rc3:
  1. `SchnirelmannGoldbach/S1/MainTerm.lean`, lemma `harmonic_avoid_step`: the last step of a
     `calc`, a `field_simp` that leaves a goal on rc3, became
     `rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul]`, as in the Romanov 1934 entry.
  2. `ChebyshevExplicit/Psi30.lean`: `Nat.Prime.dvd_factorial` is not reached through the file's
     Mathlib imports on rc3, so `public import Mathlib.Data.Nat.Prime.Factorial` was added.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; `#print axioms` lines were removed. Files that are the same module
  as in an earlier entry were checked against a fresh conversion of the lab file and copied:
  from the Romanov 1934 entry, `Common/`, `PNTSieve/`, `Schnirelmann/Inequality.lean`,
  `SchnirelmannExplicit/Constants.lean` and the `SchnirelmannGoldbach/` files it shares; from the
  Mann 1942 entry, `Ramare1995/` and `SchnirelmannConstant/Defs.lean`.
* No file in this closure contains a placeholder proof, so no declaration was removed.
  `SchnirelmannGoldbach/Statements.lean` holds only definitions. Six lab comments, in it, in
  `Ramare1995/Section9.lean`, in `SchnirelmannExplicit/Sharper3.lean`,
  `SchnirelmannGoldbach/FromDensity.lean`, `Unconditional.lean` and `Discharged.lean`, were
  reworded so that they do not mention placeholder proofs by the Lean keyword.

## Lab-written mathematics in the closure

Schnirelmann's theorem, `SchnirelmannGoldbach/`, along Nathanson, GTM 164, Chapter 7: the
Selberg sieve upper bound for the number of ways to write `n` as a sum of two primes, `S1/`,
built on the ported `PNTSieve/` files; the mean square of the singular product, `S2.lean`;
positive lower density of the sums of two primes, `S3.lean`; positive Schnirelmann density and
the bounded number of primes, `FromDensity.lean`, `Main.lean`, `Unconditional.lean`,
`Discharged.lean`. Schnirelmann's inequality and basis theorem, `Schnirelmann/Inequality.lean`.
The explicit bound, `SchnirelmannExplicit/`: explicit sieve and mean square constants,
Chebyshev's bound `π(m) ≥ 0.92 m / log m` from `ChebyshevExplicit/Psi30.lean`, and Dyson's
covering theorem from `Ramare1995/Theorem91.lean`, giving 30772 in `Sharper6.lean`.

The only `decide` in the closure is the check `r 4 = 1` in `SchnirelmannGoldbach/Discharged.lean`,
a small kernel computation. The explicit constants are checked by `norm_num` on rational
numerals, the largest about `2.5 · 10^26` in `SchnirelmannExplicit/Main.lean`; `N₂ = 3^10000` is
an `irreducible_def` and is never evaluated.
