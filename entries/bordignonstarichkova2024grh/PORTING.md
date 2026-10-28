# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that this entry needs: 55 modules, the import
closure of `LeanLab.BS2022GRH.Cert1575Closed`, taken from the lab's Lean v4.35.0 tree. AI
agents, Claude by Anthropic, wrote all of them between 2026-10-16 and 2026-10-27. No code is
ported from another project.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, as every other entry
  here does, because Palomar's Challenge renderer failed on v4.35.0 and later,
  PalomarRegistry/PalomarSubmission issue 161. No proof needed a change for rc3.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`; the leading comment became a module doc comment; `#print axioms`
  lines were removed.
* Declarations the lab proves with an unproved placeholder were removed from this copy, with
  every declaration that used them:
  - `BS2022GRH/Cert1567.lean`: `eps1500_cert`, the lab's open placeholder for `Eps1500`, which
    `Cert1575.lean` now proves; the headline does not use it.
  - `BS2022GRH/ChenThresholdGRH.lean`: `theorems567_of_inputs`, the open derivation of Theorems
    5, 6, 7 from Lemma 3 and Lemma 7, and `chenThreshold13375_of_basic`, which used it.
  - `AlmostPrimeSums/Statements.lean`: `chen1973` and `togashiUchiyama`, cited statements.
  - `DERZ1997/Statements.lean`: `zinoviev`, `derz_lemma`, `dtr` and `derz_main`, cited inputs
    of an unrelated ternary Goldbach route; the copy is the one in `entries/heathbrown1985`.
  The module comments that named these placeholders were reworded to say they were removed.
* Files identical to an already ported copy in another entry were taken from there:
  `ChebyshevExplicit/Psi30.lean` from `entries/dudek2017`, with an explicit
  `public import Mathlib.Data.Nat.Prime.Factorial`; `ChenExplicit/Statements.lean` from
  `entries/goldstonyang2016` and `ChenExplicit/Bridge.lean` from `entries/renyi1948`, whose
  comments were reworded there.
* A few comments that mentioned the placeholder keyword were reworded, in
  `ChenExplicit/TwinCNumeric.lean`, `AlmostPrimeSums/Statements.lean`, `DERZ1997/Statements.lean`
  and `BS2022GRH/Cert1567.lean`. No statement or proof was changed.

## The kernel certificate

`BS2022GRH/Cert1575W00.lean` to `Cert1575W10.lean` each prove one Boolean identity by
`decide +kernel`, no `native_decide`, over the numbers n = 1 or 5 mod 6 in a window below
9003001, summing floor(10^20/n^2) + 1 whenever gcd(n, m!) = 1. The definitions are in
`Cert1575Defs.lean`, core Lean only; `Cert1575.lean` proves them sound against Mathlib's
`Nat.factorial`, `Nat.Prime` and real sums.
