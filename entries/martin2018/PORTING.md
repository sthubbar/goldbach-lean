# Provenance of the LeanLab files

`LeanLab/` holds the one lab file that the Martin 2018 entry needs. AI agents wrote it in
Steve Hubbard's Lean Lab. No code from outside the lab is included, so the repository NOTICE
does not change for this entry. Binary Goldbach is open; nothing here claims it.

## Authors of the files

* `LeanLab/Martin2018/Statements.lean`: Claude by Anthropic, lab run 20261016T2003Z-5561,
  unit U-0046, 2026-10-16. The definitions `GoldbachAP` and `Conj1_2_iv_printed`, the
  theorems `conj1_2_iv_exceptions`, `eighteen_is_sum` and `conj1_2_iv_printed_false`. The
  proof of `conj1_2_iv_exceptions` was rewritten by the packaging agent, Claude by Anthropic,
  on 2026-11-16, see below.

## Changes made for this repository

* The file was converted to module syntax: the line `module`, then `public import Mathlib`,
  the module doc comment and `@[expose] public section`.
* It is an extract of the lab file `LeanLab/Martin2018/Statements.lean`. It keeps
  `GoldbachAP`, `Conj1_2_iv_printed`, `conj1_2_iv_exceptions`, `eighteen_is_sum` and
  `conj1_2_iv_printed_false` and drops the other declarations, which the compared theorems do
  not use: the statements of Conjectures 1.1, 1.2 i to iii, the corrected 1.2 iv, 1.3 and 1.7,
  the remarks that 1.2 ii and 1.3 i follow from binary Goldbach and that 1.2 ii and iii give
  1.2 i, the exceptions of Conjecture 1.3 ii, the lemma `goldbachAP_bounded` and the kernel
  search `apFrom`, `allIv` with the check `conj1_2_iv_upTo` of the corrected 1.2 iv for every
  n at most 3000. With them went the lab import `LeanLab.Common.Goldbach`.
* The lab proofs used `decide` on bounded searches. Palomar runs the con-ron kernel, which runs
  out of fuel on `decide` style proofs, so no `decide` is kept. `conj1_2_iv_exceptions` now
  splits on the five numbers and on every p up to n with `interval_cases` and closes each case
  with `norm_num`, which proves the needed primality and compositeness facts and residues.
  `eighteen_is_sum` and `conj1_2_iv_printed_false` use `norm_num` and `simp` in place of `rfl`
  and `decide`. The statements are unchanged; two docstrings were put in lower case.
* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later, PalomarRegistry/PalomarSubmission issue 161.
