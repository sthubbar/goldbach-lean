# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Hardy-Littlewood 1923 entry needs: 123
modules, the import closure of the eight modules `LeanLab.HardyLittlewood1923.TheoremBAll`,
`TheoremBUnlike`, `TheoremB34`, `TheoremC`, `TheoremD`, `TheoremE`, `TheoremEAssigned` and
`TheoremF`. AI agents, Claude by Anthropic, wrote them between 2026-10-16 and 2026-10-21, except as
follows. Binary Goldbach is open; nothing here claims it.

73 of the 123 files were already in other entries of this repository. Each was compared with a
fresh conversion of the current lab file, and the only differences are the port fixes, comment
rewording and removals listed in the PORTING.md of the entry it was copied from, which apply here
unchanged: 62 files from `entries/bombierivinogradov1965/LeanLab`, among them all of
`PNTPort/StrongPNT/`, `PNTPort/DirichletZF/`, `PNTPort/LargeSieve/`, `PNTPort/PsiChi/` and the
`PNTPort/BV/` files used here; `ChenExplicit/Statements`, `HeathBrown1985/Lemma2` and
`HeathBrown1985/Statements` from `entries/heathbrown1985`; `PNTPort/BVMax/CoprimeHarm` from
`entries/renyi1948`; `GoldbachAverage/Statements` and `Sums` from `entries/granville2007`;
`ChebyshevExplicit/Psi30` from `entries/schnirelmann1933`; and `PNTSieve/AuxResults`, `Basic`,
`Selberg` and `SelbergBounds` from `entries/brun1919`.

The other 50 files are new in this repository and were converted from the lab with no change
beyond the module header, except the one fix below: 17 files of `HardyLittlewood1923/`, all
but `Section5`, which no compared theorem imports; the 20 files of `PNTPort/Vinogradov/`, the lab's unconditional circle method for three primes;
`VanDerCorput1939/Statements`, `Global`, `KBounds`, `SingLimit`, `Unweight` and
`Vinogradov1Proof`; `Routes/R0001Averaged`, `R0001Markov` and `R0001Parseval`;
`GoldbachAverage/OddSum` and `OddSumPNT`; and `PNTSieve/BrunTitchmarsh` and `BrunTitchmarshAP`.
None of them has an unfinished proof in the lab, so no declaration was removed from them.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ and the
  prime number theorem with error `x exp(-c √log x)`. Same files and same changes as in the
  Bombieri-Vinogradov 1965 and Heath-Brown 1985 entries; see their PORTING.md.
  `StrongPNT/Bridge.lean` is lab-written.
* `LeanLab/PNTSieve/AuxResults.lean`, `Basic.lean`, `Selberg.lean`, `SelbergBounds.lean` and
  `BrunTitchmarsh.lean`, from the same commit, `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/`
  and the Brun-Titchmarsh file, Apache-2.0, written by Arend Mellendijk: the Selberg sieve, its
  bounds and the Brun-Titchmarsh inequality. Each file keeps its copyright line and carries a
  notice of the port. The first four are identical to the copies in the Brun 1919 entry, whose
  PORTING.md lists the lab's changes; `BrunTitchmarsh.lean` is new here and was ported in the lab
  the same way: declarations in `LeanLab.PNTSieve.*` namespaces and import paths renamed.
  `PNTSieve/BrunTitchmarshAP.lean` is lab-written on top of them.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later. The copied files carry the port fixes of the
  entries they come from. One new file needed a fix for rc3: in
  `VanDerCorput1939/Statements.lean`, theorem `euler_factor`, `field_simp; ring` leaves an
  inverse of `p² - 3p + 3` on rc3 and was replaced by
  `rw [one_add_div .., one_sub_div h2, one_sub_div .., div_mul_div_comm, div_eq_div_iff ..]; ring`.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* Four doc comments, in `VanDerCorput1939/Statements`, `ChenExplicit/Statements`,
  `HeathBrown1985/Statements` and `HeathBrown1985/Lemma2`, were reworded so that no file outside
  the Challenge names an unfinished proof; no code changed.
* The Challenge omits the line `open LeanLab.VanDerCorput1939 (I)` of `TheoremB34.lean`,
  `TheoremC.lean` and `TheoremD.lean`, since that namespace does not exist in the Challenge and no
  restated definition uses `I`. Every other `open` line and the local instance
  `Classical.propDecidable` of `TheoremD.lean` and `TheoremEStatements.lean` are kept, so the
  restated definitions elaborate as in the library.

## Lab-written mathematics in the closure

Theorems B to F of Hardy and Littlewood, `HardyLittlewood1923/`, with no hypothesis: the
recursion `ν_{r+1}(n) = Σ_p log p ν_r(n - p)`, the Euler product identities for the singular
series, prime sums in progressions with polynomial weights, and the averaging argument of Theorem
F. Below them: Vinogradov's three primes asymptotic, `VanDerCorput1939/Vinogradov1Proof`, from the
unconditional circle method of `PNTPort/Vinogradov/`, with Vaughan's identity, the minor arc
bound and the major arcs from Siegel-Walfisz; the Siegel-Walfisz theorem itself,
`PNTPort/PsiChi/`, with Siegel's theorem and the zero-free region for Dirichlet L-functions,
`PNTPort/DirichletZF/`; the large sieve; Brun-Titchmarsh in progressions; and an explicit
Chebyshev bound, `ChebyshevExplicit/Psi30`.

No `decide` in the closure is a heavy kernel computation: the six uses check small facts such
as `Finset.Ioc 0 2 = {1, 2}` and that `3` is a unit mod `8`. There is no `native_decide`.
