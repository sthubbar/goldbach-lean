# Provenance of the LeanLab files

`LeanLab/` is the part of Steve Hubbard's Lean Lab that the Rényi 1948 entry needs: 151 modules,
the import closure of `LeanLab.PNTPort.BVMax.Renyi8Main` and `LeanLab.PNTPort.BVMax.TwinRenyi`.
AI agents, Claude by Anthropic, wrote them between 2026-10-16 and 2026-10-21, except as follows.
Binary Goldbach is open; nothing here claims it.

116 of the 151 files are the files of the Bombieri-Vinogradov 1965 entry of this repository,
`entries/bombierivinogradov1965/LeanLab`, all of its files except `PNTPort/BVMax/PiPi.lean`,
which this entry does not need. Each was compared with a fresh conversion of the current lab
file, and the only differences are the port fixes, comment rewording and removals listed in that
entry's PORTING.md, which apply here unchanged. Four further files, `AlmostPrimes/DDLemma23`,
`DDLemma23Full`, `RSLogSum` and `PNTSieve/MertensUpper`, are identical to the files of the same
name in the Romanov 1934 entry. The other 31 files are new in this entry and were converted from
the lab with no change beyond the module header: `PNTSieve/Bonferroni`, `BonferroniWeighted`,
`BrunBlocks`, `BrunBlocksRel`, `BrunBlocksSupport`, `BrunPure`, `BrunTwoBlock`, `Esymm`,
`MertensLower`, `MertensProduct`, and in `PNTPort/BVMax/` the files `CoprimeHarm`, `TauGoldbach`,
`TauGoldbachMain`, `RenyiPrep`, `RenyiCount`, `RenyiRem`, `RenyiMain`, `RenyiAssembly`,
`RenyiBlocks`, `RenyiFixedK`, `TwinRenyi`, `RenyiPaired`, `RenyiWeighted`, `RenyiRealBase`,
`RenyiSmallK`, `Renyi20`, `Renyi14`, `Renyi10`, `Renyi9`, `Renyi8` and `Renyi8Main`. None of
them has an unfinished proof in the lab, so nothing was removed from them.

The lab also has files for `K = 6` and `K = 7`, `Renyi6*`, `Renyi7*` and `Twin6`, `Twin7`, edited
on 2026-10-21 and not yet verified; none of them is in this entry or in the import closure of the
compared theorems.

## Ported code

* `LeanLab/PNTPort/StrongPNT/`, 16 files, from PrimeNumberTheoremAnd commit
  c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache-2.0: the zero-free region for ζ and the
  prime number theorem with error `x exp(-c √log x)`. Same files and same changes as in the
  Bombieri-Vinogradov 1965 and Heath-Brown 1985 entries; see their PORTING.md.

## Changes made for this repository

* The repository pins Lean and Mathlib v4.35.0-rc3, not the lab's v4.35.0, because Palomar's
  Challenge renderer fails on v4.35.0 and later. The port fixes are those of the
  Bombieri-Vinogradov 1965 entry; the 31 new files needed no fix.
* Every file was converted to the Lean module system: a `module` header, `public import`, and
  `@[expose] public section`, or `public meta section` for tactic files.
* The Solution file adds one short corollary, `renyi8_isAtMostAlmostPrime`, which restates
  `renyi8_fixedK` with Mathlib's `Nat.IsAtMostAlmostPrime 8 m`, that is `m ≠ 0 ∧ Ω(m) ≤ 8`.

## Lab-written mathematics in the closure

The Bonferroni inequalities and Brun's pure and block sieve, `PNTSieve/`; Mertens' estimates;
Rényi's block sieve with Bonferroni levels and its sharpening to `K = 8`, `PNTPort/BVMax/Renyi*`;
`TwinRenyi`, which proves `twin_renyi_count`, a derived analogue proved in this entry by the same
sieve method, a twin-prime analogue of Rényi's theorem and not a result of Rényi 1948; and below them the Bombieri-Vinogradov theorem for `π(y; q, a)` and
everything it rests on, as listed in the Bombieri-Vinogradov 1965 entry's PORTING.md.
