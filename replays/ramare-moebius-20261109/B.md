# Audit B: escape hatch scan, RSBounds half

Scope: every .lean under RSBounds-project/RSBounds plus RSBounds.lean, 1376 files.
Method: static text scan only. Nothing built, no lake or lean run.

## Import closure of RSBounds.Moebius003.Upstream

Parsed `import` lines recursively, module dots to slashes, resolved against the project root
and vendor/rh100, which the lakefile names as srcDir for Zeta23, ZetaLean, RHHeight100.

- 2427 local files in closure: RSBounds 1289, MoebiusCert 1039, vendor/rh100 99.
- External roots: Mathlib, TernaryGoldbach at 192ca57, Batteries.
- 87 RSBounds files are outside the closure. Examples: RvMData0..5, MertensFinite100000,
  ModeratePsi, Totient, Theta, Moebius003/UpstreamMain, the Zeros*Statement files.
- Note for other auditors: MoebiusCert and vendor/rh100 are in the closure and are not covered here.

## Counts

raw = any line match. code = after stripping line comments, nested block comments,
docstrings and string literals. Word-boundary regexes.

| pattern | raw | code | code in closure |
|---|---|---|---|
| sorry | 6 | 0 | 0 |
| admit | 1 | 0 | 0 |
| axiom | 11 | 0 | 0 |
| native_decide | 0 | 0 | 0 |
| implemented_by | 0 | 0 | 0 |
| extern | 0 | 0 | 0 |
| unsafe | 0 | 0 | 0 |
| partial def | 0 | 0 | 0 |
| opaque | 0 | 0 | 0 |
| debug.skipKernelTC | 0 | 0 | 0 |
| maxRecDepth | 45 | 45 | 35 |
| maxHeartbeats 0 | 19 | 19 | 9 |
| run_cmd / run_elab / run_tac | 0 | 0 | 0 |
| #eval | 0 | 0 | 0 |
| addDecl | 0 | 0 | 0 |
| Environment | 0 | 0 | 0 |
| elab / elab_rules | 0 | 0 | 0 |
| macro / macro_rules | 0 | 0 | 0 |
| syntax | 0 | 0 | 0 |
| initialize | 0 | 0 | 0 |
| notation family | 4 | 3 | 3 |
| #exit, open private, unsafeCast, csimp | 0 | 0 | 0 |
| ofReduceBool / reduceBool | 0 | 0 | 0 |
| decide +kernel | 39215 | 39208 | 39008 |
| set_option | 1032 | 1032 | 1011 |

### set_option by kind, code only: total / in closure

| option | total | closure |
|---|---|---|
| Elab.async false | 955 | 955 |
| maxRecDepth 100000 | 40 | 30 |
| maxHeartbeats 0 | 19 | 9 |
| maxHeartbeats 1000000 | 6 | 5 |
| maxHeartbeats 2000000 | 3 | 3 |
| maxRecDepth 8192 | 2 | 2 |
| maxRecDepth 4096 | 2 | 2 |
| maxHeartbeats 4000000 | 1 | 1 |
| maxHeartbeats 800000 | 1 | 1 |
| maxRecDepth 1000000 | 1 | 1 |
| linter.style.longLine | 1 | 1 |
| linter.unnecessarySeqFocus | 1 | 1 |

No set_option touches debug.*, trace kernel skipping, pp, or autoImplicit.

## Notable hits

All sorry, admit, axiom raw hits are prose inside comments or docstrings. Harmless.
- sorry: RSBounds/Zeros0to1000Statement.lean:12 and Zeros1000to2000 .. Zeros5000to6000Statement.lean:10,
  each saying an upstream `count` stated with sorry was omitted. These files are outside the closure.
- admit: RSBounds/SchoenfeldLaplaceTails.lean:16, English "admit elementary".
- axiom: e.g. RSBounds/MertensPotentialBound.lean:172, MertensDLimit.lean:31, RS62FiniteHandoff.lean:12,
  SchoenfeldQuadraticPsi.lean:394, Targets.lean:29, Totient.lean:9. All prose saying "not an axiom".

Notation, in closure, harmless: `local notation "ε₀" => Goals.Schoenfeld1976.epsilon0` at
- RSBounds/Schoenfeld1976Theorem11Proved.lean:24
- RSBounds/SchoenfeldWalk11.lean:22
- RSBounds/SchoenfeldWalk11Data.lean:13
Local, an abbreviation for an existing constant, cannot leak past the file.

maxHeartbeats 0 in closure, harmless: BacklundLowScalarData, BacklundLowZeros,
QuarticFirst29BudgetNumerics, RS75GoldenNumerics, RS75RealAxisNumerics, RS75ZeroFreeNumerics,
SchoenfeldQuadraticLeft, SchoenfeldRS75BudgetBounds, ZetaZeroTableHead, all under RSBounds/.
Largest recursion bump: RSBounds/Moebius003/Cells.lean:17 `set_option maxRecDepth 1000000 in`.
These only lift elaborator resource limits. They cannot make the kernel accept a false proof.

decide +kernel: 39208 code uses across 1037 files, mostly numeric certificate checks such as
`by decide +kernel : cosDoubleCheck ... = true`. This asks the kernel itself to reduce `Decidable.decide`.
It adds no axiom and no `Lean.ofReduceBool`, unlike native_decide, so it is fully kernel checked.
Cost is replay time, not soundness.

Elab.async false: 955 uses, a parallelism switch for elaboration. Harmless.

attribute [local irreducible] at RSBounds/Moebius003/JSum.lean:59, 79, 135: transparency hint, harmless.

## What Comparator catches anyway

Comparator replays the solution environment in the kernel, allows only propext, Classical.choice,
Quot.sound, and checks the theorem's type against the challenge, which imports only Mathlib.
- Would catch: any `axiom`, any `sorry` via sorryAx, native_decide via Lean.ofReduceBool,
  implemented_by or extern only matter for compiled code and cannot change kernel terms.
- Would not catch by axiom check alone: custom syntax, macros, elaborators or notation that make
  source text read differently from the kernel term. The statement comparison against the
  Mathlib-only challenge closes that gap for the audited theorem, because the challenge's
  PlattGRH and RamareMoebius are elaborated without any RSBounds code. A trick would have to
  change the solution's kernel constants while keeping the same names and types, which the
  comparison rejects. In any case this scan found zero syntax, macro, elab, macro_rules,
  initialize, run_cmd, #eval, addDecl or Environment uses in RSBounds code, so there is nothing
  of that kind to slip through from this half.
- Remaining risk outside this scan: Mathlib, TernaryGoldbach upstream, MoebiusCert and
  vendor/rh100 are in the closure and were not scanned here.

## Not checked

Comparator run: NOT CHECKED. Build: NOT CHECKED. MoebiusCert and vendor/rh100: NOT CHECKED here.

Verdict: PASS
