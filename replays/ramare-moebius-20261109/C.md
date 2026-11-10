# Auditor C: escape hatch scan outside P/RSBounds

P = ~/ra/x/rsbounds-20261109-full/RSBounds-project. Static reading only. Nothing built, no lake or lean run.

## Scope scanned
P/MoebiusCert 1042 files, P/vendor/rh100 100 .lean files, P/comparator 24 files, P/verification, P/*.lean, P/lakefile.lean, P/lake-manifest.json. Also the 41 upstream TernaryGoldbach files in the closure.

## Pattern counts over .lean files in scope
| Pattern | Hits | Class |
|---|---|---|
| sorry | 39 | 3 in doc comments in vendor; 36 are the challenge holes in P/comparator. Challenge files are outside the proof closure; Comparator requires sorry there. Harmless. |
| admit | 0 | |
| axiom declaration | 0 | 8 text hits, all in comments, e.g. vendor/rh100/Zeta23/Hypotheses.lean:9,17 |
| native_decide, implemented_by, extern, unsafe, partial def, opaque | 0 | |
| debug.skipKernelTC, maxHeartbeats 0, run_cmd, run_elab, #eval, addDecl, Environment, elab, macro_rules, initialize, ofReduceBool | 0 | |
| macro / syntax | 2 | MoebiusCert/Raw.lean:42 raw_norm is a simp only wrapper; vendor/rh100/Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean:32 wraps linear_combination. Both proof-producing tactic sugar. Harmless. |
| import Lean | 0 | |

## set_option by kind
- maxRecDepth 100000: 1038 lines, 986 MoebiusCert files and 37 vendor files. Elaborator only. Harmless.
- Elab.async false: 984. Harmless.
- backward.isDefEq.respectTransparency false: 7, all vendor, e.g. Zeta23/FromPNTPlus/ZetaBounds.lean:618, Zeta23/GammaFacts.lean:98. Elaborator unification only; the kernel still checks. Harmless.
- maxHeartbeats 1000000 or 1600000: 3 in vendor, Zeta23/RvM/MainTerm.lean:215,483 and Zeta23/RvM/ReZeroCount.lean:102. Finite. Harmless. Upstream closure has 5 more at 1000000.
- lang.lemmaCmd true: vendor/rh100/Zeta23/FromPNTPlus/ZetaBounds.lean:31. Harmless.
- linter.style.multiGoal false: 2. Harmless.

None of the above can make the kernel accept a false proof. Every hit that could, sorry, axiom, native_decide via Lean.ofReduceBool, extern or implemented_by in a proof, would show up as an extra axiom or a kernel rejection, which Comparator catches with the propext, Classical.choice, Quot.sound whitelist. Things Comparator would not catch are statement-level tricks, a tampered build or tool, or a shadowed definition; none were found. Challenge statement fidelity is out of my scope.

## lakefile.lean
- One dependency: TernaryGoldbach from https://github.com/calr3/ternary-goldbach.git at 192ca57362fa3ee737cd83205cb9ea99526c4553.
- No precompileModules, no moreLeanArgs, no plugins, no extern_lib, no script or target definitions. leanOptions only on vendor libs: relaxedAutoImplicit false, autoImplicit false, pp.unicode.fun true. Harmless.
- No comparator dependency in the lakefile or manifest. LAPTOP-COMPARATOR.md runs `lake comparator --config ...`, so the Comparator used is the one shipped with the toolchain, pinned by lean-toolchain = leanprover/lean4:v4.35.0. Nothing in the project defines or overrides a comparator script.

## lake-manifest.json pins
```
"rev": "192ca57362fa3ee737cd83205cb9ea99526c4553",
"name": "TernaryGoldbach",
"rev": "56a005855ea17e0b0958f73ec801ae140b0a1679",
"name": "mathlib",
```
Both match. Mathlib is inherited with inputRev v4.35.0.

## Import closure of RSBounds.Moebius003.Upstream
Header-only recursive trace: 2468 local modules plus Mathlib and Batteries.
- RSBounds: 1289. MoebiusCert: 1039 of 1042; LargeAll, MsAll, SmallAll are outside.
- vendor/rh100: all 99 library modules are inside; CheckMain100.lean is outside.
- Upstream TernaryGoldbach, 41 modules: CircleMethod, Statement; Explicit/ Datum, Digamma, ExplicitFormula, GMellin, GammaBounds, GaussSmooth, LGrowth, LGrowthLeft, LGrowthPoly, Landau, LineZeros, LogDerivL, LogNumerics, MellinPlancherel, MellinRotate, RectResidue, RectResidue2, Xi, XiPartial, ZeroCount, ZeroFree, ZeroFreeRegion, ZeroSumBound, ZeroSumGen, ZeroSums, ZetaDatum, ZetaExplicit, ZetaGrowth, ZetaPoly, ZetaZeroSums; MinorArcs/Montgomery; Prelim/ GaussInduced, LogWalk, PNTMertens, PlancherelReal, RamareHarm, RamareWalk, SmallMertensLower, SmallMertensProd. No escape hatch hits in them.

Vendor entry points, via Upstream <- Moebius003.Complete <- Moebius003.Final <- Schoenfeld1976Final <- ... <- RosserSchoenfeld1975:
- RSBounds/BacklundRH100Bridge.lean:2 imports RHHeight100.Main100
- RSBounds/BacklundLowZeros.lean:2 imports RHHeight100.TwentyNineZeros
- RSBounds/PolynomialZeroCountBridge.lean:3 imports Zeta23.ZetaReflect
- RSBounds/QuarticBudgetNumericsBase.lean:2 imports ZetaLean.Rigor

## Vendor soundness
- No axiom declarations in vendor. The hypothesis structure Zeta23.PaperInputs appears only in Zeta23/Defs.lean and Zeta23/Hypotheses.lean, and nowhere in RSBounds, so no used theorem takes it.
- RHHeight100.rh_height_hundred : RHHeight100 and zero_count_hundred : ZeroCountUpTo 100 29 at RHHeight100/Main100.lean:52,58 take no arguments. RHUpToHeight is a definition, RHHeight/Statement.lean:41, over Mathlib's riemannZeta, so it is proved, not assumed.
- The bridge uses these as proved facts, BacklundRH100Bridge.lean zero_simple_below_hundred and closed_count_hundred.
- No redefinition of riemannZeta in vendor; riemannZeta0 at ZetaBounds.lean:525 is a separate name.

## Verdict
PASS on escape hatches outside P/RSBounds. Comparator run itself NOT CHECKED.
