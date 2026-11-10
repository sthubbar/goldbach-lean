# RamareMoebius audit, 2026-11-09

Independent static audit by the Lean Lab, sthubbar/goldbach-lean. Comparator Run A has not run yet; its result will be added here.

Audit of `TernaryGoldbach.RSBounds.Moebius003.ramareMoebius_of_plattGRH : PlattGRH → RamareMoebius`
in rsbounds-20261109-full, against calr3/ternary-goldbach at 192ca57. Static, read-only audit by 7 parallel
reviewers plus 1 falsifier, with file and line references in A.md to G.md. Nothing was built and Comparator was not run: that is Run A.

Tarball sha256 checked: `b7d5c861...e8ed`, matches. Challenge sha256 checked: `31cd8d5b...a361d`, matches.

## Verdicts

| | Area | Verdict | Where | Note |
|---|---|---|---|---|
| A | Trusted statement | PASS | `comparator/UpstreamRamareChallenge.lean` | Only docstring and theorem differ from upstream `Challenge.lean`, after stripping CRLF. Statement is the real-x form of [H] (2.21), sum over 1 ≤ n ≤ ⌊x⌋. PlattGRH is not vacuous. |
| B | Escape hatches, RSBounds | PASS | `B.md` | Zero native_decide, extern, unsafe, opaque, elab, axiom in code. 39,208 `decide +kernel`, all kernel-checked. Only elaborator set_options. |
| C | Escape hatches, rest | PASS | `C.md` | MoebiusCert, vendor/rh100, comparator, lakefile clean. Manifest pins Mathlib 56a0058 and upstream 192ca57. vendor/rh100 is in the closure, with no axioms and no hypotheses assumed. |
| D | Tex vs Lean, Möbius | PASS | `D.md` | Every input of `Moebius003.target` is proved. All 24 departures are benign. Lemma 7(c) has a thin margin: 0.0299980 vs 0.03, exact rational check. |
| E | Schoenfeld, FiniteRH | PASS | `E.md`, `E2.md` | All 8 Schoenfeld targets are proved from FiniteRH 1894438.5122. PlattGRH to FiniteRH via `rh_upto_1e8` is correct. PsiCert matches. Every target and ε0 checked against the page images of Schoenfeld 1976 and its corrigendum, p. 900: same constants, relations and ranges; the Lean (7.4) is the corrected (7.4). No Lean statement is stronger than the paper. |
| F | UpstreamMain, PR draft | CONCERN, untested | `F.md`, `F-upstream.patch:260` | UpstreamMain matches upstream's main theorems minus `hμ`. Nothing is built. The patch has a placeholder RSBounds git URL and rev. |
| G | Run script, addon | CONCERN, minor | `HelfgottPsiBoundsFinal.lean:25,30`, `README.md:19` | Addon (2.14) and (2.17) hold for y ≥ 2.5·10⁷, while the book has 2·10⁶ and 1.6·10⁶. Falsifier confirmed. Outside the RamareMoebius closure; upstream needs only ≥ 2.7·10⁷. A labeling issue. |

No FAIL. No concern touches the soundness of `ramareMoebius_of_plattGRH`.

## Open questions for Harald

- Is there a public git URL and rev for RSBounds, so that upstream can `require` it in a `TwoHypotheses/` package?
- Would he relabel the addon as "(2.14), (2.17) with Helfgott's constants, for y ≥ 2.5·10⁷"?

## Run A

`run-A.sh` is ready. `bash -n` passes, there is no `rm`, and the axiom patterns were matched against the real audit-log format. It has not run on WSL yet. Estimate: 18 to 40 h wall time, so plan for two nights. The build can peak at 20 to 26 GB against the 31 GB cap; if it OOMs twice, rerun with `JOBS=6`. It needs `sudo apt install bubblewrap time` first.
