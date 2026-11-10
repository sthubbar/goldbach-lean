# F: upstream main theorems without RamareMoebius, and a PR draft

Auditor F, 2026-11-09. Sources: `RSBounds-project` in `~/ra/x/rsbounds-20261109-full`, upstream clone `~/ra/upstream` at `192ca57`. Nothing was built. No lake or lean was run.

## 1. UpstreamMain against upstream's main theorems

Upstream at 192ca57, `TernaryGoldbach/MainTheorems.lean`:

```lean
theorem ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) (hμ : RamareMoebius) :
    TernaryGoldbachFrom (10 ^ 27)
theorem ternary_goldbach_of_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput)
    (hμ : RamareMoebius) : Statement
```

`RSBounds/Moebius003/UpstreamMain.lean`:

```lean
theorem ternary_goldbach_of_two_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput) :
    Statement :=
  ternary_goldbach_of_hypotheses hGRH hBG (ramareMoebius_of_plattGRH hGRH)
theorem ternary_goldbach_large_of_plattGRH (hGRH : PlattGRH) : TernaryGoldbachFrom (10 ^ 27) :=
  ternary_goldbach_large_of_hypotheses hGRH (ramareMoebius_of_plattGRH hGRH)
```

Verdict by reading: exact. Same conclusions, same remaining hypotheses in the same order, `hμ` removed and supplied by `ramareMoebius_of_plattGRH hGRH`. Argument order matches upstream's. The renames are noted in the file docstring and the README:

| upstream | UpstreamMain |
|---|---|
| `TernaryGoldbach.ternary_goldbach_of_hypotheses` | `TernaryGoldbach.RSBounds.Moebius003.ternary_goldbach_of_two_hypotheses` |
| `TernaryGoldbach.ternary_goldbach_large_of_hypotheses` | `TernaryGoldbach.RSBounds.Moebius003.ternary_goldbach_large_of_plattGRH` |

Name shadowing checked by grep: inside namespace `TernaryGoldbach.RSBounds.Moebius003` there is a second `RamareMoebius`, in `RSBounds/Moebius003Statement.lean` line 29, same body. UpstreamMain never writes bare `RamareMoebius`, and `Upstream.lean` writes `TernaryGoldbach.RamareMoebius` explicitly. The axiom audit log confirms the resolved type: `logs-claude/upstream-axiom-audit.log` prints `Moebius003.ramareMoebius_of_plattGRH : TernaryGoldbach.PlattGRH → TernaryGoldbach.RamareMoebius` and `depends on axioms: [propext, Classical.choice, Quot.sound]`. Comparator would catch any mismatch anyway.

NOT CHECKED: that UpstreamMain compiles. The project README says so itself: "Not built here." `build-upstream-20261109.log` ends `Build completed successfully (11519 jobs).` but covers `Upstream`, not `UpstreamMain`.

## 2. TernaryGoldbachChallenge against upstream Challenge.lean

Upstream's working tree is CRLF, the challenge is LF, so a plain `diff` marks every line. With `diff --strip-trailing-cr upstream/Challenge.lean .../comparator/TernaryGoldbachChallenge.lean`, exit 1, the whole output is:

```
4c4
< # Challenge for leanprover/comparator
---
> # Challenge: upstream's main theorems without `RamareMoebius`, and `RamareMoebius` itself
6,14c6,10
< The statements of the main theorems, with Mathlib-only definitions. ...
  [upstream docstring, 9 lines]
---
> The definitions are copied verbatim from upstream's `Challenge.lean` ...
  [new docstring, 5 lines]
69c65,67
< /-! ## Main theorems -/
---
> end TernaryGoldbach
>
> namespace TernaryGoldbach.RSBounds.Moebius003
71,73c69,71
< /-- Every odd `n ≥ 10²⁷` is a sum of three primes, given two of the hypotheses. -/
< theorem ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) (hμ : RamareMoebius) :
<     TernaryGoldbachFrom (10 ^ 27) := by
---
> open TernaryGoldbach
>
> theorem ramareMoebius_of_plattGRH (h : TernaryGoldbach.PlattGRH) : TernaryGoldbach.RamareMoebius := by
76,78c74,75
< /-- The ternary Goldbach conjecture, given the three hypotheses. -/
< theorem ternary_goldbach_of_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput)
<     (hμ : RamareMoebius) : Statement := by
---
> theorem ternary_goldbach_of_two_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput) :
>     Statement := by
81c78,81
< end TernaryGoldbach
---
> theorem ternary_goldbach_large_of_plattGRH (hGRH : PlattGRH) : TernaryGoldbachFrom (10 ^ 27) := by
>   sorry
>
> end TernaryGoldbach.RSBounds.Moebius003
```

Lines 15 to 68 of upstream, the `import Mathlib`, namespace and all seven definitions, are identical. Only docstring and theorems differ. Upstream's Challenge.lean in turn matches `TernaryGoldbach/Statement.lean` except that Statement.lean also has the lemma `statement_of_upTo_of_from`, which is not a definition the theorems mention.

`comparator-ternary-goldbach.json`: challenge `TernaryGoldbachChallenge`, solution `RSBounds.Moebius003.UpstreamMain`, the three theorem names above, permitted axioms the standard three. Consistent with the files.

## 3. The dependency problem and the options

RSBounds requires `TernaryGoldbach` from git at 192ca57. The proof of `ramareMoebius_of_plattGRH` imports 15 upstream modules, among them `TernaryGoldbach.Explicit.ZetaZeroSums` for `rh_upto_1e8`. So upstream's root package cannot require RSBounds: that is a cycle. Measured by a script that follows `import` lines from `RSBounds.Moebius003.Upstream`: 2,427 local modules, 40,209,640 bytes of source. 1,009 are `RSBounds/PsiFinite`, 954 `MoebiusCert/Large`, 99 `vendor/rh100`. The project README puts the build at about ten hours for PsiCert plus one for MoebiusCert, on 2 cores.

Options:

- **A. Vendor into upstream** and change `ternary_goldbach_of_hypotheses` itself. The only way to change the signature of upstream's own main theorem. Costs Charlie 2,427 files, 40 MB, roughly doubling the build, plus maintaining Helfgott's certificates through every Mathlib bump. License is fine, MIT into Apache 2.0 with notice. Least likely to merge.
- **B. Downstream wrapper only.** This already exists: `UpstreamMain` plus `comparator-ternary-goldbach.json` in RSBounds. Upstream changes nothing, or one README line. Easy to merge, but the result never appears in Charlie's repo.
- **C. Separate package inside upstream's tree.** A subdirectory `TwoHypotheses/` with its own lakefile that requires `TernaryGoldbach` from `..` and RSBounds from git. The root package does not depend on it, so no cycle, the root `lake build` and the existing Comparator run are untouched, and the three-hypothesis theorems stay. Charlie gets the two-hypothesis theorems and a Comparator challenge in his repo for about 200 lines.

Pick: **C**. It is the smallest change that puts the two-hypothesis main theorems in upstream, it costs Charlie nothing in build time or trust surface for his main target, and it fits his existing Challenge plus config.json pattern. A is out on size. B is the fallback if Charlie does not want an external pin in his repo.

What C does not do: it does not change the signature of `TernaryGoldbach.ternary_goldbach_of_hypotheses`. It adds new theorems with two hypotheses. No option short of A can change the original.

## 4. The draft: `~/ra/out/F-upstream.patch`

Made in the copy `~/ra/upstream-F`, new files marked with `git add -N` there, then `git diff`. `~/ra/upstream` is untouched: `git status --short | wc -l` printed `0`. `git -C ~/ra/upstream apply --check ~/ra/out/F-upstream.patch` exited 0. Stat: 8 files changed, 215 insertions.

- `README.md`: a "Two hypotheses" paragraph in Status, one Layout row.
- `TwoHypotheses/lakefile.lean`: `package TwoHypotheses`, `require TernaryGoldbach from ".."`, `require RSBounds from git "RSBOUNDS_URL" @ "RSBOUNDS_REV"`, libs `TwoHypotheses` and `TwoHypothesesChallenge`.
- `TwoHypotheses/TwoHypotheses.lean`: `TernaryGoldbach.ramareMoebius_of_plattGRH`, `ternary_goldbach_large_of_plattGRH`, `ternary_goldbach_of_two_hypotheses`, each a one-line term from upstream's theorem and RSBounds's lemma.
- `TwoHypotheses/TwoHypothesesChallenge.lean`: generated by script from upstream's Challenge.lean, so the definitions are byte-identical. Checked: `diff --strip-trailing-cr` of the definition blocks printed nothing, then `DEFS-IDENTICAL`.
- `TwoHypotheses/comparator.json`, `README.md`, `lean-toolchain` copied from root, `.gitignore`.

No vendoring, so no file list is needed.

Blocker: RSBounds has no public git URL in any file I read. `RSBOUNDS_URL` and `RSBOUNDS_REV` are placeholders until Helfgott publishes it. For a local test, replace that line with `require RSBounds from "/path/to/RSBounds-project"`.

Unverified assumption, NOT CHECKED: that Lake resolves `TernaryGoldbach` to the root's `..` requirement and ignores RSBounds's own git pin of it. If Lake instead errors on the conflicting sources, the fallback is to pin RSBounds's pin and upstream's checkout to the same commit and require upstream by git too.

## 5. What our PC must build to check it

In WSL Linux, because Comparator needs bubblewrap. Apply the patch to a fresh clone of upstream at 192ca57, fill in or localize the RSBounds require, then from `TwoHypotheses/`:

```sh
bwrap --unshare-user --ro-bind / / true && echo bwrap-ok
lake update
lake exe cache get
lake build TwoHypotheses TwoHypothesesChallenge 2>&1 | tee build-two.log
printf 'import TwoHypotheses\n#print axioms TernaryGoldbach.ternary_goldbach_of_two_hypotheses\n#print axioms TernaryGoldbach.ternary_goldbach_large_of_plattGRH\n' > ax.lean
lake env lean ax.lean
( time lake comparator --config comparator.json ) 2>&1 | tee comparator-two.log
```

Expected: each `#print axioms` gives `[propext, Classical.choice, Quot.sound]`; Comparator ends with `Lean default kernel accepts the solution` and `Your solution is okay!`.

Expected Comparator config, as in the patch:

```json
{
  "challenge_module": "TwoHypothesesChallenge",
  "solution_module": "TwoHypotheses",
  "theorem_names": [
    "TernaryGoldbach.ramareMoebius_of_plattGRH",
    "TernaryGoldbach.ternary_goldbach_large_of_plattGRH",
    "TernaryGoldbach.ternary_goldbach_of_two_hypotheses"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```

Size of the job: all of upstream's development, including the 128 ladder files, about 5 core-hours, and data files upstream reports at 7.5 GB resident, plus RSBounds's 2,427 modules. Upstream's own Comparator run took 112 minutes, 90 of them kernel replay at up to about 5 GB; this one replays both. Plan for 16 GB in WSL and an overnight run. The memory note says WSL is capped at 10 jobs; leave that.

The same build also checks Helfgott's own `comparator-ternary-goldbach.json`, from inside `RSBounds-project`: `lake build RSBounds.Moebius003.UpstreamMain TernaryGoldbachChallenge` then `lake comparator --config comparator-ternary-goldbach.json`. Running one of the two is enough to show the result; C's is the one to cite to Charlie.

## 6. Notes for the PR text

- Upstream's `NOTES.md` "Open directions" and `HYPOTHESES.md` "Outlook" say proving `ramare_moebius` is out of reach. The patch leaves them alone; Charlie will want to edit them himself.
- The PR should be opened only after RSBounds is public and the Comparator run above has passed.

Verdict: CONCERN. UpstreamMain and the challenge are exact by reading and diff, but UpstreamMain has never been built and the patch is untested.
