# Independent replay of calr3/ternary-goldbach at 192ca57

**Summary**
- Commit: calr3/ternary-goldbach `192ca57362fa3ee737cd83205cb9ea99526c4553`, Lean and Mathlib v4.35.0.
- Build: `lake build` of all four libraries, including the 128 ladder files, succeeded with 0 errors in about 6 h 32 min of wall time, peaking at 21.1 GB.
- Axioms: both main theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. `PlattGRH`, `BinaryGoldbachInput` and `RamareMoebius` are explicit arguments.
- Hypotheses: each is stated no stronger than its source (Platt Thm 7.1, OeSHP 2014, Ramaré 2013 Cor. 1.4).
- Comparator: `lake comparator` accepted both theorems, exit 0, "Your solution is okay!", after a 36 h kernel replay.
- Problems found: none.

Run 2026-11-07 to 11-09, Steve's PC, by Claude Code with Steve's approval. All times are Pacific (PST).
Read-only toward Reams's repo: nothing pushed, no issues, no pull requests, nothing posted or emailed.
Logs: `C:\Users\sthub\git-repos\reams-replay-logs\` (Windows) and `~/replay-logs/` in the LeanAgents WSL distro.

## 1. Commit and toolchain

- Repo: https://github.com/calr3/ternary-goldbach, cloned fresh twice:
  - `C:\Users\sthub\git-repos\reams-replay` (Windows);
  - `~/reams-replay` (WSL Ubuntu 24.04, kernel 6.18 WSL2).
- Checked out detached at **`192ca57362fa3ee737cd83205cb9ea99526c4553`**, committed 2026-11-07 22:31:18 UTC (2:31 PM PT), "NOTES: what removing RamareMoebius would need; models for its two uses". `git rev-parse HEAD` gives this hash in both clones.
- `lean-toolchain`: `leanprover/lean4:v4.35.0`.
- Mathlib: `v4.35.0`, manifest rev `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Files: 429 `.lean` files outside `.lake`, including 128 ladder data files `TernaryGoldbach/Ladder/Data/L000-L127.lean`.

## 2. Build

**Result: `Build completed successfully (9472 jobs)`, exit 0, 0 errors.** The build of record ran in WSL.

Target: `lake build TernaryGoldbach LadderHints Challenge Solution`. This is every library in the lakefile, so it includes all 128 ladder data files.

Settings:
- WSL2 distro LeanAgents: 12 logical CPUs, 31 GB memory limit.
- `LEAN_NUM_THREADS=8`, `nice -n 19`, timed with `/usr/bin/time -v`.
- Mathlib cache: `lake exe cache get` downloaded 9031 files in 5 minutes (6:56 to 7:01 PM PT).

| Item | Value |
|---|---|
| Wall time | about **6 h 32 min** in two parts. Part 1: 7:01 to 7:49 PM PT (48 min), cut off by Steve's reboot. Part 2: 8:11 PM to 1:55 AM PT, `5:44:22` by `time`. Lake kept the modules finished in part 1. |
| CPU | 644 % average in part 2, about 6.4 of the 8 threads busy. |
| Peak memory | **21.1 GB** of WSL memory in use (sampled every 30 s), at 12:03 AM PT while ladder and table files compiled together. |
| Largest single process | 17.6 GB RSS for one `lean`, at 1:00 AM PT, during the SmallLiouville / LSQuot8g / SmallMuPhi stretch. `time -v` gives max RSS 18.0 GB. RSS includes about 7 GB of memory-mapped Mathlib `.olean`s. |
| Ladder files | 128 of 128 built, plus `Ladder.Data`. Median 789 s per file and maximum 1179 s, 8 running at once. 100,361 s of compile time in part 2 alone, about 28 core-hours. Reams's "about 5 h of one core" is the kernel check alone; elaboration includes the native hint search and re-checks. |
| Slowest other modules | SmallMertensProd 1780 s, SmallMuPhi 1680 s, SmallLiouville 1363 s, SmallPsiData5 1228 s, SmallPsiData4 1177 s, SmallFsq 1133 s. |

Contention to note:
- Steve's machine was in normal use.
- A separate Lean Lab job (BhowmikGrimmelt2026) built on Windows from 8:07 PM to about 9 PM PT.
- Times are therefore upper bounds.

**Warnings: 1908 in total (287 in part 1, 1621 in part 2), across 161 files, none of them errors.**
- 1277 are deprecations, mostly `if_pos`/`if_neg`/`if_true`/`if_false` → `ite_*`, and `integral_finset_sum`.
- 128 are "unused tactic" and 48 "`<;>` should be `;`".
- 94 are unused variables, 78 "this tactic is never executed", 59 unused simp arguments, 40 "used X where Y would suffice", 10 "Try this".
- 160 are "imports X from package `mathlib`, which is designed for use with the module system".

None bears on soundness. The full logs are in WSL at `~/replay-logs/build.log` and `~/replay-logs/old/build-part1.log`.

Windows attempt (not the build of record):
- The same commit built natively on Windows 10 with `LEAN_NUM_THREADS=10` at BelowNormal priority, from 4:45 to 7:49 PM PT.
- It reached 9110 of 9480 jobs with no errors, and 18 of 128 ladder files at about 4,300 s each (15 at once).
- The reboot stopped it, and it was not resumed, because WSL compiles the ladder about 4 times faster.
- Mathlib cache on Windows: 11.5 min. Log: `C:\Users\sthub\git-repos\reams-replay-logs\old\win-build-part1.log`.

## 3. Axioms

The check file is `~/replay-logs/Axioms.lean` in WSL, outside the repo, so the clone stays clean (`git status` is empty). It was run with `lake env lean` after the build. Output in full:

```
ternary_goldbach_of_hypotheses : PlattGRH → BinaryGoldbachInput → RamareMoebius → Statement
ternary_goldbach_large_of_hypotheses : PlattGRH → RamareMoebius → TernaryGoldbachFrom (10 ^ 27)
'TernaryGoldbach.ternary_goldbach_of_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryGoldbach.ternary_goldbach_large_of_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
@Helfgott.ternaryGoldbachUpTo_1e27 : ∀ [Fact BinaryGoldbachInput], TernaryGoldbachUpTo (10 ^ 27)
@Helfgott.ternaryGoldbachFrom : ∀ [Fact PlattGRH] [Fact RamareMoebius], TernaryGoldbachFrom (10 ^ 27)
@Helfgott.major_arcs_input : ∀ [Fact PlattGRH] (N : ℕ),
  Odd N →
    10 ^ 27 ≤ N →
      1.049 * Helfgott.xOf N ^ 2 / Helfgott.κ ≤
        (∫ (α : ℝ) in Set.Ioc 0 1 ∩ Helfgott.majorArcs 8 Helfgott.r₀ (Helfgott.xOf N), Helfgott.integrand N α).re
'TernaryGoldbach.Helfgott.ternaryGoldbachUpTo_1e27' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryGoldbach.Helfgott.ternaryGoldbachFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **As expected.** Only `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`, no `Lean.ofReduceBool`, no other axiom.
- The three hypotheses are explicit arguments of the main theorem: `PlattGRH`, `BinaryGoldbachInput` (to 4·10^18) and `RamareMoebius`.
- The brief named `TernaryGoldbach/Statement.lean` as the home of the main theorem. In fact `Statement.lean` defines `Statement` and the three hypotheses, and the theorems are at `TernaryGoldbach/MainTheorems.lean:16` (`_large_`) and `:23`.
- Proof-term trace (Deicyde's calr3/ternary-goldbach issue #1), from the signatures:
  - the small cases `ternaryGoldbachUpTo_1e27` take only `BinaryGoldbachInput`;
  - the large case `ternaryGoldbachFrom` takes `PlattGRH` and `RamareMoebius`;
  - `major_arcs_input` takes only `PlattGRH`.
- Caveat on the trace: these are `Fact` section variables. The `unusedSectionVars` linter drops unused ones, so the signature shows what each proof uses.

## 4. Grep of the whole tree

Searched all `.lean` files outside `.lake/` with whole-word matching.

| Keyword | Hits | Where |
|---|---|---|
| `sorry` | 2 in code | `Challenge.lean:74` and `Challenge.lean:79`, the two Comparator challenge statements. The other 26 hits are comments such as "Proved, with no `sorry`", plus one in `lakefile.lean:17`. |
| `axiom` | 0 | |
| `opaque` | 0 | |
| `native_decide` | 0 in code | 3 hits, all in comments that say it is not used: `Explicit/WeilNumC.lean:11`, `Prelim/SmallPsi.lean:10`, `Prelim/SmallPsiTable.lean:10`. |
| `implemented_by` | 0 | |
| `extern`, `unsafe`, `ofReduceBool`, `reduceBool` | 0 | |

Other checks:
- No `debug.skipKernelTC` or other kernel-bypass options.
- `set_option` uses only `maxRecDepth` (498), `maxHeartbeats` (84) and `Elab.async` (141).
- The only metaprograms are the two `elab` commands in `LadderHints.lean` (`ladder_hints%`, `ladder_chunks`).
  - They compute an untrusted 11-bit hint per rung, natively (`precompileModules`).
  - Each chunk theorem is then `⟨ladder_hints% a, by decide +kernel⟩`, so the kernel checks every rung.
  - A wrong hint can only make the build fail. It cannot make a false rung pass.

**Result: as expected.** The only sorries are the two Challenge statements.

## 5. Comparator

**Result: accepted. Exit code 0.**

Command, run from the repository root in WSL, as comparator/README.md says:

```
nice -n 19 lake comparator --config comparator/config.json
```

Setup:
- This is Lake v4.35.0's built-in comparator.
- It builds and exports the project inside a `bwrap` sandbox: bubblewrap 0.9.0 with unprivileged user namespaces, the same version Reams used.
- `comparator/config.json` names `TernaryGoldbach.ternary_goldbach_of_hypotheses` and `TernaryGoldbach.ternary_goldbach_large_of_hypotheses`, and permits only `propext`, `Quot.sound` and `Classical.choice`.
- `enable_nanoda` is false, so the second kernel was not run.
- There is no user systemd session in this distro, so there is no `systemd-run` wrapper. The README allows this.

Final lines of the output (the full log is `~/replay-logs/comparator.log`; the rest is the sandboxed build's warnings):

```
Build completed successfully (9472 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, TernaryGoldbach.ternary_goldbach_of_hypotheses, TernaryGoldbach.ternary_goldbach_large_of_hypotheses, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, ...
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

Timing (Pacific):

| Stage | From | To | Time |
|---|---|---|---|
| Sandboxed build and exports (challenge 356 MB, solution 2.32 GB) | Sun 11-08 1:55 AM | 4:35 AM | about 2 h 40 min |
| Kernel replay of `Solution` (`leanchecker --silent --from-export`, single-threaded) | Sun 11-08 4:35 AM | Mon 11-09 4:50 PM | **about 36 h 15 min** wall, about 35 CPU-hours |
| Total, `/usr/bin/time` | | | `38:55:12`; maximum RSS 3.2 GB |

Why it is so much longer than Reams's 112 minutes:
- Reams's recorded run (comparator/README.md:47) was at 83ac1e1 on 11-06, before the prime ladder was added (f714a63, 11-07). This is the first Comparator run at a commit that contains the ladder. Its 62,168 chunks of `decide +kernel` arithmetic are all re-checked in the single-threaded replay.
- A 10-second `perf` sample during the replay showed the time in the kernel's natural-number reduction (`reduce_bin_nat_op`, `is_nat_succ`).
- The replay shared a 6-core, 12-thread laptop CPU with a 12-job ladder build from 11-08 4:30 AM on. At times the WSL VM ran at BelowNormal or Idle Windows priority.
- `leanchecker` has no checkpoint or resume (v4.35.0 `src/lean/LeanChecker.lean`: one `kernelEnv.replay` call). Anyone repeating this should budget a day or more on similar hardware.

The exports are saved, cmp-verified, at `~/replay-logs/exports/` in WSL. `lake comparator --challenge-from-export ... --solution-from-export ...` can re-judge them without rebuilding.

## 6. Hypotheses against their sources

All three are stated in `TernaryGoldbach/Statement.lean`. `Challenge.lean` repeats them word for word.

### PlattGRH: no stronger than Platt, arXiv:1305.3087 Thm 7.1

Platt Thm 7.1, from the arXiv text:
- GRH holds for Dirichlet L-functions of primitive characters of modulus q ≤ 400,000;
- to height t0 = max(10^8/q, 7.5·10^7/q + 200) for even q;
- to height t0 = max(10^8/q, 3.75·10^7/q + 200) for odd q.

The Lean statement (`Statement.lean:55`) is a conjunction over primitive χ of conductor q:
- odd q ≤ 300,000, zeros with 0 < Re ρ < 1 and |Im ρ| ≤ 10^8/q;
- even q ≤ 400,000, |Im ρ| ≤ max(10^8/q, 200 + 7.5·10^7/q).

Comparison:
- The even case is exactly Platt's.
- The odd case is weaker in both range (300,000 < 400,000) and height (10^8/q ≤ Platt's max).
- q = 1 (ζ, RH to height 10^8) falls under the odd case. Platt's theorem covers all primitive characters with q ≤ 400,000, so it covers q = 1. RH to 10^8 is in any case far below Gourdon's 10^13 zeros, which Platt cites.
- Mathlib's `DirichletCharacter.LFunction` at a primitive χ is L(s, χ). For q = 1 it is ζ. The pole at s = 1 is excluded by Re ρ < 1.

**Verdict: no stronger than the source.**

### BinaryGoldbachInput: no stronger than OeSHP 2014

- Oliveira e Silva, Herzog, Pardi, *Math. Comp.* 83 (2014), no. 288, 2033-2060. The abstract (AMS page, and the author's publication page) says the even Goldbach conjecture was confirmed for all even numbers up to 4·10^18.
- Lean (`Statement.lean:64`): `BinaryGoldbachUpTo (4 * 10 ^ 18)`, every even n with 4 ≤ n ≤ 4·10^18 is a sum of two primes.

**Verdict: exactly the source, no stronger.**
- Caveat, which Reams's HYPOTHESES.md also notes: the paper double-checked only up to 3·10^17.
- The proof uses the full range: the ladder gaps are about 3.9992·10^18.

### RamareMoebius: no stronger than Ramaré, Acta Arith. 157 (2013) Cor. 1.4

Source read: Ramaré's own preprint of the paper, "From explicit estimates for the primes to explicit estimates for the Moebius function", dated November 12, 2012 (ramare-olivier.github.io/Maths/ElementaryConversion-11.pdf).
- The published version (Acta Arith. 157(4), 365-379, doi 10.4064/aa157-4-4) is paywalled and was not read.
- Cor. 1.4 in the preprint: for D ≥ 50,000, |∑_{d≤D} μ(d)/d| ≤ (3 log D − 10)/(100 (log D)^2).
- The preprint then says: "If we replace the −10 by 0, the resulting bound is valid from 11 815 onward." That bound is 3 log D/(100 (log D)^2) = 0.03/log D for D ≥ 11,815.

Lean (`Statement.lean:68`): for real x ≥ 11815, |∑_{n ∈ [1, ⌊x⌋]} μ(n)/n| ≤ 0.03/log x. This is the same statement, since the sum depends only on ⌊x⌋.

**Verdict: matches the source, no stronger.** Two notes:
- It is the remark after Cor. 1.4, not Cor. 1.4 itself (Cor. 1.4 proper is the −10 form from 50,000). Helfgott's [H, (2.21)] cites it the same way, as "[Ram13]" for x ≥ 11815.
- Reams's HYPOTHESES.md says this is the one source he did not check against the paper. This replay checked it against the preprint only. Someone with Acta Arith. access should confirm the published Cor. 1.4 kept the remark unchanged.

Independent support:
- Ramaré and Zuniga-Alterman, arXiv:2408.05969, Cor. 1.3: |m(X)| ≤ (0.0144 log X − 0.1)/(log X)^2 for X ≥ 463,421. This is stronger than 0.03/log X there.
- Reams's float check `scripts/moebius_ramare_check.py` covers [11815, 10^8). It was not re-run here.

## 7. Problems found

**None.** No defect was found in the repository at 192ca57.

Notes for readers, none of them a defect in the proof:
- The main theorems are in `TernaryGoldbach/MainTheorems.lean:16` and `:23`, not in `Statement.lean`, which defines the statement and the three hypotheses.
- The bound 0.03/log x for x ≥ 11815 is the remark at the end of Ramaré's Cor. 1.4, not the displayed corollary. It was checked against the author's 2012 preprint only.
- `comparator/README.md` says to expect about an hour and a half for the kernel replay. That was true before the ladder; at 192ca57 it took about 36 hours here.
- The build emits 1908 warnings, mostly deprecations and linter notes, and no errors.
