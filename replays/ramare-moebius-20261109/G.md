# Auditor G: Run A script, Helfgott constants, time and memory

Verdict: CONCERN. The script is ready. The Lean statements carry Helfgott's constants but over a smaller range than the book.

## 1. Run A script

File: `~/ra\out\run-A.sh`, LF line endings, pure ASCII, no `rm`.

Syntax check, run here with Git Bash 5.3.15:

```
$ bash -n run-A.sh; echo "bash -n exit=$?"
bash -n exit=0
```

Not run end to end. NOT CHECKED on WSL.

Tarball checked here:

```
b7d5c861bb1a7045d2a7b896ab9dd5a1d873cca4e463b739bbb140ffad71e8ed *full.tgz
```

It matches the brief. Its top directory is `rsbounds-20261109-full/`, as the script expects.

What it does, in order:

- Refuses to run under /mnt. Checks for /usr/bin/time, git, curl, bwrap, elan.
- bwrap check every run. It stops unless the output is exactly `bwrap-ok`.
- sha256 of the tarball. Path from `$1`, else `$TARBALL`, else `~/ra-runA/rsbounds-20261109-full.tar.gz`.
- Unpacks into `~/ra-runA/work` only if that dir is empty. A half-unpacked dir stops the script with an `mv` hint, never a delete.
- `lake exe cache get`.
- The step 2 build, verbatim from LAPTOP-COMPARATOR.md. Always rerun, since Lake resumes. The old build.log is rotated, not overwritten.
- Step 3 axioms. The log is flattened before matching, because Lean wraps the long lines. All five names must show `[propext, Classical.choice, Quot.sound]`, and no `sorryAx` or `error:` may appear.
- Step 4: comparator-moebius003.json, then comparator-upstream-ramare.json. A run is marked done only on exit 0 plus both success strings. If the short run fails, the script stops before the long one, which is what the doc intends.
- Every step runs under `/usr/bin/time -v`, `nice -n 19`, `LEAN_NUM_THREADS=10`, and `taskset -c 0-9`.
- Logs go to `~/ra-runA/logs/`: one file per step plus `.time` files, `sysinfo.log`, `oom.log` and `run-A.log`.
- Markers go to `~/ra-runA/markers/`.
- On any failure it captures uname, nproc, free and the dmesg OOM lines, then prints the summary.

Deviation from the doc: it uses `/usr/bin/time -v` instead of the shell's `time`, as the brief asks. Log names keep the doc's names: build.log, axioms.log, comparator-*.log.

Lake job limit: unsure. I did not run lake, per the rules, and I could not confirm a `-j`/`--jobs` flag for Lake 4.35.0. The script greps `lake --help` at run time and passes `-j 10` only if the flag is listed. Either way, `taskset -c 0-9` caps the run at 10 CPUs. taskset does not cap how many lean processes Lake starts, though, and that matters for memory.

Prerequisites to install: `sudo apt install bubblewrap time`. Ubuntu does not ship /usr/bin/time by default.

## 2. [H] (2.14) and (2.17)

Lean, `RSBounds/HelfgottPsiBoundsFinal.lean` in the addon:

```lean
theorem psi_le_10004 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 4e6 ≤ y) :
    Chebyshev.psi y ≤ 1.0004 * y
theorem sum_vonMangoldt_le_a14 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y
theorem sum_vonMangoldt_mul_lt_a17 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2
```

`comparator/HelfgottPsiChallenge.lean` states the same three, word for word.

Book: arXiv 1501.05438v2, dated 27 Jan 2015, chapter 2, PDF page 46, printed page 36. I fetched it and extracted the text with PyMuPDF:

- (2.14): ∑_{n≤y} Λ(n) ≤ 1.0004y for y ≥ 2·10⁶.
- (2.17): ∑_{n≤y} Λ(n)n < 1.0008 y²/2 for y > 1.6·10⁶.

The constants match, and so does the shape, since ∑_{n∈[1,⌊y⌋]} Λ(n) is ψ(y).

The ranges do not match.

- Lean proves (2.14) from 4·10⁶ for ψ and from 2.5·10⁷ for the sum form. The book claims it from 2·10⁶.
- Lean proves (2.17) from 2.5·10⁷. The book claims it from 1.6·10⁶.

So the Lean theorems are strictly weaker than the book's statements, and they add the premise FiniteRH 1894438.5122.

The challenge docstring is honest about this: "in the form and range of calr3/ternary-goldbach". The README table is not. It says "[H, (2.14)] and [H, (2.17)], with Helfgott's constants" and names no range. Anyone citing these as the book's equations is overclaiming the range.

I did not check whether 2.5·10⁷ is enough for every place the book or upstream uses (2.14) and (2.17). NOT CHECKED.

## 3. Wall time and memory for Run A on our PC

Inputs:

- Here, on 2 cores: PsiCert took about 10 h wall, MoebiusCert 63 min 40 s wall for 2.1 core-hours, and the lambda comparator took 424 s default and 2421 s paranoid.
- The short comparator run here got through the "Replayed" phase in under 3 min, so Comparator reused the build rather than rebuilding. That contradicts the brief's premise, at least for this toolchain.
- Our upstream replay: build 6 h 32 min on 8 threads, sandbox and export 2 h 40 min, kernel replay 36 h. Upstream itself reports about 90 min for its kernel replay. That 24x gap on our machine is unexplained, and it is the biggest source of uncertainty below.

Estimates. These are judgement, not measured:

| step | estimate |
|---|---|
| cache get | 5 to 15 min |
| build, 10 CPUs | 3 to 6 h. Upstream's ladder files are not in this closure, but PsiCert and MoebiusCert are. |
| axioms | under 5 min |
| comparator-moebius003 | 1 to 4 h, mostly the single-threaded replay of the Cells and Moebius003 closure |
| comparator-upstream-ramare | 12 to 30 h. The single-threaded replay of PsiCert alone is likely 8 to 15 h, plus MoebiusCert, Schoenfeld, (L) and moebius003 again. |
| total | about 18 to 40 h. Plan for two nights. If our kernel replay is as slow as his 36 h upstream run implies, the top end is right. |

Peak memory against the 31 GB WSL cap:

- Build: Cells peaks near 6 GB, and each large MoebiusCert segment near 2 GB. With 10 to 12 lean processes in parallel, a bad overlap reaches about 20 to 26 GB. That is under 31 GB but tight. A process killed this way makes Lake stop, and rerunning the script resumes.
- Kernel replay: one process. Here it was killed at 5.3 GB under a cgroup limit, while the PsiCert-only replay finished on this 7 GB machine. Expect 6 to 12 GB, well under the cap.

Main risk is the build overlap, not the replay. If the build OOMs twice, rerun as `JOBS=6 ~/ra-runA/run-A.sh`, which pins to 6 CPUs.
