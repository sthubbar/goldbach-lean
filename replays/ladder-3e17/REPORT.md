# Prime ladder to 10^27 with gaps under 3·10^17

Steve Hubbard, 2026-11-10. Built with Claude Code on one laptop. Based on Charlie Reams's [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) at 192ca57 (Apache-2.0).

## Result

With this patch, the small cases of ternary Goldbach need binary Goldbach only up to **3·10^17**, the range Oliveira e Silva, Herzog and Pardi double-checked (Math. Comp. 83 (2014), Table 1 and section 1.3), instead of 4·10^18. The large case n ≥ 10^27 is unchanged.

- `lake build TernaryGoldbach LadderHints Challenge Solution`: **Build completed successfully (11,557 jobs)**. See [build-tail.log](build-tail.log).
- `#print axioms` ([Axioms.lean](Axioms.lean), output in [axioms.log](axioms.log)):

```
TernaryGoldbach.ternary_goldbach_of_hypotheses : PlattGRH → BinaryGoldbachInput → RamareMoebius → Statement
TernaryGoldbach.ternary_goldbach_large_of_hypotheses : PlattGRH → RamareMoebius → TernaryGoldbachFrom (10 ^ 27)
def TernaryGoldbach.BinaryGoldbachInput : Prop := TernaryGoldbach.BinaryGoldbachUpTo (3 * 10 ^ 17)
'TernaryGoldbach.ternary_goldbach_of_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryGoldbach.ternary_goldbach_large_of_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryGoldbach.Ladder.ladder_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Every rung is checked by the kernel with `decide +kernel`, as in upstream. No `native_decide`, no new axioms. `LadderHints` is compiled code that only finds hints; the kernel rechecks every rung.
- **Comparator was not run.** Upstream's 128-file ladder took leanchecker about 35 h on one core at 12 GB peak in our replay of 192ca57. This ladder is 17.2 times larger: roughly 19 days on one core, and more memory than our 31 GB machine has. An independent replay needs to be split by data file.

## What changed

| | Reams 192ca57 | This patch |
|---|---|---|
| Step S (rung i is a Proth prime `(S*i - t)*2^45 + 1`, `0 ≤ t < 2048`) | 111616 | 6478 |
| Largest gap `(S + 2047)*2^45` | 3.999·10^18 < 4·10^18 − 4 | 2.99947·10^17 < 3·10^17 − 4 |
| Rungs | 254,638,308 | 4,387,420,412 |
| Chunks of 4096 rungs | 62,168 | 1,071,148 |
| Data files | 128 | 2,205, 485 or 486 chunks each |
| Rung index bound | `i < 2^28` | `i < 2^33` |
| `BinaryGoldbachInput` | `BinaryGoldbachUpTo (4 * 10 ^ 18)` | `BinaryGoldbachUpTo (3 * 10 ^ 17)` |

Files: `scripts/gen_ladder.py` (new S and asserts on the gap and index bounds), `LadderHints.lean`, `Ladder/Check.lean`, `Ladder/Spec.lean` (`2^28` to `2^33`), `Ladder/Main.lean`, `Helfgott/SmallCases.lean`, `Helfgott/Inputs.lean`, and `Statement.lean` and `Challenge.lean` with the same new text. README, HYPOTHESES, BLUEPRINT and formalization.yaml are updated to match. `4 * 10 ^ 18` no longer appears in any `.lean` file.

## Reproduce

```sh
git clone https://github.com/calr3/ternary-goldbach && cd ternary-goldbach
git checkout 192ca57362fa3ee737cd83205cb9ea99526c4553
git apply ladder-3e17.patch        # sha256 cd05c6f740776b5821f79238258419bb78cb1c8bad3ae10997379a3fb4977ba9
python3 scripts/gen_ladder.py      # writes Ladder/Data/L0000..L2204.lean and Data.lean
lake exe cache get && lake build TernaryGoldbach LadderHints Challenge Solution
```

The patch leaves out the 2,205 generated files. Regenerating them from a fresh checkout matches the files we built: sha256 of `cat Ladder/Data/L[0-9][0-9][0-9][0-9].lean` is `db808bb54c6f79fc1633f06e4c5e8e317c8ac198c162a9827d02c59bc5b3e881`, and of `Data.lean` is `2af958ca3fc2f7284f42649585132ed5a9037e62334adb371c07cbcde0b7ad52`. Upstream's old `L000..L127.lean` should be moved out of `Ladder/Data/` first.

Lake builds the data files one at a time unless driven in parallel. `scripts/ladder-3e17-run/sched.py` runs one `lake build` per data file with a job cap and a memory guard. Cost here: one data file takes about 470 s alone with peak RSS 1.7 GB, mostly shared Mathlib pages. All 2,205 took about 59 hours on a 6-core i7-9750H with 10 to 12 jobs. The final full build took 1 h 17 min at 17.9 GB peak.

## Checks

- **Pilot:** first file L0000 (rungs 1 to 1,990,656) in 458 s, last file L2204 in 491 s, each 1.70 GB peak.
- **Negative control** ([NegControl.lean](NegControl.lean), [negcontrol.log](negcontrol.log)): the true first chunk passes. Lowering the first rung's offset by one fails with "decide proved that the proposition ... is false". Altering the last rung of the last chunk fails with "(kernel) application type mismatch".
- **Build log:** [sched.log](sched.log), one line per data file, 0 failures. A Windows crash on 11-10 cost only the 10 files in flight; every finished file was intact and loaded cleanly.

## Next

- Combine with Harald Helfgott's proof of `RamareMoebius` from PlattGRH ([Garald1/RSBounds](https://github.com/Garald1/RSBounds), rev 0393b52), so the main theorems rest on PlattGRH and binary Goldbach up to 3·10^17 alone.
- An independent replay of this ladder, split by data file.
