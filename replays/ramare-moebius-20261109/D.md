# Auditor D: mobius003.tex against the Lean, Möbius part

Scope: `~/ra/mobius003.tex` read in full; Lean read in `RSBounds/Moebius003/`, `MoebiusCert/`,
`RSBounds/MoebiusInputs.lean`, `RSBounds/LambdaInputs.lean`, `RSBounds/LambdaInputsProof.lean`,
`RSBounds/Moebius003Statement.lean`, `RSBounds/Schoenfeld1976Targets*.lean`, `Schoenfeld1976Final.lean`.
P = `~/ra/x/rsbounds-20261109-full/RSBounds-project`. Nothing was built. No lake or lean run.

## Checks I ran myself

- grep for `native_decide|implemented_by|@[extern|axiom|sorry|ofReduceBool|skipKernelTC|admit` over
  `MoebiusCert/`, `RSBounds/Moebius003/`, `RSBounds/LambdaCert/`, `LambdaInputsProof.lean`, the three statement
  files: **zero hits**.
- MoebiusCert segment modules, theorem count vs `by decide +kernel` count:
  `Large thm=3815 dk=3815`, `Small thm=75 dk=75`, `Ms thm=158 dk=158`.
- LambdaCert tactic census: `297 by decide +kernel`, `3 by decide`, `16 by norm_num`, no native_decide.
- Moebius003 kernel checks: `cells_check`, `qcheck`, `r2_1..r2_3`, LogCert evaluations in `Tail.lean`: all
  `decide +kernel`.
- Axiom results: NOT CHECKED by me. The logs say `[propext, Classical.choice, Quot.sound]` for `target`,
  `target_L`, `mertensSqrt`, `smallMoebiusSum`, `ramareMoebius_of_finiteRH`, `ramareMoebius_of_plattGRH`
  Sources: `logs-claude/moebius003/axioms.txt`, `moebius-complete-axiom-audit.log`, `upstream-axiom-audit.log`.

## Discharge chain of `Target`

`Target := PsiThetaLog → PsiCert → MertensSqrt → SmallMoebiusSum → WeightSumBound → GHBounds → FiniteRH 1894438.5122 → RamareMoebius`

| input | discharged by | file |
|---|---|---|
| (L) WeightSumBound, GHBounds | `LambdaInputs.weightSumBound`, `ghBounds` | `TargetL.lean` via `LambdaInputsProof.lean` |
| (S) PsiThetaLog | `Schoenfeld1976Final.psiThetaLog` | `Final.lean` |
| (P) PsiCert | `Schoenfeld1976Final.psiCert` | `Final.lean` |
| (M), (m) | `MoebiusInputs.mertensSqrt`, `smallMoebiusSum` | `Complete.lean` via `MoebiusCert/Final.lean` |
| FiniteRH 1894438.5122 | `finiteRH_of_plattGRH` from upstream `rh_upto_1e8` | `Upstream.lean` |

Every input of `Target` is supplied by a theorem, not a hypothesis. The last remaining premise, `PlattGRH`, is
already an upstream hypothesis, so `ramareMoebius_of_plattGRH : PlattGRH → TernaryGoldbach.RamareMoebius`
removes `RamareMoebius` without adding anything. `RamareMoebius` body matches upstream's text as printed in
`upstream-axiom-audit.log`.

## Table

| tex item | Lean name | file | match | note |
|---|---|---|---|---|
| Theorem 1, bound part | `Moebius003.target`, `main_nat` | Main.lean | yes | Proved as `|m(n)| log(n+1) ≤ 0.03` for n ≥ 11815, then `log x ≤ log(⌊x⌋+1)`. Equivalent to the tex for real x. |
| Theorem 1, sharpness at 11814 | none | | no | Not formalized. Not needed for RamareMoebius. Benign. |
| (S) | `PsiThetaLog`, used via `Inputs.S` | Schoenfeld1976Targets.lean, Inputs.lean | yes | Lean: `x ≥ e²²`, strict `<`, C5 = 0.0077629, under FiniteRH. tex quotes it for x > V and notes it holds past e²². Lean uses it from e²². Proved upstream of here. |
| (P) | `PsiCert` | Schoenfeld1976TargetsExtra.lean | yes | `1500 ≤ x ≤ 10¹⁰`, `|ψ(x)−x| ≤ 4/5 √x`. Exact. |
| (M) | `MertensSqrt` | MoebiusInputs.lean | yes | `33 ≤ n ≤ 10⁹`, `10⁶ M(n)² ≤ 326041 n`, integer, exactly the tex checklist item 1. Proved on [1, 1000013823] by `mertens_all`, 3815+75 segments, all `decide +kernel`. |
| (m) | `SmallMoebiusSum` | MoebiusInputs.lean | yes | `11815 ≤ n ≤ 6·10⁵`, `|m(n)| log(n+1) ≤ 0.03`, checklist item 2. Covers real x up to 6·10⁵+1, slightly more than tex. Proved on [1, 602111] by `msAll`, 158 segments, `decide +kernel`, log 2 via Mathlib `log_two_lt_d9`. |
| (L) A(n) ≤ 2(n−1), n ≤ 2²⁰ | `WeightSumBound` | LambdaInputs.lean | yes | Exact range and constant. |
| (L) 36 values of G, H | `GHBounds`, `ghTable` | LambdaInputs.lean | yes, wider | 45 checkpoints, enclosures at 10⁻⁶. Spot check: G(2) ∈ [0.153425, 0.153428] vs tex 0.153426; G(2²⁰) ∈ [20.011880, 20.011883] vs 20.011881. |
| (q) | `qcheck`, `checkBlocks_sound`, `Q1_bounds` | SquarefreeData.lean | yes, form differs | Computed inside the proof by `decide +kernel`, not an input. Integer bounds [0.96, 1.17], see dep 9. |
| Constants X0, V, C5, cM | `X0 = 10^9`, `Vn = 10^10`, `C5 = 0.0077629`, `cM = 0.571` | Defs, JSum, Rho, Misc | yes | Exact. |
| λ0 = 1.10682 | `lam0 = 1.107` | Misc.lean | yes, weaker | Larger constant, proved by discrete step. |
| κ = 6/π² | `κ`, `κ_lo`, `κ_hi` | Kappa.lean | yes | Proved from Mathlib ζ(2), not computed numerically. |
| I33 = 4.78186, I0 = 36112 | `S33_le : S 33 ≤ 5.33`, `I0B = 36113` | Misc.lean | yes, weaker | dep 11. |
| C0 ≤ 1743 | `abs_C0_le_C0B`, `C0B = 1743` | Misc.lean | yes | Same constant. |
| Lemma 1, Schoenfeld identity | `schoenfeld_identity` | Schoenfeld.lean | yes | Natural x, y with floor division. Same identity, M and ρ are step functions. |
| Lemma 2 | `M_eq_of_N`, `abs_M_sub_N_div_log_le`, `abs_C0_le` | MofN.lean | yes | Discrete Abel form, any 2 ≤ X ≤ x. |
| Lemma 3, El Marraki | `el_marraki` | ElMarraki.lean | yes | Same statement with S(x) for the integral. Independent finite-sum proof. |
| Lemma 4 | `abs_rho_floor_le`, `rho_P`, `rho_P_nat`, `rho_S`, `rho_S_nat` | Rho.lean | yes, sharper at integers | dep 8. |
| Lemma 5(a) | `abs_Q_sub_le` | Squarefree.lean | yes | `|Q(x)−κx| ≤ 2√x+1`, exact. |
| Lemma 5(b) | `sum_sq_div_sqrt_le` | Squarefree.lean | different | `κ(2√J−1)+4+log J` vs `2κ√J+3(1+½log J)`. Neither dominates for all J; Lean's is what the checker uses. Benign. |
| Lemma 5(c) | `Q1_bounds` | SquarefreeData.lean | different | Integers only, [0.96, 1.17] vs real [0.578, 1.166]. Correct for the integer use. |
| Lemma 5(d) | `sum_sq_div_log_le` | Squarefree.lean | different | Extra `2κ/(L−ℓ)²`, constants 0.21, 0.96 vs 0.588, 0.578. Propagated consistently into checker and tail. |
| Lemma 6(a) | `A_le` | Weights.lean | yes | Different proof beyond 2²⁰, dep 10. I checked the pointwise inequality by hand; it is right. |
| Lemma 6(b) | `sum_weight_le` | Weights.lean | yes | Sum form instead of integral. |
| Lemma 7(a) | `S_le`, `S_X0_le` | Misc.lean | yes, weaker | dep 11. |
| Lemma 7(b) | `abs_C0_le_C0B` | Misc.lean | yes | |
| Lemma 7(c) | `range2`, `r2ok`, `r2_1..3` | Range2.lean | yes | Interval split, exact rational check with certified log and sqrt. Margin 0.0299980 vs 0.03, thinner than the tex's 0.02972 but exact. |
| Lemma 7(d) | `sum_inv_log_sq_le` | Misc.lean | yes | λ0 = 1.107. |
| Lemma 7(e) | `sum_inv_log_le` | Misc.lean | yes | Needs `log a ≥ 5`. All uses are far above e⁵. |
| Prop 8, step 1 | `cell_NM`, `ksum_bound`, `block_bound`, `rho_y_bound`, `jsum_bound` | Checker, KSum, JSum | yes | Integer U_s, dep 15, 16. |
| Prop 8, steps 2 and 3 | `step_abstract` | Step.lean | yes | ν and η conditions are the tex formulas, as inequalities. Strong induction replaces least counterexample. |
| Corollary 9 | `cell_m_bound` | Step.lean | yes | Same m_i formula with I0B = 36113. |
| Computation of §4, (i) to (iii) | `cells_check`, `checkCells_sound`, `CellsResult` | Cells, Checker, CellData | yes | Checker enforces ν ≤ 0.017, ν ≤ 0.014 when D₊ > D_mid, m_i ≤ 0.03, contiguity from 10⁹ to D_end. Cell data untrusted. |
| Prop 10 | `prop10` | Tail.lean | yes | For D ≥ D_end, ν∞ = 0.014. dep 20 to 22. |
| Corollary 11 | `tail` | Tail.lean | yes | Proves ≤ 0.03 directly, not 0.02843. Enough. |
| §6 split | `main_nat` | Main.lean | yes | [11815, 6·10⁵], (6·10⁵, 10⁹), [10⁹, D_end), [D_end, ∞). No gap: integer cases `n ≤ 6·10⁵`, `n < X0`, `n < Dend`, else. |
| RamareMoebius | `ramareMoebius_of_finiteRH`, `ramareMoebius_of_plattGRH` | Complete.lean, Upstream.lean | yes | |

## The 24 departures

| # | summary | benign? | why |
|---|---|---|---|
| 1 | Everything at integers | yes | M, N, m, ρ, Q, Q1 are step functions; final real step is in `target`. |
| 2 | Integrals become finite sums | yes | The sums are proved bounds in their own right. |
| 3 | Own LogCert | yes | Soundness theorems `logLo_le`, `le_logHi`, `sqrtLo_le` are proved. |
| 4 | κ from Mathlib ζ(2) | yes | Stronger foundation than the note. |
| 5 | Lemma 1 for natural y ≤ x | yes | All uses have natural y. |
| 6 | Lemma 2 discrete | yes | |
| 7 | Lemma 3 finite-sum proof | yes | Same statement. |
| 8 | ρ(n) = ψ(n) − n, no +1 at integers | yes | Correct since ρ(n) = ψ(n) − n exactly; `ρ_eq_psi` proves it. |
| 9 | Lemma 5 (b), (c), (d) discrete variants | yes | Different constants but proved, and the checker and tail use the Lean constants, not the tex ones. |
| 10 | Lemma 6(a) via `|λ−1| ≤ 1 + λ(1−2/log n)` | yes | Inequality holds for 0 ≤ λ ≤ L, L ≥ 1. Gives A(n) ≤ 2(n−1) with (P), (S). |
| 11 | Lemma 7 constants: I0 = 36113, λ0 = 1.107, e⁵, interval split for (c) | yes | All slightly weaker, all carried consistently. |
| 12 | Integer endpoints, D_end = 306985·10⁶⁴ | yes | `log_Dend_ge` proves ≥ 160. Checker only needs contiguity. |
| 13 | D_mid = D₁₇₃ for e¹³⁶ | yes | `exp136_ge_Dmid` proved; matches (ii) "i ≥ 173". |
| 14 | y chosen among all 45 checkpoints | yes | Internal choice; cell 1 uses y = 16384, not 10^4.125. |
| 15 | Integer U_s | yes | Correct floor ranges; requires 33β ≤ D₋ so (M) applies. |
| 16 | j-sum bound rewritten | yes | Follows from discrete Lemma 5. Keeps a +1 that is not even needed at integer points. |
| 17 | Strong induction for step 2 | yes | |
| 18 | Rounding of ν, η, I, T | yes | Upward rounding, recomputed in ℚ by the kernel. |
| 19 | Outcome numbers 0.016628, 0.011882, 0.027868 | yes | Better than the tex's 0.01681, 0.01201, 0.02812 because y may be 2²⁰. Kernel checks exact inequalities. |
| 20 | Y = ⌊D^{3/20}⌋ | yes | |
| 21 | Tail three bounds via telescoping | yes | Uses (S) at Y ≥ e²², which the Lean (S) covers. |
| 22 | No monotonicity of Φ; norm_num at L = 160 | yes | Replaces a monotonicity argument by explicit inequalities. Margin 0.0136767 vs 0.0139125. |
| 23 | Corollary 11 constants | yes | Ends at ≤ 0.03. |
| 24 | Final four ranges | yes | Checked against `main_nat`. |

No departure changes what is proved. None introduces a hypothesis.

## Findings

1. The sharpness claim of Theorem 1 at 11814 is not in Lean. Harmless.
2. Lean's (S) is used from e²², the tex says x > V. That is still Schoenfeld's (5.6b*) range and it is proved in
   `Schoenfeld1976Final`, which is another auditor's area.
3. MoebiusCert had no comparator run, per its README. Its axiom log is clean. NOT CHECKED by me.
4. Lemma 5(b), (c), (d) and Lemma 7 constants differ from the tex. All are proved and used consistently.

Verdict: PASS
