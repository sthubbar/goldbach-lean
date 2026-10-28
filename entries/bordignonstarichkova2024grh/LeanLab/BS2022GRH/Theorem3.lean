module

public import LeanLab.BS2022GRH.Lemma9M

/-!
BS2022GRH, P0021: Theorem 3 and Corollary 1 assembled from Lemma 10 and Theorems 5, 6, 7.

Bordignon, Starichkova, An explicit version of Chen's theorem assuming GRH, arXiv 2211.08844 v1,
Section 5 and Section 5.4, read in Claude in Chrome 2026-10-18 by run 20261018T2103Z-18477.

* Lemma 10, Chen, cited as [13, Theorem 10.2]:
  `π₂(N) > S(A,P,z) - 1/2 Σ_{z ≤ q < y} S(A_q,P,z) - 1/2 S(B,P,y) - 2 N^{7/8} - N^{1/3}`.
* Theorem 5: `S(A,P,z) > 8 U_N N / log² N · thm5Bracket`.
* Theorem 6: `Σ S(A_q,P,z) ≤ 8 U_N N / log² N · thm6Bracket`.
* Theorem 7: `S(B,P,y) ≤ U_N N / log² N · thm7Bracket`.

Here the four sieve quantities, `π₂(N)`, `U_N` and `li(y)` are real variables and every one of
the cited results above enters as a hypothesis, so `theorem3_of` is CONDITIONAL ON Lemma 10,
Theorems 5, 6, 7 at the Section 5.4 parameters, `U_N ≥ 1` and `li(y) ≤ ∫₂^y dt/log t + 2`,
weaker than the paper's `+ 1.046`; Theorem3LiPV.lean discharges the last two.
Everything else, the whole Section 5.4 arithmetic and the error terms `2N^{7/8} + N^{1/3}`, is
proved. AI wrote the Lean code.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

/-- `x^4/24 ≤ exp x` for `x ≥ 0`. -/
lemma exp_ge_four {t : ℝ} (ht : 0 ≤ t) : t ^ 4 / 24 ≤ exp t := by
  have h := Real.pow_div_factorial_le_exp (x := t) ht 4
  norm_num [Nat.factorial] at h; exact h

/-- For `log N ≥ 7.64·10⁶`: `2 N^{7/8} + N^{1/3} ≤ 10⁻⁴ · N / log² N`, and also
`√N + 1 ≤ 10⁻⁴ · N / log² N`. -/
lemma error_terms {N : ℝ} (hN : 0 < N) (hL : 7640000 ≤ log N) :
    2 * N ^ (7 / 8 : ℝ) + N ^ (1 / 3 : ℝ) ≤ 1e-4 * (N / log N ^ 2) ∧
    sqrt N + 1 ≤ 1e-4 * (N / log N ^ 2) := by
  set L := log N with hLdef
  have hL0 : 0 < L := by linarith
  have eN : N = exp L := (exp_log hN).symm
  -- N^{1/8} ≥ 3000 L²
  have h8 : 30000 * L ^ 2 ≤ exp (L / 8) := by
    have h := exp_ge_four (t := L / 8) (by positivity)
    have : 30000 * L ^ 2 ≤ (L / 8) ^ 4 / 24 := by
      have hL2 : (30000 * 24 * 4096 : ℝ) ≤ L ^ 2 := by nlinarith
      have : (L / 8) ^ 4 / 24 = L ^ 2 * L ^ 2 / (24 * 4096) := by ring
      rw [this, le_div_iff₀ (by norm_num)]
      nlinarith [sq_nonneg L]
    linarith
  have r78 : N ^ (7 / 8 : ℝ) = exp (L * (7 / 8)) := by rw [rpow_def_of_pos hN]
  have r13 : N ^ (1 / 3 : ℝ) = exp (L * (1 / 3)) := by rw [rpow_def_of_pos hN]
  have hsq : sqrt N = exp (L / 2) := by
    rw [eN, sqrt_eq_iff_mul_self_eq_of_pos (exp_pos _), ← exp_add]; ring_nf
  have hdiv : N / L ^ 2 = exp (L * (7 / 8)) * (exp (L / 8) / L ^ 2) := by
    rw [eN, mul_div_assoc', ← exp_add]; ring_nf
  have hq : 30000 ≤ exp (L / 8) / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have e13 : exp (L * (1 / 3)) ≤ exp (L * (7 / 8)) := exp_le_exp.2 (by nlinarith)
  have e12 : exp (L / 2) ≤ exp (L * (7 / 8)) := exp_le_exp.2 (by nlinarith)
  have e1 : (1 : ℝ) ≤ exp (L * (7 / 8)) := one_le_exp (by nlinarith)
  have hpos := exp_pos (L * (7 / 8))
  have key : 3 * exp (L * (7 / 8)) ≤ 1e-4 * (N / L ^ 2) := by
    rw [hdiv]; nlinarith
  refine ⟨?_, ?_⟩
  · rw [r78, r13]; linarith
  · rw [hsq]; linarith

/-- **Theorem 3, CONDITIONAL.** For `N ≥ X₂ ≥ exp(exp 15.85)`, if Lemma 10 and Theorems 5, 6
and 7 hold at the Section 5.4 parameters, `U_N ≥ 1` and `li(y) ≤ ∫₂^y dt/log t + 2` with
`y = N^{1/3}`, then `π₂(N) > 4·10⁻⁴ U_N N / log² N`. CONDITIONAL ON those named inputs. -/
theorem theorem3_of {pi2 S0 S6 SB U li X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N)
    (hU : 1 ≤ U)
    (hli : li ≤ (∫ t in (2 : ℝ)..N ^ (1 / 3 : ℝ), 1 / log t) + 2)
    (h10 : S0 - 1 / 2 * S6 - 1 / 2 * SB - 2 * N ^ (7 / 8 : ℝ) - N ^ (1 / 3 : ℝ) < pi2)
    (h5 : 8 * (U * N / log N ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N < S0)
    (h6 : S6 ≤ 8 * (U * N / log N ^ 2) * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ N)
    (h7 : SB ≤ U * N / log N ^ 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5)) li N) :
    4e-4 * (U * N / log N ^ 2) < pi2 := by
  obtain ⟨hL, hN0⟩ := logN_ge hX hN
  have hm := theorem3_main_thm567_m hX hN hli
  rw [K3_third] at hm
  obtain ⟨hE, -⟩ := error_terms hN0 hL
  set B5 := thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
  set B6 := thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
  set B7 := thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5)) li N
  have hc : (0.0015 - 8e-8 - 4e-6 - 5e-5 : ℝ) < 8 * B5 - 4 * B6 - 1 / 2 * B7 := by linarith
  set M := U * N / log N ^ 2
  set M0 := N / log N ^ 2
  have hM0 : 0 < M0 := by positivity
  have hMM : M0 ≤ M := by
    show N / log N ^ 2 ≤ U * N / log N ^ 2
    gcongr; nlinarith
  have hM : 0 < M := lt_of_lt_of_le hM0 hMM
  have hcomb : M * (0.0015 - 8e-8 - 4e-6 - 5e-5) < M * (8 * B5 - 4 * B6 - 1 / 2 * B7) :=
    mul_lt_mul_of_pos_left hc hM
  nlinarith

/-- **Corollary 1, CONDITIONAL.** With `π₂'(N) ≥ π₂(N) - √N - 1`, as in Section 5.5, and the
inputs of `theorem3_of`, `π₂'(N) > 0`: `N` is a prime plus a squarefree semiprime. -/
theorem corollary1_of {pi2 pi2' S0 S6 SB U li X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂)
    (hN : X₂ ≤ N) (hU : 1 ≤ U)
    (hli : li ≤ (∫ t in (2 : ℝ)..N ^ (1 / 3 : ℝ), 1 / log t) + 2)
    (h10 : S0 - 1 / 2 * S6 - 1 / 2 * SB - 2 * N ^ (7 / 8 : ℝ) - N ^ (1 / 3 : ℝ) < pi2)
    (h5 : 8 * (U * N / log N ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N < S0)
    (h6 : S6 ≤ 8 * (U * N / log N ^ 2) * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ N)
    (h7 : SB ≤ U * N / log N ^ 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5)) li N)
    (hC : pi2 - sqrt N - 1 ≤ pi2') :
    0 < pi2' := by
  have h3 := theorem3_of hX hN hU hli h10 h5 h6 h7
  obtain ⟨hL, hN0⟩ := logN_ge hX hN
  obtain ⟨-, hE⟩ := error_terms hN0 hL
  have hM0 : 0 < N / log N ^ 2 := by positivity
  have hMM : N / log N ^ 2 ≤ U * N / log N ^ 2 := by gcongr; nlinarith
  nlinarith


end LeanLab.BS2022GRH
