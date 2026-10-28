module

public import LeanLab.BS2022GRH.U7153Theorem3
public import LeanLab.ChenExplicit.TwinCNumeric

/-!
BS2022GRH, P0021, unit U-7154: Theorem 3 with the paper's normalised `U_N`.

arXiv 2211.08844 v1 page 2 and Lemma 11 on page 11 print
`U_N = 2e^{γ} ∏_{p>2} (1 - 1/(p-1)²) ∏_{p>2, p|N} (p-1)/(p-2)`, while Lemma 11 itself,
`V(x) = U_N / log x · (1 + O(...))` with `V(x) = ∏_{p<x, p∤N} (1 - 1/(p-1))`, forces by Mertens
`U_N = 2e^{-γ} C₂ Π_N`; the printed `e^{γ}` is a sign slip. The lab's old `UN n = Π_N` of
Theorem3LiPV.lean has no constant factor at all, so its h5 asks `S(A,P,z) > 8 B5 Π_N N/log²N`
with `8 B5 ≈ 7.81`, above the linear sieve upper bound `≈ 6.06 Π_N N/log²N`; see U7154_REPORT.md.

Here `UNfull n = LeanLab.ChenExplicit.U n = 2 e^{-γ} C₂ Π_N`, with `C₂ = twinC` the true twin prime
constant as a `tsum` and `twinC ≥ 0.65` PROVED in ChenExplicit/TwinCNumeric.lean.
`UNfull_eq` checks it is `2 e^{-γ} twinC · UN n` by `rfl`; `two_fifths_le_UNfull` proves
`U_N ≥ 2/5`. Since `U_N < 1` here, `theorem3_of` with `1 ≤ U` does not apply, so
`theorem3_of_U25` reproves it from the same Section 5.4 lemma with `2/5 ≤ U`; the error terms
`2N^{7/8} + N^{1/3} ≤ 10⁻⁴ N/log²N ≤ 2.5·10⁻⁴ U N/log²N` still fit in the margin.

`theorem3_of_nat_full`: Theorem 3 for natural `n`, conclusion `π₂(n) > 4·10⁻⁴ U_n n/log²n` with
the paper's `U_n`, CONDITIONAL ON Theorems 5, 6, 7 at the Section 5.4 parameters only, stated with
the same `U_n`. Lemma 10, li and the bound on `U_n` are PROVED. Caveat: the brackets are kept as
the lab transcribed them; the negligible Theorem 5 error term carries the paper's printed
`(2e^{γ} C₂)^{-1}`, see the report.

AI-written Lean code, Claude, session MANUAL-N1, unit U-7154. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

/-- The paper's `U_N = 2 e^{-γ} C₂ ∏_{p>2, p|N} (p-1)/(p-2)`, sign of `γ` corrected. -/
noncomputable def UNfull (n : ℕ) : ℝ := LeanLab.ChenExplicit.U n

lemma UNfull_eq (n : ℕ) :
    UNfull n = 2 * exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC * UN n := rfl

/-- `U_N ≥ 2/5`: `e^{-γ} ≥ e^{-2/3} ≥ 1/3`, `C₂ ≥ 0.65`, `Π_N ≥ 1`. -/
lemma two_fifths_le_UNfull (n : ℕ) : (2 / 5 : ℝ) ≤ UNfull n := by
  rw [UNfull_eq]
  have hg := eulerMascheroniConstant_lt_two_thirds
  have he : (1 / 3 : ℝ) ≤ exp (-eulerMascheroniConstant) := by
    have := add_one_le_exp (-eulerMascheroniConstant); linarith
  have hT := LeanLab.ChenExplicit.twinC_ge_065
  have hU := one_le_UN n
  have h1 : (2 / 5 : ℝ) ≤ 2 * exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC := by
    nlinarith
  nlinarith

/-- **Theorem 3, CONDITIONAL**, as `theorem3_of` but with `2/5 ≤ U` in place of `1 ≤ U`. -/
theorem theorem3_of_U25 {pi2 S0 S6 SB U li X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N)
    (hU : 2 / 5 ≤ U)
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
  have hMeq : M = U * M0 := by simp only [M, M0]; ring
  have hMM : M0 ≤ 5 / 2 * M := by rw [hMeq]; nlinarith
  have hM : 0 < M := by linarith
  have hcomb : M * (0.0015 - 8e-8 - 4e-6 - 5e-5) < M * (8 * B5 - 4 * B6 - 1 / 2 * B7) :=
    mul_lt_mul_of_pos_left hc hM
  nlinarith

/-- **Theorem 3 for a natural number `N = n` with the paper's `U_n`, CONDITIONAL** ON Theorems
5, 6, 7 at the Section 5.4 parameters only, each stated with `U_n = 2e^{-γ}C₂Π_n`. Lemma 10, the
li input and `U_n ≥ 2/5` are PROVED. -/
theorem theorem3_of_nat_full {X₂ : ℝ} {n : ℕ} (hX : exp (exp 15.85) ≤ X₂)
    (hN : X₂ ≤ (n : ℝ))
    (h5 : 8 * (UNfull n * (n : ℝ) / log (n : ℝ) ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant)
          (1 / 8137) 114 LeanLab.ChenExplicit.twinC (cG X₂) X₂ (n : ℝ) < (U7153.SA n : ℝ))
    (h6 : ∑ q ∈ U7153.Qset n, (U7153.SAq n q : ℝ) ≤ 8 * (UNfull n * (n : ℝ) / log (n : ℝ) ^ 2) *
          thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ (n : ℝ))
    (h7 : (U7153.SB n : ℝ) ≤ UNfull n * (n : ℝ) / log (n : ℝ) ^ 2 * thm7Bracket α0
          (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * (n : ℝ) ^ (1 / 8 : ℝ))) ((n : ℝ) ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * (n : ℝ) ^ (1 / 8 : ℝ)) (sqrt (n : ℝ) / log (n : ℝ) ^ 5))
          (liPV ((n : ℝ) ^ (1 / 3 : ℝ))) (n : ℝ)) :
    4e-4 * (UNfull n * (n : ℝ) / log (n : ℝ) ^ 2) < (U7153.pi2 n : ℝ) :=
  theorem3_of_U25 hX hN (two_fifths_le_UNfull n) (liPV_le (cbrt_ge_two hX hN))
    (U7153.lemma10 n (two_pow_24_le hX hN)) h5 h6 h7


end LeanLab.BS2022GRH
