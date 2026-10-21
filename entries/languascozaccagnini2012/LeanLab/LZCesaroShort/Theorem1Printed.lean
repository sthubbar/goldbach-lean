module

public import LeanLab.LZCesaroShort.Sec5Proof

/-!
# P0058 Theorems 1 and 2 eq. (3) as printed, and the corrected positivity link

Lab file, unit U-6100, CLOUD 20261020T0618Z-cloud36. AI wrote this file. Binary Goldbach is OPEN.

Faithfulness correction. `Statements.lean` reads the first error term of Theorem 1 and the
bound of Theorem 2 eq. (3) as `N log(2N²/H)`; that came from the pdftotext layer, which drops the
square. The page images of arXiv 1606.00869 v1 p. 2 and v2 p. 2 both print
`N (log(2N/H))²`, and v2 p. 10 eq. (30) ends in `HN (log(2N/H))²`. Neither bound implies the
other: at `H = 1` the printed one is larger, at `H = N` the lab one is larger.

`Theorem1P` and `Theorem2bP` are the printed statements. `cesaro_pos_of_printed` is the
positivity link from the printed Theorem 1: it needs `C log² N ≤ H`, not the `C log N ≤ H` of
`cesaro_pos_of`, which rests on the misread `Theorem1` and so is not a consequence of the paper.
-/

@[expose] public section


open Finset Filter Asymptotics
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.LZCesaroShort

/-- Theorem 1 as printed, v1 and v2 p. 2: error `N (log(2N/H))² + H (log N)² log(2H)`. -/
def Theorem1P : Prop :=
  ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K * (N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H))

/-- Theorem 2 eq. (3) as printed: the full sum, `y = H`, is `≪ N (log(2N/H))²`. -/
def Theorem2bP : Prop :=
  ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    |wsum N H H| ≤ K * N * Real.log (2 * (N : ℝ) / H) ^ 2

/-- Vacuity check: the printed error term is positive in the whole range. -/
theorem theorem1P_rhs_pos {N H : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) :
    0 < (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHN' : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have h1 : 1 < 2 * (N : ℝ) / H := by rw [lt_div_iff₀ (by linarith)]; linarith
  have h2 : 0 < Real.log (2 * (N : ℝ) / H) := Real.log_pos h1
  have h3 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have h4 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have : 0 < (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2 := by positivity
  have : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  linarith

/-- The two readings differ: at `H = 1` the printed term `N log²(2N)` exceeds the lab's
`N log(2N²)` once `N ≥ 8`. -/
theorem printed_gt_lab_at_one {N : ℕ} (hN : 8 ≤ N) :
    (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / 1) < N * Real.log (2 * (N : ℝ) / 1) ^ 2 := by
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [div_one, div_one]
  set l := Real.log (2 * (N : ℝ))
  have hl : Real.log (2 * (N : ℝ) ^ 2) = 2 * l - Real.log 2 := by
    have : 2 * (N : ℝ) ^ 2 = (2 * N) ^ 2 / 2 := by ring
    rw [this, Real.log_div (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
  have hl3 : 2 < l := by
    have h16 : (16 : ℝ) ≤ 2 * N := by linarith
    have : Real.log 16 ≤ l := Real.log_le_log (by norm_num) h16
    have h2 : (2 : ℝ) < Real.log 16 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hl]
  have : 2 * l - Real.log 2 < l ^ 2 := by nlinarith
  exact mul_lt_mul_of_pos_left this hN0

set_option maxHeartbeats 2000000 in
/-- **Corrected link.** The printed Theorem 1 and the Section 5 bound give a positive Cesàro sum
for every `H` with `C log² N ≤ H ≤ N`, `N` large. -/
theorem cesaro_pos_of_printed (h1 : Theorem1P) (h5 : Sec5RH) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → H ≤ N →
      0 < cesaro N H := by
  obtain ⟨K1', hK1⟩ := h1
  obtain ⟨N5, K2', hK2⟩ := h5
  set K1 := |K1'|
  set K2 := |K2'|
  have K1n : 0 ≤ K1 := abs_nonneg _
  have K2n : 0 ≤ K2 := abs_nonneg _
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (eventually_small (2 * K1 + 2 * K2))
  refine ⟨32 * K1 + 8 * K2 + 4, max (max Ne N5) 3, fun N H hN hCH hHN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 ≤ Real.log N := by linarith
  have hL2 : 1 ≤ Real.log N ^ 2 := by nlinarith
  have hHR : (4 : ℝ) ≤ H := by
    have : (4 : ℝ) * 1 ≤ (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 :=
      mul_le_mul (by linarith) hL2 (by norm_num) (by linarith)
    linarith
  have hH2 : 2 ≤ H := by exact_mod_cast (show (2 : ℝ) ≤ H by linarith)
  have hH1 : 1 ≤ H := by omega
  have hHle : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hHp : (0 : ℝ) < H := by linarith
  obtain ⟨hs1, hs2⟩ := hNe N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have b1 := hK1 N H (by omega) hH1 hHN
  have b2 := hK2 N H (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) hH2 hHN
  -- logs
  have hlogA : Real.log (2 * (N : ℝ) / H) ≤ 2 * Real.log N := by
    have : 2 * (N : ℝ) / H ≤ (N : ℝ) ^ 2 := by
      rw [div_le_iff₀ hHp]; nlinarith
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogA0 : 0 ≤ Real.log (2 * (N : ℝ) / H) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hHp]; linarith
  have hlogA2 : Real.log (2 * (N : ℝ) / H) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
  have hlogB : Real.log (2 * (H : ℝ)) ≤ 2 * Real.log N := by
    have : 2 * (H : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlogB0 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have X1n : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
      + H * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  have b1' : ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K1 * (N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H)) :=
    le_trans b1 (mul_le_mul_of_nonneg_right (le_abs_self K1') X1n)
  have X2n : 0 ≤ (H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N := by positivity
  have b2' : ‖ZH N H / (H : ℂ)‖ ≤ K2 * (H * Real.sqrt N * Real.log N ^ 2 + N) :=
    le_trans b2 (mul_le_mul_of_nonneg_right (le_abs_self K2') X2n)
  set E : ℂ := 2 / (H : ℂ) * ZH N H
  have hE : ‖E‖ ≤ 2 * (K2 * ((H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N)) := by
    have : E = 2 * (ZH N H / (H : ℂ)) := by simp only [E]; ring
    rw [this, norm_mul]; simp only [Complex.norm_ofNat]; linarith
  have hreal : (H : ℝ) * N - cesaro N H ≤ ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + E‖ + ‖E‖ := by
    have e : (((H : ℝ) * N - cesaro N H : ℝ) : ℂ)
        = -((((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + E)) + E := by push_cast; ring
    calc (H : ℝ) * N - cesaro N H ≤ ‖((((H : ℝ) * N - cesaro N H : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ _ := by rw [e]; exact le_trans (norm_add_le _ _) (by rw [norm_neg])
  have hCL : (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 * N ≤ H * N :=
    mul_le_mul_of_nonneg_right hCH (by positivity)
  -- the error terms
  have t1 : K1 * (N * Real.log (2 * (N : ℝ) / H) ^ 2) ≤ 4 * K1 * N * Real.log N ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlogA2 (show 0 ≤ K1 * N by positivity); linarith
  have t2 : K1 * (H * Real.log N ^ 2 * Real.log (2 * H)) ≤ 2 * K1 * H * Real.log N ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlogB (show 0 ≤ K1 * H * Real.log N ^ 2 by positivity)
    have e : K1 * H * Real.log N ^ 2 * (2 * Real.log N) = 2 * K1 * H * Real.log N ^ 3 := by ring
    linarith
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
  have hsqn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have t3 : 2 * K1 * H * Real.log N ^ 3 ≤ H * N / 4 := by
    have : 2 * K1 * Real.log N ^ 3 ≤ N / 4 := by
      have : 2 * K1 * Real.log N ^ 3 ≤ (2 * K1 + 2 * K2) * Real.log N ^ 3 := by
        nlinarith [pow_nonneg hL0 3]
      linarith
    have := mul_le_mul_of_nonneg_left this hHp.le
    have e : (H : ℝ) * (2 * K1 * Real.log N ^ 3) = 2 * K1 * H * Real.log N ^ 3 := by ring
    linarith
  have t4 : 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) ≤ H * N / 4 := by
    have hs : 2 * K2 * Real.log N ^ 2 ≤ Real.sqrt N / 4 := by
      have : 2 * K2 * Real.log N ^ 2 ≤ (2 * K1 + 2 * K2) * Real.log N ^ 2 := by
        nlinarith [pow_nonneg hL0 2]
      linarith
    have := mul_le_mul_of_nonneg_left hs (show 0 ≤ (H : ℝ) * Real.sqrt N by positivity)
    have e1 : (H : ℝ) * Real.sqrt N * (Real.sqrt N / 4) = H * N / 4 := by
      rw [mul_assoc, ← mul_div_assoc, hsq]; ring
    have e2 : (H : ℝ) * Real.sqrt N * (2 * K2 * Real.log N ^ 2)
        = 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) := by ring
    linarith
  have t1' : 4 * K1 * N * Real.log N ^ 2 ≤ H * N / 8 := by
    have h8 : 32 * K1 * Real.log N ^ 2 * N ≤ (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 * N := by
      have : 0 ≤ (8 * K2 + 4) * Real.log N ^ 2 * N := by positivity
      nlinarith
    nlinarith
  have t5 : 2 * K2 * (N : ℝ) ≤ H * N / 4 := by
    have h8 : 8 * K2 * N ≤ (32 * K1 + 8 * K2 + 4) * Real.log N ^ 2 * N := by
      have : 8 * K2 * N * 1 ≤ 8 * K2 * N * Real.log N ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      have : 0 ≤ (32 * K1 + 4) * Real.log N ^ 2 * N := by positivity
      nlinarith
    nlinarith
  have hfin : (H : ℝ) * N - cesaro N H ≤ 7 * (H * N) / 8 := by
    have e1 : K1 * ((N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
        + H * Real.log N ^ 2 * Real.log (2 * H))
        = K1 * (N * Real.log (2 * (N : ℝ) / H) ^ 2) + K1 * (H * Real.log N ^ 2 * Real.log (2 * H)) :=
      by ring
    have e2 : 2 * (K2 * ((H : ℝ) * Real.sqrt N * Real.log N ^ 2 + N))
        = 2 * K2 * (H * Real.sqrt N * Real.log N ^ 2) + 2 * K2 * N := by ring
    linarith
  have : 0 < (H : ℝ) * N := by positivity
  linarith

/-- The corrected short-window statement: sums of two prime powers in every `[N - H, N + H]` with
`C log² N ≤ H ≤ N`, `N` large, CONDITIONAL ON RH and the printed Theorem 1. -/
theorem exists_R_pos_short_printed (hRH : RiemannHypothesis) (h1 : Theorem1P) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → H ≤ N →
      ∃ n ∈ Icc (N - H) (N + H), ∃ a b : ℕ, IsPrimePow a ∧ IsPrimePow b ∧ a + b = n := by
  obtain ⟨C, N₀, h⟩ := cesaro_pos_of_printed h1 (lz_sec5_rh_proved hRH)
  refine ⟨C, N₀, fun N H hN hC hH => ?_⟩
  obtain ⟨n, hn, hR⟩ := exists_R_pos_of_cesaro_pos (h N H hN hC hH)
  exact ⟨n, hn, primePow_sum_of_R_pos hR⟩

end LeanLab.LZCesaroShort

