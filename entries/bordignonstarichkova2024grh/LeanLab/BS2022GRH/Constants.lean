module

public import Mathlib
public import LeanLab.BS2022GRH.Params
public import LeanLab.ChenExplicit.BJSCbar
public import LeanLab.ChenExplicit.GammaBounds

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T1803Z-10253, unit U-0963.
P0021 Bordignon, Starichkova 2022, arXiv 2211.08844 v1: printed constants of Lemmas 3, 13,
14, 15 and the main-term margin of Theorem 3 at the Section 5.4 parameters.

PROVED, no cited input:
* `qG_le`: q_G(4·10¹⁸) ≤ 0.6399, Lemma 3 prints ≤ 0.640. MATCH, the value is 0.63985.
* `pG_le`, `cG_le`: p_G(4·10¹⁸) ≤ 0.429 and c_G(4·10¹⁸) ≤ 0.429, Lemmas 13 and 14. MATCH.
  These are checked at the endpoint X₂ = 4·10¹⁸ only, not for every X₂ ≥ 4·10¹⁸.
* `lemma13_const`: 1/(16π) ≤ 0.02. `lemma14_const`: 0.65 · 1.3841 ≤ 0.9. MATCH.
* `Hz_const`: (8/7) log(13/8) ≤ 0.56, the H(z) ≤ 0.56/log N of Lemma 15's proof by the
  substitution t = N^τ, which gives H(z) log N = (8/7) log(13/8) ≈ 0.5549. MATCH.
* `lemma15_gap`: 64 log(26/21) < 36. Lemma 15's statement has 64 log(26/21)/log³N where its
  proof ends with 36/log³N; see FINDINGS. Harmless at log N ≈ 7.6·10⁶.
* `theorem3_main`: the main-term constant of Theorem 3 at α = 10^{-2.61}, ε = 1/8137,
  C₁ = 112, C₂ = 114 and c̄ = Lemma 15's integral,
    K = 8(2e^γ log(3−8α)/(4−8α) − εC₂·3e^{8α−2}/(4−8α))
        − ½·8(e^γ/4 · (log 6 + log((3−8α)/(3−18α)))/(½−α) + log(8/3) εC₁)
        − ½(2e^γ/(½−α) + 3εC₁) c̄,
  satisfies K > 0.0015, above the paper's 4·10⁻⁴. The value is 0.00193. The factors the
  paper carries beside these, such as 1 − 0.62 log X₂/X₂^{1/16}, (1 + 3·10⁻⁷) and the
  c_G/log^{A−2}N terms, differ from 1 or 0 by less than 10⁻⁶ at X₂ = exp(exp 15.85) and are
  not formalized here. Uses `BJS.cbar_lt`, c̄ < 0.363084, and the lab's γ bounds.
Goldbach is open.
-/

@[expose] public section

open Real Finset

set_option exponentiation.threshold 2000

noncomputable section
namespace LeanLab.BS2022GRH

/-- q_G of Lemma 3. -/
def qG (X : ℝ) : ℝ :=
  0.165 + 12.683 / log X + 254.980 / (log X) ^ 2 + 2607.854 / (log X) ^ 3 + 11605.056 / (log X) ^ 4
  + 1.314 * log X / X ^ ((1 : ℝ) / 4) + 0.092 * log (log X) / X ^ ((1 : ℝ) / 4)
  + 60.883 / X ^ ((1 : ℝ) / 4) + 8.250 * log (log X) / (X ^ ((1 : ℝ) / 4) * log X)
  + 939.260 / (X ^ ((1 : ℝ) / 4) * log X) - 237.934 / (sqrt X * log X)

/-- p_G of Lemma 13. -/
def pG (X : ℝ) : ℝ := 0.65 * (0.02 + qG X)
/-- c_G of Lemma 14. -/
def cG (X : ℝ) : ℝ := pG X + 0.9 / (sqrt X * log (log X))

lemma exp084_ge : (2.316366 : ℝ) ≤ exp 0.84 := by
  have h := Real.sum_le_exp_of_nonneg (x := (0.84 : ℝ)) (by norm_num) 14
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

lemma logX_bounds : (42.83 : ℝ) ≤ log 4e18 ∧ log 4e18 ≤ 42.84 := by
  constructor
  · rw [Real.le_log_iff_exp_le (by norm_num)]
    have e : (42.83 : ℝ) = ((42 : ℕ) : ℝ) + 0.83 := by norm_num
    rw [e, exp_add]
    calc exp ((42 : ℕ) : ℝ) * exp 0.83 ≤ 2.7182818286 ^ 42 * 2.293319 := by
          gcongr
          · exact exp_nat_le 42
          · exact exp083_le
      _ ≤ 4e18 := by norm_num
  · rw [Real.log_le_iff_le_exp (by norm_num)]
    have e : (42.84 : ℝ) = ((42 : ℕ) : ℝ) + 0.84 := by norm_num
    rw [e, exp_add]
    calc (4e18 : ℝ) ≤ 2.7182818283 ^ 42 * 2.316366 := by norm_num
      _ ≤ exp ((42 : ℕ) : ℝ) * exp 0.84 := by
          gcongr
          · exact exp_nat_ge 42
          · exact exp084_ge

lemma X4_ge : (44721 : ℝ) ≤ (4e18 : ℝ) ^ ((1 : ℝ) / 4) := by
  have hp : 0 < (4e18 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  rw [← pow_le_pow_iff_left₀ (by norm_num) hp.le (by norm_num : (4 : ℕ) ≠ 0),
    ← Real.rpow_natCast ((4e18 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma sqrtX : sqrt (4e18 : ℝ) = 2e9 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num

lemma loglogX_bounds : (1 : ℝ) ≤ log (log 4e18) ∧ log (log 4e18) ≤ 4 := by
  obtain ⟨h1, h2⟩ := logX_bounds
  constructor
  · rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  · rw [Real.log_le_iff_le_exp (by linarith)]
    have h := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 6
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith

/-- **Lemma 3's q_G(4·10¹⁸) ≤ 0.640**, here with 0.6399. -/
theorem qG_le : qG 4e18 ≤ 0.6399 := by
  obtain ⟨hL1, hL2⟩ := logX_bounds
  obtain ⟨hl1, hl2⟩ := loglogX_bounds
  have hX4 := X4_ge
  unfold qG
  set L := log (4e18 : ℝ)
  set l := log L
  set Y := (4e18 : ℝ) ^ ((1 : ℝ) / 4)
  have hLp : 0 < L := by linarith
  have hYp : 0 < Y := by linarith
  have t1 : 12.683 / L ≤ 12.683 / 42.83 := by gcongr
  have t2 : 254.980 / L ^ 2 ≤ 254.980 / (42.83 : ℝ) ^ 2 := by gcongr
  have t3 : 2607.854 / L ^ 3 ≤ 2607.854 / (42.83 : ℝ) ^ 3 := by gcongr
  have t4 : 11605.056 / L ^ 4 ≤ 11605.056 / (42.83 : ℝ) ^ 4 := by gcongr
  have t5 : 1.314 * L / Y ≤ 1.314 * 42.84 / 44721 := by gcongr
  have t6 : 0.092 * l / Y ≤ 0.092 * 4 / 44721 := by
    have : 0 ≤ l := by linarith
    gcongr
  have t7 : 60.883 / Y ≤ 60.883 / 44721 := by gcongr
  have t8 : 8.250 * l / (Y * L) ≤ 8.250 * 4 / (44721 * 42.83) := by
    have : 0 ≤ l := by linarith
    gcongr
  have t9 : 939.260 / (Y * L) ≤ 939.260 / (44721 * 42.83) := by gcongr
  have t10 : 0 ≤ 237.934 / (sqrt 4e18 * L) := by positivity
  have : (0.165 : ℝ) + 12.683 / 42.83 + 254.980 / 42.83 ^ 2 + 2607.854 / 42.83 ^ 3 +
      11605.056 / 42.83 ^ 4 + 1.314 * 42.84 / 44721 + 0.092 * 4 / 44721 + 60.883 / 44721 +
      8.250 * 4 / (44721 * 42.83) + 939.260 / (44721 * 42.83) ≤ 0.6399 := by norm_num
  linarith

theorem pG_le : pG 4e18 ≤ 0.429 := by
  unfold pG; linarith [qG_le]

theorem cG_le : cG 4e18 ≤ 0.429 := by
  unfold cG pG
  rw [sqrtX]
  have hl := loglogX_bounds.1
  have : 0.9 / (2e9 * log (log 4e18)) ≤ 0.9 / (2e9 * 1) := by gcongr
  have := qG_le
  have : (0.65 : ℝ) * (0.02 + 0.6399) + 0.9 / (2e9 * 1) ≤ 0.429 := by norm_num
  nlinarith

theorem lemma13_const : 1 / (16 * π) ≤ 0.02 := by
  have := Real.pi_gt_d2
  rw [div_le_iff₀ (by positivity)]; nlinarith

theorem lemma14_const : (0.65 : ℝ) * 1.3841 ≤ 0.9 := by norm_num

theorem Hz_const : 8 / 7 * log (13 / 8) ≤ (0.56 : ℝ) := by
  have h : log (13 / 8 : ℝ) ≤ 0.49 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := (0.49 : ℝ)) (by norm_num) 6
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  linarith

theorem lemma15_gap : 64 * log (26 / 21) < (36 : ℝ) := by
  have := Real.log_le_sub_one_of_pos (x := (26 / 21 : ℝ)) (by norm_num)
  linarith

/-! ### Theorem 3, main-term margin -/

/-- The main-term constant of Theorem 3, from Theorems 5, 6 and 7 and Lemma 10. -/
def K3 (α g ε C₁ C₂ cb : ℝ) : ℝ :=
  8 * (2 * g * log (3 - 8 * α) / (4 - 8 * α) - ε * C₂ * 3 * exp (8 * α - 2) / (4 - 8 * α))
  - 1 / 2 * (8 * (g / 4 * (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)
      + log (8 / 3) * ε * C₁))
  - 1 / 2 * ((2 * g / (1 / 2 - α) + 3 * ε * C₁) * cb)

lemma g_bounds : (1.78103 : ℝ) ≤ exp eulerMascheroniConstant ∧
    exp eulerMascheroniConstant ≤ 1.781081 := by
  have h1 := LeanLab.ChenExplicit.Gamma.gamma_gt
  have h2 := LeanLab.ChenExplicit.Gamma.gamma_lt
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := (0.57720 : ℝ)) (by norm_num) 12
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith [exp_le_exp.mpr h1.le]
  · have h := Real.exp_bound' (x := (0.57722 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith [exp_le_exp.mpr h2.le]

lemma log3_ge {α : ℝ} (h : α ≤ 0.0024548) : (1.09204 : ℝ) ≤ log (3 - 8 * α) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have e : (1.09204 : ℝ) = 1 + 0.09204 := by norm_num
  rw [e, exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 : exp (0.09204 : ℝ) ≤ 1.0964088 := by
    have h := Real.exp_bound' (x := (0.09204 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc exp 1 * exp 0.09204 ≤ 2.7182818286 * 1.0964088 := by gcongr
    _ ≤ 3 - 8 * α := by norm_num; linarith

lemma exp82_le {α : ℝ} (h : α ≤ 0.0024548) : exp (8 * α - 2) ≤ (0.13803 : ℝ) := by
  have h1 : exp (8 * α - 2) ≤ exp (-1.9803616) := exp_le_exp.mpr (by linarith)
  have h2 : (7.2449 : ℝ) ≤ exp 1.9803616 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1.9803616 : ℝ)) (by norm_num) 16
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  rw [exp_neg] at h1
  have : (exp 1.9803616)⁻¹ ≤ (7.2449 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have : (7.2449 : ℝ)⁻¹ ≤ 0.13803 := by norm_num
  linarith

lemma log6_le : log (6 : ℝ) ≤ 1.79176 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have e : (1.79176 : ℝ) = 1 + 0.79176 := by norm_num
  rw [e, exp_add]
  have h1 := Real.exp_one_gt_d9
  have h2 : (2.207277 : ℝ) ≤ exp 0.79176 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.79176 : ℝ)) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc (6 : ℝ) ≤ 2.7182818283 * 2.207277 := by norm_num
    _ ≤ exp 1 * exp 0.79176 := by gcongr

lemma log83_le : log (8 / 3 : ℝ) ≤ 0.98083 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := (0.98083 : ℝ)) (by norm_num) 16
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

lemma logr_le {α : ℝ} (h0 : 0 ≤ α) (h : α ≤ 0.0024548) :
    log ((3 - 8 * α) / (3 - 18 * α)) ≤ 0.024548 / (3 - 18 * 0.0024548) := by
  have hp : 0 < 3 - 18 * α := by linarith
  refine le_trans (Real.log_le_sub_one_of_pos (div_pos (by linarith) hp)) ?_
  have e : (3 - 8 * α) / (3 - 18 * α) - 1 = 10 * α / (3 - 18 * α) := by
    rw [div_sub_one hp.ne']; congr 1; ring
  rw [e]
  have : 10 * α ≤ 0.024548 := by linarith
  have : (3 : ℝ) - 18 * 0.0024548 ≤ 3 - 18 * α := by linarith
  calc 10 * α / (3 - 18 * α) ≤ 0.024548 / (3 - 18 * α) := by gcongr
    _ ≤ 0.024548 / (3 - 18 * 0.0024548) := by gcongr

/-- **Theorem 3's main-term margin** at the Section 5.4 parameters: K > 0.0015 > 4·10⁻⁴. -/
theorem theorem3_main :
    (0.0015 : ℝ) < K3 α0 (exp eulerMascheroniConstant) (1 / 8137) 112 114 LeanLab.ChenExplicit.BJS.cbar := by
  have ha1 := alpha_ge
  have ha2 := alpha_le
  obtain ⟨hg1, hg2⟩ := g_bounds
  have hc := LeanLab.ChenExplicit.BJS.cbar_lt
  have hc0 := LeanLab.ChenExplicit.BJS.cbar_gt
  have hl3 := log3_ge ha2
  have he := exp82_le ha2
  have hl6 := log6_le
  have hl83 := log83_le
  have hlr := logr_le (by linarith) ha2
  have hl83' : 0 ≤ log (8 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  set α := α0
  set g := exp eulerMascheroniConstant
  set cb := LeanLab.ChenExplicit.BJS.cbar
  set r := log ((3 - 8 * α) / (3 - 18 * α))
  -- term 1, lower bound
  have T1 : 2 * 1.78103 * 1.09204 / (4 - 8 * 0.0024547) ≤ 2 * g * log (3 - 8 * α) / (4 - 8 * α) := by
    have hd : 0 < 4 - 8 * α := by linarith
    rw [div_le_div_iff₀ (by norm_num) hd]
    have : 0 ≤ log (3 - 8 * α) := by linarith
    nlinarith [mul_le_mul hg1 hl3 (by norm_num) (by linarith)]
  have T2 : (1 / 8137) * 114 * 3 * exp (8 * α - 2) / (4 - 8 * α) ≤
      (1 / 8137) * 114 * 3 * 0.13803 / (4 - 8 * 0.0024548) := by
    have hd : 0 < 4 - 8 * α := by linarith
    rw [div_le_div_iff₀ hd (by norm_num)]
    nlinarith [exp_pos (8 * α - 2)]
  have T3 : g / 4 * (log 6 + r) / (1 / 2 - α) ≤
      1.781081 / 4 * (1.79176 + 0.024548 / (3 - 18 * 0.0024548)) / (1 / 2 - 0.0024548) := by
    have hd : 0 < 1 / 2 - α := by linarith
    have hr0 : 0 ≤ log 6 + r := by
      have : 0 ≤ r := Real.log_nonneg (by
        rw [le_div_iff₀ (by linarith)]; linarith)
      have : 0 ≤ log (6 : ℝ) := Real.log_nonneg (by norm_num)
      linarith
    rw [div_le_div_iff₀ hd (by norm_num)]
    have hg0 : 0 ≤ g := (exp_pos _).le
    have := mul_le_mul hg2 (add_le_add hl6 hlr) hr0 (by norm_num)
    nlinarith
  have T4 : (2 * g / (1 / 2 - α) + 3 * (1 / 8137) * 112) * cb ≤
      (2 * 1.781081 / (1 / 2 - 0.0024548) + 3 * (1 / 8137) * 112) * 0.363084 := by
    have hd : 0 < 1 / 2 - α := by linarith
    have h1 : 2 * g / (1 / 2 - α) ≤ 2 * 1.781081 / (1 / 2 - 0.0024548) := by
      rw [div_le_div_iff₀ hd (by norm_num)]; nlinarith [(exp_pos eulerMascheroniConstant)]
    have h2 : 0 ≤ 2 * g / (1 / 2 - α) + 3 * (1 / 8137) * 112 := by
      have : 0 ≤ 2 * g / (1 / 2 - α) := by have := exp_pos eulerMascheroniConstant; positivity
      linarith
    exact mul_le_mul (by linarith) (by norm_num at hc ⊢; linarith) (by linarith) (by norm_num)
  have T5 : log (8 / 3) * (1 / 8137) * 112 ≤ (0.98083 : ℝ) * (1 / 8137) * 112 := by
    nlinarith
  unfold K3
  have fin : (0.0015 : ℝ) < 8 * (2 * 1.78103 * 1.09204 / (4 - 8 * 0.0024547)
      - (1 / 8137) * 114 * 3 * 0.13803 / (4 - 8 * 0.0024548))
      - 1 / 2 * (8 * (1.781081 / 4 * (1.79176 + 0.024548 / (3 - 18 * 0.0024548)) / (1 / 2 - 0.0024548)
        + 0.98083 * (1 / 8137) * 112))
      - 1 / 2 * ((2 * 1.781081 / (1 / 2 - 0.0024548) + 3 * (1 / 8137) * 112) * 0.363084) := by
    norm_num
  linarith

end LeanLab.BS2022GRH
