module

public import Mathlib
public import LeanLab.BS2022GRH.Constants

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T1803Z-10253, unit U-0964.
P0021 Bordignon, Starichkova 2022, arXiv 2211.08844 v1.

PROVED, no cited input:
* `qG_le_all`: q_G(X) ≤ 0.63995 for every X ≥ 4·10¹⁸, so Lemma 3's q_G(X₂) ≤ 0.640 holds on
  its whole stated range, X₂ ≥ 4·10¹⁸. MATCH.
* `pG_le_all`, `cG_le_all`: Lemmas 13 and 14, p_G(X₂) ≤ 0.429 and c_G(X₂) ≤ 0.429 for every
  X₂ ≥ 4·10¹⁸. MATCH.
* `cond18_full`: the rest of conditions (18), (21), (27) at the Section 5.4 parameters:
  √X/log^5 X ≥ 10⁹ for log X ≥ exp 15.85, u ≤ 10¹⁸, and 0 < α < 1/24, which gives
  α < 1/8 and α < 1/16 too. With `cond18` this is all of (18), (21), (27).
Method: with L = log X ≥ 42.83, X^{1/4} = e^{L/4} ≥ e^{L₀/4} L/L₀ for L₀ = 42.83, so
L/X^{1/4} ≤ L₀/e^{L₀/4}; log L ≤ L/10; the c/L^k terms decrease; the last term is ≤ 0.
Goldbach is open.
-/

@[expose] public section

open Real Finset

set_option exponentiation.threshold 2000

noncomputable section
namespace LeanLab.BS2022GRH

lemma exp_L0_ge : (44680 : ℝ) ≤ exp (42.83 / 4) := by
  have e : (42.83 / 4 : ℝ) = ((10 : ℕ) : ℝ) + 0.7075 := by norm_num
  rw [e, exp_add]
  have h2 : (2.0289 : ℝ) ≤ exp 0.7075 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.7075 : ℝ)) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc (44680 : ℝ) ≤ 2.7182818283 ^ 10 * 2.0289 := by norm_num
    _ ≤ exp ((10 : ℕ) : ℝ) * exp 0.7075 := by
        gcongr
        exact exp_nat_ge 10

/-- e^{L/4} ≥ e^{L₀/4} · L / L₀ for L ≥ L₀ = 42.83. -/
lemma expL4_ge {L : ℝ} (hL : 42.83 ≤ L) : exp (42.83 / 4) * (L / 42.83) ≤ exp (L / 4) := by
  have e : L / 4 = 42.83 / 4 + (L - 42.83) / 4 := by ring
  rw [e, exp_add]
  have h1 := Real.add_one_le_exp ((L - 42.83) / 4)
  have h2 : L / 42.83 ≤ (L - 42.83) / 4 + 1 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le

lemma logL_le {L : ℝ} (hL : 42.83 ≤ L) : log L ≤ L / 10 := by
  have h38 : log (42.83 : ℝ) ≤ 3.8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := (3.8 : ℝ)) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have h1 := Real.log_le_sub_one_of_pos (x := L / 42.83) (by positivity)
  rw [Real.log_div (by linarith) (by norm_num)] at h1
  have : L / 42.83 - 1 ≤ L / 10 - 3.8 := by
    rw [div_sub_one (by norm_num), div_sub' (by norm_num)]
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  linarith

/-- **Lemma 3, q_G(X) ≤ 0.640 on its whole range X ≥ 4·10¹⁸**, here with 0.63995. -/
theorem qG_le_all (X : ℝ) (hX : 4e18 ≤ X) : qG X ≤ 0.63995 := by
  have hX0 : 0 < X := by linarith
  have hL1 : 42.83 ≤ log X :=
    le_trans logX_bounds.1 (Real.log_le_log (by norm_num) hX)
  unfold qG
  set L := log X with hLdef
  have hLp : 0 < L := by linarith
  have hY : X ^ ((1 : ℝ) / 4) = exp (L / 4) := by
    rw [Real.rpow_def_of_pos hX0]; congr 1; rw [hLdef]; ring
  rw [hY]
  set Y := exp (L / 4)
  have hYp : 0 < Y := exp_pos _
  have hE := exp_L0_ge
  have hYge : 44680 * (L / 42.83) ≤ Y :=
    le_trans (mul_le_mul_of_nonneg_right hE (by positivity)) (expL4_ge hL1)
  have hY1 : (44680 : ℝ) ≤ Y := by
    have : (1 : ℝ) ≤ L / 42.83 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hLY : L / Y ≤ 42.83 / 44680 := by
    have h := hYge
    rw [mul_div_assoc', div_le_iff₀ (by norm_num)] at h
    rw [div_le_div_iff₀ hYp (by norm_num)]; linarith
  have hl0 : 0 ≤ log L := Real.log_nonneg (by linarith)
  have hl := logL_le hL1
  have t1 : 12.683 / L ≤ 12.683 / 42.83 := by gcongr
  have t2 : 254.980 / L ^ 2 ≤ 254.980 / (42.83 : ℝ) ^ 2 := by gcongr
  have t3 : 2607.854 / L ^ 3 ≤ 2607.854 / (42.83 : ℝ) ^ 3 := by gcongr
  have t4 : 11605.056 / L ^ 4 ≤ 11605.056 / (42.83 : ℝ) ^ 4 := by gcongr
  have t5 : 1.314 * L / Y ≤ 1.314 * (42.83 / 44680) := by
    rw [mul_div_assoc]; gcongr
  have t6 : 0.092 * log L / Y ≤ 0.0092 * (42.83 / 44680) := by
    calc 0.092 * log L / Y ≤ 0.092 * (L / 10) / Y := by gcongr
      _ = 0.0092 * (L / Y) := by ring
      _ ≤ 0.0092 * (42.83 / 44680) := by gcongr
  have t7 : 60.883 / Y ≤ 60.883 / 44680 := by gcongr
  have t8 : 8.250 * log L / (Y * L) ≤ 0.825 / 44680 := by
    calc 8.250 * log L / (Y * L) ≤ 8.250 * (L / 10) / (Y * L) := by gcongr
      _ = 0.825 / Y := by field_simp; ring
      _ ≤ 0.825 / 44680 := by gcongr
  have t9 : 939.260 / (Y * L) ≤ 939.260 / (44680 * 42.83) := by gcongr
  have t10 : 0 ≤ 237.934 / (sqrt X * L) := by positivity
  have : (0.165 : ℝ) + 12.683 / 42.83 + 254.980 / 42.83 ^ 2 + 2607.854 / 42.83 ^ 3 +
      11605.056 / 42.83 ^ 4 + 1.314 * (42.83 / 44680) + 0.0092 * (42.83 / 44680) + 60.883 / 44680 +
      0.825 / 44680 + 939.260 / (44680 * 42.83) ≤ 0.63995 := by norm_num
  linarith

theorem pG_le_all (X : ℝ) (hX : 4e18 ≤ X) : pG X ≤ 0.429 := by
  unfold pG; linarith [qG_le_all X hX]

theorem cG_le_all (X : ℝ) (hX : 4e18 ≤ X) : cG X ≤ 0.429 := by
  unfold cG pG
  have hq := qG_le_all X hX
  have hs : (2e9 : ℝ) ≤ sqrt X := by rw [← sqrtX]; exact Real.sqrt_le_sqrt hX
  have hL1 : 42.83 ≤ log X := le_trans logX_bounds.1 (Real.log_le_log (by norm_num) hX)
  have hll : (1 : ℝ) ≤ log (log X) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  have : 0.9 / (sqrt X * log (log X)) ≤ 0.9 / (2e9 * 1) := by gcongr
  have : (0.65 : ℝ) * (0.02 + 0.63995) + 0.9 / (2e9 * 1) ≤ 0.429 := by norm_num
  nlinarith

/-- **The rest of conditions (18), (21), (27)** at the Section 5.4 parameters, A = 4. -/
theorem cond18_full :
    (∀ L : ℝ, exp 15.85 ≤ L → (1e9 : ℝ) ≤ exp (L / 2) / L ^ 5) ∧ u0 ≤ 1e18 ∧
      0 < α0 ∧ α0 < 1 / 24 := by
  refine ⟨?_, by linarith [u_le], α0_pos, by linarith [alpha_le]⟩
  intro L hL
  have h0 : (7640000 : ℝ) ≤ L := le_trans exp1585_ge hL
  have hLp : 0 < L := by linarith
  have h := Real.pow_div_factorial_le_exp (x := L / 2) (by positivity) 10
  rw [le_div_iff₀ (by positivity)]
  have e : (L / 2) ^ 10 / (Nat.factorial 10 : ℝ) = L ^ 5 * (L ^ 5 / (1024 * 3628800)) := by
    simp [Nat.factorial]; ring
  rw [e] at h
  have h5 : (7640000 : ℝ) ^ 5 ≤ L ^ 5 := by gcongr
  have : (1e9 : ℝ) ≤ L ^ 5 / (1024 * 3628800) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hL5 : 0 ≤ L ^ 5 := by positivity
  nlinarith

end LeanLab.BS2022GRH
