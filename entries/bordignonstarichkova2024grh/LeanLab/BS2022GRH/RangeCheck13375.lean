module

public import LeanLab.BS2022GRH.JournalPositive

/-!
P0021, T2 FRONTIER, I-0088 second-run VERIFY of U-1193, unit U-1227, PC run 20261020T1303Z-22201.

The question U-1193 left: does any hypothesis of the journal's Theorems 5 to 7 or Lemmas 7, 8,
9, 11, 12, 13, 14 have a range that holds at log log X₂ = 13.45 but fails at 13.375? Read on the
page images of copies/P0021-journal.pdf, Ramanujan J. 64 (2024), pp. 1216 to 1241. Every range
there is either a fixed threshold, met with room at 13.375, or one of the parameter displays
(19), (21), (25), which `JournalPositive.conditions_13375` already checks. This file proves the
fixed-threshold and implied-range steps at 13.375 in Lean:

* `lemma7_range`: Lemma 7 needs z > exp 2753 with z = N^{1/8}; log z = log N / 8 ≥ e^{13.375}/8.
* `display25_first`: (25) first condition, log X₂ ≥ max((A + 1)/α₃, 48(A + 4/3)) at A = 10.
* `display25_third`: (25) third condition, X₂^{1/48}/log^{A+4/3} X₂ ≥ 0.44, in log form.
* `remark1_H`: Remark 1, p. 1230, H = √N/log^{A+1} N ≥ 10⁸ follows from (19): if
  N^α/log^{A+1} N ≥ e^u with α ≤ 1/2, u ≥ 400 and N ≥ 1, then √N/log^{A+1} N ≥ 10⁸.
  The same step gives D* ≥ 10⁸ for Mϕ(D*) ≤ Mϕ(10⁸) on p. 1240.
* `mono_step`: the proof of Theorem 5, p. 1229, uses N^α/log^{A+1} N ≥ X₂^α/log^{A+1} X₂ for
  N ≥ X₂; in log form α t − (A + 1) log t is nondecreasing for t ≥ (A + 1)/α, which the first
  condition of (19) supplies.
* `sieve_ranges_13375`: s = 4 − 8α₁ ∈ [3, 4] for f(s), p. 1229, and k_{α₂} = 8(1/6 − α₂) > 1,
  p. 1231, at α = 0.00256.

Lemma 11 needs N ≥ exp(exp 10), Lemmas 12 and 13 need X₂ ≥ 4·10¹⁸, Lemma 14 needs y ≥ 2657,
the proof of Theorem 6 needs y ≥ 286; all hold since log log X₂ = 13.375 > 10. None depends on
13.45. Plain math only, the cited theorems stay cited; the result they feed is CONDITIONAL ON
GRH and the journal's Theorems 5 to 7 and Lemma 9.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Journal
open Real

/-- Lemma 7 range: with log N ≥ e^{13.375}, log z = log N / 8 > 2753. -/
theorem lemma7_range {logN : ℝ} (h : exp 13.375 ≤ logN) : (2753 : ℝ) < logN / 8 := by
  have := exp13375_ge
  linarith

/-- (25) first condition at A = 10, α₃ = 0.00256. -/
theorem display25_first :
    max ((10 + 1) / (0.00256 : ℝ)) (48 * (10 + 4 / 3)) ≤ exp 13.375 := by
  have := exp13375_ge
  apply max_le <;> norm_num <;> linarith

/-- (25) third condition in log form: L/48 − (A + 4/3) log L ≥ log 0.44 at L = e^{13.375},
log L = 13.375, A = 10. -/
theorem display25_third :
    Real.log 0.44 ≤ exp 13.375 / 48 - (10 + 4 / 3) * 13.375 := by
  have := exp13375_ge
  have hl : Real.log 0.44 < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-- `10⁸ ≤ e^{400}`. -/
lemma e400_ge : (10 : ℝ) ^ 8 ≤ exp 400 := by
  have h := Real.add_one_le_exp (400 : ℝ)
  have h2 : (10 : ℝ) ^ 8 ≤ exp 20 := by
    have h1 := Real.exp_one_gt_d9
    have e : exp (20 : ℝ) = exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 8 ≤ 2.7 ^ 20 := by norm_num
      _ ≤ exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) (by linarith) 20
  calc (10 : ℝ) ^ 8 ≤ exp 20 := h2
    _ ≤ exp 400 := Real.exp_le_exp.mpr (by norm_num)

/-- Remark 1: from (19) in the form N^α / ℓ ≥ e^u, with ℓ = log^{A+1} N > 0, α ≤ 1/2,
u ≥ 400 and N ≥ 1, the sieve level H = √N / ℓ is at least 10⁸. -/
theorem remark1_H {N α ℓ u : ℝ} (hN : 1 ≤ N) (hα : α ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hu : 400 ≤ u) (h19 : exp u ≤ N ^ α / ℓ) :
    (10 : ℝ) ^ 8 ≤ Real.sqrt N / ℓ := by
  have hs : N ^ α ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN hα
  have h1 : N ^ α / ℓ ≤ Real.sqrt N / ℓ := div_le_div_of_nonneg_right hs hℓ.le
  have h2 : exp 400 ≤ exp u := Real.exp_le_exp.mpr hu
  linarith [e400_ge]

/-- Vacuity for `remark1_H`: N = e^{2000}, α = 1/2, ℓ = 1, u = 400 meet its hypotheses. -/
theorem remark1_H_vacuity :
    exp 400 ≤ (exp 2000) ^ (1 / 2 : ℝ) / 1 := by
  rw [div_one, ← Real.exp_mul]; exact Real.exp_le_exp.mpr (by norm_num)

/-- The monotonicity step of Theorem 5's proof, in log form: for (A + 1)/α ≤ t₁ ≤ t₂, with
B = A + 1 > 0, α t₁ − B log t₁ ≤ α t₂ − B log t₂. With t = log N this is
N^α/log^{A+1} N ≥ X₂^α/log^{A+1} X₂ for N ≥ X₂. -/
theorem mono_step {α B t₁ t₂ : ℝ} (hα : 0 < α) (hB : 0 < B) (h1 : B / α ≤ t₁)
    (h12 : t₁ ≤ t₂) :
    α * t₁ - B * Real.log t₁ ≤ α * t₂ - B * Real.log t₂ := by
  have ht1 : 0 < t₁ := lt_of_lt_of_le (div_pos hB hα) h1
  have ht2 : 0 < t₂ := by linarith
  have hlog : Real.log t₂ - Real.log t₁ ≤ (t₂ - t₁) / t₁ := by
    rw [← Real.log_div ht2.ne' ht1.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ht2 ht1)
    have e : t₂ / t₁ - 1 = (t₂ - t₁) / t₁ := by field_simp
    linarith
  have hBt : B / t₁ ≤ α := by
    rw [div_le_iff₀ ht1]; rw [div_le_iff₀ hα] at h1; linarith
  have key : B * ((t₂ - t₁) / t₁) ≤ α * (t₂ - t₁) := by
    have e : B * ((t₂ - t₁) / t₁) = (B / t₁) * (t₂ - t₁) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hBt (by linarith)
  have := mul_le_mul_of_nonneg_left hlog hB.le
  nlinarith

/-- The first condition of (19) at the new parameters puts t = log X₂ in `mono_step`'s range:
(A + 1)/α = 11/0.00256 ≤ e^{13.375}. -/
theorem mono_range_13375 : (11 : ℝ) / 0.00256 ≤ exp 13.375 :=
  (conditions_13375).2

/-- The linear sieve ranges at α = 0.00256: s = 4 − 8α₁ ∈ [3, 4] and k_{α₂} = 8(1/6 − α₂) > 1. -/
theorem sieve_ranges_13375 :
    (3 : ℝ) ≤ 4 - 8 * 0.00256 ∧ 4 - 8 * (0.00256 : ℝ) ≤ 4 ∧ (1 : ℝ) < 8 * (1 / 6 - 0.00256) := by
  norm_num


end LeanLab.BS2022GRH.Journal
