module

public import Mathlib

/-!
# `‖ζ'/ζ(2)‖ ≤ 0.97`

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6551. AI wrote this file. Known mathematics, no
cited input. `-ζ'/ζ(2) = Σ Λ(n)/n²` by Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
`Λ(n) ≤ log n`, the terms `n ≤ 8` summed with `log 2 < 0.6931471808`, `log(3/2) ≤ 1/2`,
`log(5/4) ≤ 1/4`, `log(7/8) ≤ -1/8`, and the tail by the telescoping bound
`log n/n² ≤ g(n - 1) - g(n)`, `g(a) = (log a + 1)/a`, for `n ≥ 4`. The true value is `0.5700`;
`Σ_{n≥2} log n/n² = 0.9375`; this file proves `≤ 0.97`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real

/-- `g(a) = (log a + 1)/a`. -/
noncomputable def gt (a : ℝ) : ℝ := (Real.log a + 1) / a

lemma gt_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ gt a := by
  unfold gt; have := Real.log_nonneg ha; positivity

lemma log_four_gt : (4 : ℝ) / 3 ≤ Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_gt_d9; push_cast; linarith

/-- **The telescoping step**: `log a/a² ≤ g(a - 1) - g(a)` for `a ≥ 4`. -/
lemma tele_step {a : ℝ} (ha : 4 ≤ a) : Real.log a / a ^ 2 ≤ gt (a - 1) - gt a := by
  have ha1 : 0 < a - 1 := by linarith
  have ha0 : 0 < a := by linarith
  set L := Real.log a with hLdef
  have hL : a ≤ L * (a - 1) := by
    have h1 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) ha
    have h2 := log_four_gt
    nlinarith
  have hlog1 : L - 1 / (a - 1) ≤ Real.log (a - 1) := by
    have := Real.log_le_sub_one_of_pos (show 0 < a / (a - 1) by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at this
    have e : a / (a - 1) - 1 = 1 / (a - 1) := by field_simp; ring
    linarith
  unfold gt
  have step1 : (L - 1 / (a - 1) + 1) / (a - 1) ≤ (Real.log (a - 1) + 1) / (a - 1) := by
    apply div_le_div_of_nonneg_right _ ha1.le; linarith
  have key : (L - 1 / (a - 1) + 1) / (a - 1) - (L + 1) / a - L / a ^ 2 =
      (L * (a - 1) - a) / (a ^ 2 * (a - 1) ^ 2) := by
    field_simp; ring
  have hpos : 0 ≤ (L * (a - 1) - a) / (a ^ 2 * (a - 1) ^ 2) := by
    apply div_nonneg (by linarith); positivity
  linarith

/-- `f(n) = log n/n²`. -/
noncomputable def fl (n : ℕ) : ℝ := Real.log n / (n : ℝ) ^ 2

lemma fl_nonneg (n : ℕ) : 0 ≤ fl n := by
  unfold fl
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    have := Real.log_nonneg this; positivity

/-- The terms `n ≤ 8`. -/
lemma sum_nine_le : ∑ n ∈ Finset.range 9, fl n + gt 8 ≤ 0.97 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fl, gt]
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  have l3 : Real.log 3 ≤ Real.log 2 + 1 / 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at this; linarith
  have l5 : Real.log 5 ≤ 2 * Real.log 2 + 1 / 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this; push_cast at this; linarith
  have l7 : Real.log 7 ≤ 3 * Real.log 2 - 1 / 8 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this; push_cast at this; linarith
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  push_cast
  simp only [Real.log_zero, Real.log_one, zero_div]
  rw [l4, l6, l8]
  norm_num
  linarith

/-- The partial sums with the telescoped tail. -/
lemma sum_range_fl_le_aux (M : ℕ) (hM : 9 ≤ M) :
    ∑ n ∈ Finset.range M, fl n ≤ ∑ n ∈ Finset.range 9, fl n + gt 8 - gt ((M : ℝ) - 1) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_range_succ]
    have hM4 : (4 : ℝ) ≤ M := by
      have : (9 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have := tele_step hM4
    have e : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
    rw [e]
    have h2 : fl M ≤ gt ((M : ℝ) - 1) - gt M := this
    linarith

lemma sum_range_fl_le (M : ℕ) : ∑ n ∈ Finset.range M, fl n ≤ 0.97 := by
  rcases le_or_gt 9 M with hM | hM
  · have h1 := sum_range_fl_le_aux M hM
    have h2 : 0 ≤ gt ((M : ℝ) - 1) := gt_nonneg (by
      have : (9 : ℝ) ≤ M := by exact_mod_cast hM
      linarith)
    linarith [sum_nine_le]
  · have : ∑ n ∈ Finset.range M, fl n ≤ ∑ n ∈ Finset.range 9, fl n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hM.le)
        (fun n _ _ => fl_nonneg n)
    linarith [sum_nine_le, gt_nonneg (show (1 : ℝ) ≤ 8 by norm_num)]

lemma summable_fl : Summable fl :=
  summable_of_sum_range_le fl_nonneg sum_range_fl_le

/-- **`‖ζ'/ζ(2)‖ ≤ 0.97`**. -/
theorem norm_logDeriv_zeta_two_le :
    ‖deriv riemannZeta 2 / riemannZeta 2‖ ≤ 0.97 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have e : deriv riemannZeta 2 / riemannZeta 2 = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 := by
    rw [hL]; ring
  rw [e, norm_neg]
  have hb : ∀ n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ ≤ fl n := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · exact fl_nonneg n
    · unfold fl
      have hre : (2 : ℂ).re = 2 := by norm_num
      rw [hre, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        show ((n : ℝ) ^ (2 : ℝ)) = (n : ℝ) ^ 2 by norm_cast]
      gcongr
      exact ArithmeticFunction.vonMangoldt_le_log
  have hsum : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb summable_fl
  calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2‖
      ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, fl n := hsum.tsum_le_tsum hb summable_fl
    _ ≤ 0.97 := tsum_le_of_sum_range_le fl_nonneg sum_range_fl_le

end LeanLab.PNTPort.ExplicitPsi1.Trivial
