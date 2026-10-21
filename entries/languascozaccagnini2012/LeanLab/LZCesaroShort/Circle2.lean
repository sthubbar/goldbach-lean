module

public import LeanLab.LZCesaroShort.Circle
public import LeanLab.LZCesaroShort.Lemma3Upper

/-!
# P0058 Lemma 6 at `y = H`, explicit: the term `I₂`

Lab proof, unit U-6105, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

* `W_hasSum`: `W(α) = 1/(1 − e^{−z}) = Σ_{m ≥ 0} e^{−m/N} e(mα)`;
* `conv_DW`: the convolution of `(Λ(m) − 1) e^{−m/N}` with `e^{−m/N}` at `n` is
  `e^{−n/N} (ψ(n) − n − 1)`;
* `I2_bound`: for `N ≥ 10^20` and `H < N`,
  `‖2∫ T(−α) R̃(α)/z dα − 2Σ t_H(n − N) e^{−n/N}(ψ(n) − n)‖ ≤ 2H²(8√(4N log N) + 8√(1 + N/2) + 1)`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher LeanLab.PNTPort.Selberg

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- `W(α) = 1/(1 − e^{−z})`. -/
noncomputable def Wz (N : ℕ) (α : ℝ) : ℂ := 1 / (1 - Complex.exp (-(zz N α)))

/-- Coefficients of `W`. -/
noncomputable def wc (N m : ℕ) : ℂ := ((Real.exp (-(m / N)) : ℝ) : ℂ)

/-- Coefficients of `D = S̃ − W`. -/
noncomputable def dc (N m : ℕ) : ℂ := ((Real.exp (-(m / N)) : ℝ) : ℂ) * lam1 m

lemma exp_pow_eq (N m : ℕ) : Real.exp (-(1 / (N : ℝ))) ^ m = Real.exp (-(m / N)) := by
  rw [← Real.exp_nat_mul]; congr 1; ring

lemma q_lt_one {N : ℕ} (hN : 1 ≤ N) : Real.exp (-(1 / (N : ℝ))) < 1 := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by
    have : 0 < 1 / (N : ℝ) := by positivity
    linarith)
  rwa [Real.exp_zero] at h

lemma summable_n_q {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-(1 / (N : ℝ))) ^ n) := by
  set q := Real.exp (-(1 / (N : ℝ)))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 := q_lt_one hN
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
    (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have h2 := summable_geometric_of_lt_one hq0.le hq1
  refine (h1.add h2).congr fun n => ?_
  simp only [pow_one]; ring

lemma summable_wc {N : ℕ} (hN : 1 ≤ N) : Summable (fun m => ‖wc N m‖) := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (summable_n_q hN)
  unfold wc
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← exp_pow_eq]
  have : (0 : ℝ) ≤ Real.exp (-(1 / (N : ℝ))) ^ m := by positivity
  nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]

lemma summable_dc {N : ℕ} (hN : 1 ≤ N) : Summable (fun m => ‖dc N m‖) := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (summable_n_q hN)
  unfold dc
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← exp_pow_eq,
    mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_lam1_le_succ m) (by positivity)

lemma W_eq {N : ℕ} (hN : 1 ≤ N) (α : ℝ) : Wz N α = ∑' m, wc N m * eL (m * α) := by
  set r : ℂ := ((Real.exp (-(1 / (N : ℝ))) : ℝ) : ℂ) * eL α with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact q_lt_one hN
  have h := hasSum_geometric_of_norm_lt_one hr1
  unfold Wz
  rw [cexp_neg_zz, ← hr, one_div, ← h.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [hr, mul_pow, ← Complex.ofReal_pow, exp_pow_eq, eL_nat_mul]
  rfl

lemma D_eq {N : ℕ} (hN : 1 ≤ N) (α : ℝ) : St N α - Wz N α = ∑' m, dc N m * eL (m * α) := by
  unfold Wz
  rw [← (hasSum_weighted hN α).tsum_eq]
  refine tsum_congr fun m => ?_
  unfold dc; ring

lemma sum_range_vonMangoldt (n : ℕ) : ∑ i ∈ range (n + 1), Λ i = ψ (n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]

lemma conv_DW (N n : ℕ) :
    ∑ p ∈ antidiagonal n, dc N p.1 * wc N p.2
      = ((Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1) : ℝ) : ℂ) := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hpt : ∀ k ∈ range (n + 1), dc N k * wc N (n - k)
      = ((Real.exp (-(n / N)) * (Λ k - 1) : ℝ) : ℂ) := by
    intro k hk
    rw [mem_range] at hk
    unfold dc wc lam1
    have : Real.exp (-(k / N)) * Real.exp (-(((n - k : ℕ) : ℝ) / N)) = Real.exp (-(n / N)) := by
      rw [← Real.exp_add]; congr 1; push_cast [Nat.cast_sub (by omega : k ≤ n)]; ring
    rw [← this]; push_cast; ring
  rw [sum_congr rfl hpt, ← Complex.ofReal_sum, ← mul_sum, sum_sub_distrib, sum_range_vonMangoldt]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  push_cast; ring

lemma continuous_Wz {N : ℕ} (hN : 1 ≤ N) : Continuous (Wz N) := by
  have : Wz N = fun α => ∑' m, wc N m * eL (m * α) := funext (W_eq hN)
  rw [this]; exact continuous_tsum_e _ (summable_wc hN)

/-- `∫ D W T(−α) = Σ t e^{−n/N}(ψ(n) − n − 1)`. -/
theorem DW_eq {N H : ℕ} (hN : 1 ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - Wz N α) * Wz N α
      = ∑ n ∈ Icc (N - H) (N + H),
          ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1)) : ℝ) : ℂ) := by
  have hd := summable_dc hN
  have hw := summable_wc hN
  have hpt : ∀ α, TH N H H (-α) * (St N α - Wz N α) * Wz N α = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, dc N m * eL (m * α)) * (∑' k, wc N k * eL (k * α))
        * eL (-(n * α))) := by
    intro α
    rw [TH_full, D_eq hN, W_eq hN, sum_mul, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, dc N m * eL (m * α)) * (∑' k, wc N k * eL (k * α))
        * eL (-(n * α)))
      = ∑ n ∈ Icc (N - H) (N + H), ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, dc N m * eL (m * α)) * (∑' k, wc N k * eL (k * α))
        * eL (-(n * α))) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      ((((continuous_tsum_e _ hd).mul (continuous_tsum_e _ hw)).mul
        (continuous_e.comp (continuous_const.mul continuous_id).neg)))).intervalIntegrable _ _
  rw [hsw]
  refine sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, coef_mul_tsum _ _ hd hw n, conv_DW]
  push_cast; ring

/-- `∫_{-1/2}^{1/2} ‖g‖ ≤ √B` when `∫ ‖g‖² ≤ B`. -/
lemma integral_norm_le_sqrt {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ} (hB0 : 0 < B)
    (hB : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2 ≤ B) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ≤ Real.sqrt B := by
  set s := Real.sqrt B with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hB0
  have hss : s * s = B := Real.mul_self_sqrt hB0.le
  have hpt : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖g α‖ ≤ (1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2 := by
    intro α _
    have h := sq_nonneg (‖g α‖ - s)
    rw [div_mul_eq_mul_div, one_mul, div_add_div _ _ (by positivity) (by norm_num),
      le_div_iff₀ (by positivity)]
    nlinarith
  have hc2 : Continuous (fun α => ‖g α‖ ^ 2) := hg.norm.pow 2
  have hc3 : Continuous (fun α => (1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2) :=
    (continuous_const.mul hc2).add continuous_const
  have hmono : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖
      ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ((1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2) :=
    intervalIntegral.integral_mono_on (by norm_num) (hg.norm.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _) hpt
  have hr : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ((1 / (2 * s)) * ‖g α‖ ^ 2 + s / 2)
      = (1 / (2 * s)) * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2) + s / 2 := by
    have i1 : IntervalIntegrable (fun α => (1 / (2 * s)) * ‖g α‖ ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul hc2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      smul_eq_mul]
    norm_num
  have : (1 / (2 * s)) * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2) ≤ (1 / (2 * s)) * B :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have e1 : (1 / (2 * s)) * B = s / 2 := by rw [← hss]; field_simp
  linarith

lemma tsum_exp_two_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' m : ℕ, ‖wc N m‖ ^ 2 ≤ 1 + N / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set q := Real.exp (-(1 / (N : ℝ)))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 := q_lt_one hN
  have hq21 : q ^ 2 < 1 := by nlinarith
  have heq : ∀ m, ‖wc N m‖ ^ 2 = (q ^ 2) ^ m := by
    intro m
    unfold wc
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← exp_pow_eq, ← pow_mul,
      ← pow_mul, mul_comm]
  simp_rw [heq]
  rw [tsum_geometric_of_lt_one (by positivity) hq21]
  have e : q ^ 2 = Real.exp (-(2 / N)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [← one_div, e]
  have := inv_one_sub_exp_neg_le (x := 2 / (N : ℝ)) (by positivity)
  rwa [one_div_div] at this

/-- **`I₂`, Lemma 6 at `y = H`, explicit.** -/
theorem I2_bound {N H : ℕ} (hN : (10 : ℝ) ^ 20 ≤ N) (hHN : H < N) :
    ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N) + 8 * Real.sqrt (1 + N / 2) + 1) := by
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set T : ℝ → ℂ := fun α => TH N H H (-α) with hT
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α with hRt
  set iz : ℝ → ℂ := fun α => 1 / zz N α with hiz
  have hTc : Continuous T := continuous_TH_neg N H
  have hStc : Continuous (St N) := continuous_St hNn
  have hizc : Continuous iz := continuous_const.div (continuous_zz N) (zz_ne_zero hNn)
  have hWc : Continuous (Wz N) := continuous_Wz hNn
  have hRtc : Continuous Rt := hStc.sub hizc
  -- the split
  have hsplit : ∀ α, T α * Rt α * iz α = T α * Rt α * (iz α - Wz N α)
      + T α * (Wz N α - iz α) * Wz N α + T α * (St N α - Wz N α) * Wz N α := by
    intro α; simp only [hRt, hiz]; ring
  have i1 : IntervalIntegrable (fun α => T α * Rt α * (iz α - Wz N α)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    ((hTc.mul hRtc).mul (hizc.sub hWc)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun α => T α * (Wz N α - iz α) * Wz N α) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    ((hTc.mul (hWc.sub hizc)).mul hWc).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun α => T α * (St N α - Wz N α) * Wz N α) volume
      (-(1 / 2 : ℝ)) (1 / 2) :=
    ((hTc.mul (hStc.sub hWc)).mul hWc).intervalIntegrable _ _
  have hint : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α
      = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
        + (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α := by
    simp_rw [hsplit]
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]
  have hDW := DW_eq (H := H) hNn
  -- pointwise bounds on `[-1/2, 1/2]`
  have hgeom : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖iz α - Wz N α‖ ≤ 8 := by
    intro α hα
    have hre : (zz N α).re = 1 / N := by simp [zz]
    have him : (zz N α).im = -(2 * Real.pi * α) := by simp [zz]
    have hb := geom_sub_inv_le (z := zz N α) (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          have : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
          nlinarith [Real.pi_pos])
    rw [norm_sub_rev]; exact hb
  have hTb : ∀ α, ‖T α‖ ≤ (H : ℝ) ^ 2 := fun α => norm_TH_le hHN.le _
  -- `∫ ‖Rt‖ ≤ √(4 N log N)`
  have hlog46 : (46 : ℝ) ≤ Real.log N := le_trans LeanLab.Zinoviev1997.log_1e20_ge
    (Real.log_le_log (by norm_num) hN)
  have hR2 : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖Rt α‖ ^ 2 ≤ 4 * N * Real.log N := by
    have := lemma3_upper N hN
    have : (N : ℝ) + 130 ≤ 2 * N * Real.log N := by nlinarith
    linarith
  have hR1 := integral_norm_le_sqrt hRtc (by positivity) hR2
  -- `∫ ‖W‖ ≤ √(1 + N/2)`
  have hW2 : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖Wz N α‖ ^ 2 ≤ 1 + N / 2 := by
    have : (fun α => ‖Wz N α‖ ^ 2) = fun α => ‖∑' m, wc N m * eL (m * α)‖ ^ 2 :=
      funext fun α => by rw [W_eq hNn]
    rw [this, parseval_tsum _ (summable_wc hNn)]
    exact tsum_exp_two_le hNn
  have hW1 := integral_norm_le_sqrt hWc (by positivity) hW2
  -- the three pieces
  have b1 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α)‖
      ≤ (H : ℝ) ^ 2 * 8 * Real.sqrt (4 * N * Real.log N) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
    have m1 : IntervalIntegrable (fun α => ‖T α * Rt α * (iz α - Wz N α)‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      ((hTc.mul hRtc).mul (hizc.sub hWc)).norm.intervalIntegrable _ _
    have m2 : IntervalIntegrable (fun α => ((H : ℝ) ^ 2 * 8) * ‖Rt α‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul hRtc.norm).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
      m1 m2
      (fun α hα => show ‖T α * Rt α * (iz α - Wz N α)‖ ≤ ((H : ℝ) ^ 2 * 8) * ‖Rt α‖ by
        rw [norm_mul, norm_mul]
        have := mul_le_mul (hTb α) (hgeom α hα) (norm_nonneg _) (by positivity)
        nlinarith [norm_nonneg (Rt α), norm_nonneg (T α), norm_nonneg (iz α - Wz N α)])
    rw [intervalIntegral.integral_const_mul] at hm
    have := mul_le_mul_of_nonneg_left hR1 (show (0 : ℝ) ≤ (H : ℝ) ^ 2 * 8 by positivity)
    linarith
  have b2 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α‖
      ≤ (H : ℝ) ^ 2 * 8 * Real.sqrt (1 + N / 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
    have m1 : IntervalIntegrable (fun α => ‖T α * (Wz N α - iz α) * Wz N α‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      ((hTc.mul (hWc.sub hizc)).mul hWc).norm.intervalIntegrable _ _
    have m2 : IntervalIntegrable (fun α => ((H : ℝ) ^ 2 * 8) * ‖Wz N α‖) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul hWc.norm).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
      m1 m2
      (fun α hα => show ‖T α * (Wz N α - iz α) * Wz N α‖ ≤ ((H : ℝ) ^ 2 * 8) * ‖Wz N α‖ by
        rw [norm_mul, norm_mul, norm_sub_rev]
        have := mul_le_mul (hTb α) (hgeom α hα) (norm_nonneg _) (by positivity)
        nlinarith [norm_nonneg (Wz N α), norm_nonneg (T α), norm_nonneg (iz α - Wz N α)])
    rw [intervalIntegral.integral_const_mul] at hm
    have := mul_le_mul_of_nonneg_left hW1 (show (0 : ℝ) ≤ (H : ℝ) ^ 2 * 8 by positivity)
    linarith
  have b3 : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - Wz N α) * Wz N α from rfl, hDW,
      ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_tw hHN.le]
    refine sum_le_sum fun n hn => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1))
        - tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) = -(tw N H n * Real.exp (-(n / N))) := by
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (tw_nonneg hHN.le hn) (Real.exp_pos _).le)]
    have : Real.exp (-(n / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0 : ℝ) ≤ n / N := by positivity
      linarith
    nlinarith [tw_nonneg hHN.le hn]
  -- assembly
  have hgoal : (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
      = 2 * ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
        + (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
        + ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
          - ∑ n ∈ Icc (N - H) (N + H),
            ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))) := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α from rfl, hint]
    ring
  rw [hgoal, norm_mul, Complex.norm_ofNat]
  have := norm_add₃_le (a := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
      (b := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
      (c := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
  nlinarith

end LeanLab.LZCesaroShort

