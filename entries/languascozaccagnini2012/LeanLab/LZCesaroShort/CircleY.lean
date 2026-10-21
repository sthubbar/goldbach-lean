module

public import LeanLab.LZCesaroShort.Circle2

/-!
# P0058 Section 4 for every `y ∈ [-H, H]`: the circle identity, `I₁` and `I₂`

Lab proof, unit U-6109, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN. The files `Circle.lean` and `Circle2.lean` treat `y = H`; here the same
statements hold for the partial sums over `F_y = {n : N − H ≤ n ≤ N + H, n ≤ N + y}`, with the
same proofs and the bound `Σ_{F_y} t_H ≤ H²`. Needed for Theorem 2 eq. (2).
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher LeanLab.PNTPort.Selberg

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- The summation range of `T_H(N, y; ·)`. -/
noncomputable def Fy (N H : ℕ) (y : ℝ) : Finset ℕ :=
  (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + y)

lemma TH_eqY (N H : ℕ) (y α : ℝ) :
    TH N H y α = ∑ n ∈ Fy N H y, ((tw N H n : ℝ) : ℂ) * eL (n * α) := rfl

lemma tw_nonnegY {N H n : ℕ} {y : ℝ} (hHN : H ≤ N) (hn : n ∈ Fy N H y) : 0 ≤ tw N H n :=
  tw_nonneg hHN (mem_filter.mp hn).1

lemma sum_twY_le {N H : ℕ} {y : ℝ} (hHN : H ≤ N) : ∑ n ∈ Fy N H y, tw N H n ≤ (H : ℝ) ^ 2 := by
  rw [← sum_tw hHN]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => tw_nonneg hHN hn

lemma norm_THY_le {N H : ℕ} {y : ℝ} (hHN : H ≤ N) (α : ℝ) : ‖TH N H y α‖ ≤ (H : ℝ) ^ 2 := by
  rw [TH_eqY]
  refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) (sum_twY_le (y := y) hHN))
  refine sum_congr rfl fun n hn => ?_
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tw_nonnegY hHN hn)]

lemma continuous_THY_neg (N H : ℕ) (y : ℝ) : Continuous (fun α => TH N H y (-α)) := by
  simp_rw [TH_eqY]
  exact continuous_finsetSum _ fun n _ => continuous_const.mul
    ((continuous_e_mul _).comp continuous_neg)

/-- **The circle method identity**, eq. (26) at `y = H`. -/
theorem Q_eqY {N H : ℕ} {y : ℝ} (hN : 1 ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), St N α ^ 2 * TH N H y (-α)
      = ∑ n ∈ Fy N H y, ((tw N H n * Real.exp (-n / N) * R n : ℝ) : ℂ) := by
  have hc := summable_cS hN
  have hpt : ∀ α, St N α ^ 2 * TH N H y (-α) = ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * ((∑' m, cS N m * eL (m * α)) * (∑' k, cS N k * eL (k * α))
        * eL (-(n * α))) := by
    intro α
    rw [TH_eqY, mul_sum, St_eq]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * ((∑' m, cS N m * eL (m * α)) * (∑' k, cS N k * eL (k * α))
        * eL (-(n * α)))
      = ∑ n ∈ Fy N H y, ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, cS N m * eL (m * α)) * (∑' k, cS N k * eL (k * α))
        * eL (-(n * α))) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      ((((continuous_tsum_e _ hc).mul (continuous_tsum_e _ hc)).mul
        (continuous_e.comp (continuous_const.mul continuous_id).neg)))).intervalIntegrable _ _
  rw [hsw]
  refine sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, coef_mul_tsum _ _ hc hc n, conv_cS]
  push_cast; ring

/-- **`I₁`**, from Lemma 2. -/
theorem I1_boundY {N H : ℕ} {y : ℝ} (hN : 1 ≤ N) (hHN : H < N) :
    ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (1 / zz N α) ^ 2)
      - ∑ n ∈ Fy N H y, ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ α, TH N H y (-α) * (1 / zz N α) ^ 2 = ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2) := by
    intro α; rw [TH_eqY, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  have hcz : Continuous (fun α => (1 / zz N α) ^ 2) :=
    (continuous_const.div (continuous_zz N) (zz_ne_zero hN)).pow 2
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2)
      = ∑ n ∈ Fy N H y, ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      (((continuous_e.comp (continuous_const.mul continuous_id).neg)).mul hcz)).intervalIntegrable _ _
  rw [hsw, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (sum_twY_le (y := y) hHN.le)
  refine sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := by have hn' := (mem_filter.mp hn).1; rw [mem_Icc] at hn'; omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [intervalIntegral.integral_const_mul]
  have hI : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), eL (-(n * α)) * (1 / zz N α) ^ 2
      = ∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc fun α _ => ?_
    rw [e_neg_eq, zz_eq, one_div_pow]
  have h2' := lemma2 hN0 hnr
  rw [hI]
  have e1 : ((tw N H n : ℝ) : ℂ) * (∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
      - ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)
      = ((tw N H n : ℝ) : ℂ) * ((∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
        - ((n * Real.exp (-n / N) : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tw_nonnegY hHN.le hn)]
  have hpi : 1 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  calc tw N H n * ‖_‖ ≤ tw N H n * (1 / Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left h2' (tw_nonnegY hHN.le hn)
    _ ≤ tw N H n * 1 := mul_le_mul_of_nonneg_left hpi (tw_nonnegY hHN.le hn)
    _ = tw N H n := mul_one _

/-- `∫ D W T(−α) = Σ t e^{−n/N}(ψ(n) − n − 1)`. -/
theorem DW_eqY {N H : ℕ} {y : ℝ} (hN : 1 ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - Wz N α) * Wz N α
      = ∑ n ∈ Fy N H y,
          ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1)) : ℝ) : ℂ) := by
  have hd := summable_dc hN
  have hw := summable_wc hN
  have hpt : ∀ α, TH N H y (-α) * (St N α - Wz N α) * Wz N α = ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * ((∑' m, dc N m * eL (m * α)) * (∑' k, wc N k * eL (k * α))
        * eL (-(n * α))) := by
    intro α
    rw [TH_eqY, D_eq hN, W_eq hN, sum_mul, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * ((∑' m, dc N m * eL (m * α)) * (∑' k, wc N k * eL (k * α))
        * eL (-(n * α)))
      = ∑ n ∈ Fy N H y, ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, dc N m * eL (m * α)) * (∑' k, wc N k * eL (k * α))
        * eL (-(n * α))) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      ((((continuous_tsum_e _ hd).mul (continuous_tsum_e _ hw)).mul
        (continuous_e.comp (continuous_const.mul continuous_id).neg)))).intervalIntegrable _ _
  rw [hsw]
  refine sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, coef_mul_tsum _ _ hd hw n, conv_DW]
  push_cast; ring

/-- **`I₂`, Lemma 6 at `y = H`, explicit.** -/
theorem I2_boundY {N H : ℕ} {y : ℝ} (hN : (10 : ℝ) ^ 20 ≤ N) (hHN : H < N) :
    ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N) + 8 * Real.sqrt (1 + N / 2) + 1) := by
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set T : ℝ → ℂ := fun α => TH N H y (-α) with hT
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α with hRt
  set iz : ℝ → ℂ := fun α => 1 / zz N α with hiz
  have hTc : Continuous T := continuous_THY_neg N H y
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
  have hDW := DW_eqY (H := H) (y := y) hNn
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
  have hTb : ∀ α, ‖T α‖ ≤ (H : ℝ) ^ 2 := fun α => norm_THY_le hHN.le _
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
      - ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - Wz N α) * Wz N α from rfl, hDW,
      ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (sum_twY_le (y := y) hHN.le)
    refine sum_le_sum fun n hn => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n - 1))
        - tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) = -(tw N H n * Real.exp (-(n / N))) := by
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (tw_nonnegY hHN.le hn) (Real.exp_pos _).le)]
    have : Real.exp (-(n / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0 : ℝ) ≤ n / N := by positivity
      linarith
    nlinarith [tw_nonnegY hHN.le hn]
  -- assembly
  have hgoal : (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      - 2 * ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
      = 2 * ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
        + (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
        + ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
          - ∑ n ∈ Fy N H y,
            ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))) := by
    rw [show (∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) * (1 / zz N α))
      = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α from rfl, hint]
    ring
  rw [hgoal, norm_mul, Complex.norm_ofNat]
  have := norm_add₃_le (a := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * (iz α - Wz N α))
      (b := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (Wz N α - iz α) * Wz N α)
      (c := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * (St N α - Wz N α) * Wz N α)
      - ∑ n ∈ Fy N H y, ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ))
  nlinarith

end LeanLab.LZCesaroShort

