module

public import LeanLab.PNTPort.Selberg.LZLemma1Range
public import LeanLab.PNTPort.Selberg.GallagherEdge
public import LeanLab.PNTPort.Selberg.CramerWeighted

/-!
# P0058 Lemma 1 for `ξ ≤ 1/N`, from RH by Cramér

Lab proof, unit U-6200, CLOUD 20261020T0817Z-cloud38, T2 toward P0058 Lemma 1. AI wrote this
file. CONDITIONAL ON RiemannHypothesis only, through `cramer_weighted`.

* `abel_c`: `∑_{n<M} a_n c_n = ∑_{n<M} (c_n - c_{n+1}) A_{n+1} + c_M A_M`, `A_k = ∑_{i<k} a_i`;
* `weighted_Gp_sq`: under RH, `∑_{n<M} e^{-n/N} ‖Gp n‖² ≤ K N²`, with `Gp n = ψ(n) - n - 1`;
* `tiny_pointwise`: under RH, `‖S̃(α) - 1/(1 - e^{-z})‖ ≤ C √N (1 + N |α|)` for every real `α`;
* `lz_lemma1_tiny`: under RH, `∫_{-ξ}^{ξ} ‖S̃(α) - 1/z‖² dα ≤ C N ξ` for `0 ≤ ξ ≤ min(1/N, 1/2)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PNTPort.Gallagher

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- Abel summation with complex weights. -/
lemma abel_c (a c : ℕ → ℂ) (M : ℕ) :
    ∑ n ∈ range M, a n * c n
      = ∑ n ∈ range M, (c n - c (n + 1)) * ∑ i ∈ range (n + 1), a i
        + c M * ∑ i ∈ range M, a i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun n => (c n - c (n + 1)) * ∑ i ∈ range (n + 1), a i),
      sum_range_succ a M]
    ring

/-- Cramér for `Gp`, with the exponential weight. -/
lemma weighted_Gp_sq (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ,
      ∑ n ∈ range M, Real.exp (-(1 / (N : ℝ))) ^ n * ‖Gp n‖ ^ 2 ≤ K * (N : ℝ) ^ 2 := by
  obtain ⟨Kw, hKw0, hKw⟩ := cramer_weighted hRH
  refine ⟨2 * Kw + 4, by positivity, fun N hN M => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have h1q : 0 < 1 - q := by linarith
  have hw : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  have h1 : ∑ n ∈ range M, q ^ n * ‖Gp n‖ ^ 2 ≤
      ∑ n ∈ range M, (2 * ((Chebyshev.psi n - n) ^ 2 * Real.exp (-(n / N))) + 2 * q ^ n) := by
    refine sum_le_sum fun n _ => ?_
    rw [hw n]
    have := norm_Gp_sq_le n
    nlinarith [pow_pos hq0 n]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h1
  have h2 := hKw N hN M
  have h3 : ∑ n ∈ range M, q ^ n ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ h1q, mul_comm, mul_neg_geom_sum]
    have : 0 ≤ q ^ M := by positivity
    linarith
  have hD : 1 / (1 - q) ≤ 2 * N := one_sub_exp_neg_inv hN1
  nlinarith

/-- `‖1 - q e(α)‖ ≤ (1 - q) + 2π|α|` for `0 ≤ q ≤ 1`. -/
lemma norm_one_sub_qe {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (α : ℝ) :
    ‖1 - (q : ℂ) * eL α‖ ≤ (1 - q) + 2 * Real.pi * |α| := by
  have e : 1 - (q : ℂ) * eL α = ((1 - q : ℝ) : ℂ) - (q : ℂ) * (eL α - 1) := by push_cast; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hq0, norm_e_sub_one]
  have hs : |Real.sin (Real.pi * α)| ≤ |Real.pi * α| := Real.abs_sin_le_abs
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have : q * (2 * |Real.sin (Real.pi * α)|) ≤ 2 * Real.pi * |α| := by
    have h0 : 0 ≤ 2 * |Real.sin (Real.pi * α)| := by positivity
    nlinarith [abs_nonneg α, Real.pi_pos]
  linarith

set_option maxHeartbeats 2000000 in
/-- **The pointwise bound near `0`, under RH.** -/
theorem tiny_pointwise (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
      ‖LeanLab.LZCesaroShort.St N α - 1 / (1 - Complex.exp (-(LeanLab.LZCesaroShort.zz N α)))‖
        ≤ C * Real.sqrt N * (1 + N * |α|) := by
  obtain ⟨K, hK0, hK⟩ := weighted_Gp_sq hRH
  refine ⟨7 * (K + 3), by positivity, fun N hN α => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have h1q : 0 < 1 - q := by linarith
  have h1qN : 1 - q ≤ 1 / N := by
    have := Real.add_one_le_exp (-(1 / (N : ℝ)))
    rw [hq]; linarith
  have hD : 1 / (1 - q) ≤ 2 * N := one_sub_exp_neg_inv hN1
  have hpow : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  set w : ℂ := (q : ℂ) * eL α with hwdef
  have hwn : ‖w‖ = q := by
    rw [hwdef, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hq0]
  set sN := Real.sqrt N with hsN
  have hsN0 : 0 < sN := Real.sqrt_pos.mpr hN0
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt hN0.le
  -- the bound `B` for every partial sum, up to `q^M M²`
  set B := ‖1 - w‖ * ((K + 2) * N * sN) with hB
  have hpart : ∀ M : ℕ, ‖∑ n ∈ range M, (Real.exp (-(n / N)) : ℂ) * (lam1 n * eL (n * α))‖
      ≤ B + q ^ M * (M : ℝ) ^ 2 := by
    intro M
    have hre : ∑ n ∈ range M, (Real.exp (-(n / N)) : ℂ) * (lam1 n * eL (n * α))
        = ∑ n ∈ range M, lam1 n * w ^ n := by
      refine sum_congr rfl fun n _ => ?_
      rw [hpow, eL_nat_mul, hwdef, mul_pow]; push_cast; ring
    rw [hre, abel_c lam1 (fun n => w ^ n) M]
    have hc : ∀ n : ℕ, w ^ n - w ^ (n + 1) = (1 - w) * w ^ n := fun n => by ring
    simp_rw [hc]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · -- the main sum
      have h1 : ‖∑ n ∈ range M, (1 - w) * w ^ n * ∑ i ∈ range (n + 1), lam1 i‖ ≤
          ‖1 - w‖ * ∑ n ∈ range M, q ^ n * ‖Gp n‖ := by
        rw [mul_sum]
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
        rw [norm_mul, norm_mul, norm_pow, hwn, mul_assoc]
        rfl
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have hamgm : ∀ n : ℕ, q ^ n * ‖Gp n‖ ≤ (N * q ^ n + q ^ n * ‖Gp n‖ ^ 2) / (2 * sN) := by
        intro n
        rw [le_div_iff₀ (by positivity)]
        have : 0 ≤ q ^ n * (‖Gp n‖ - sN) ^ 2 := by positivity
        nlinarith [pow_pos hq0 n]
      refine (sum_le_sum fun n _ => hamgm n).trans ?_
      rw [← sum_div, sum_add_distrib, ← mul_sum]
      have h3 : ∑ n ∈ range M, q ^ n ≤ 1 / (1 - q) := by
        rw [le_div_iff₀ h1q, mul_comm, mul_neg_geom_sum]
        have : 0 ≤ q ^ M := by positivity
        linarith
      have h4 := hK N hN M
      rw [div_le_iff₀ (by positivity)]
      have : (N : ℝ) * ∑ n ∈ range M, q ^ n ≤ 2 * N ^ 2 := by nlinarith
      have : (K + 2) * N * sN * (2 * sN) = 2 * (K + 2) * (N : ℝ) ^ 2 := by
        rw [show (K + 2) * N * sN * (2 * sN) = 2 * (K + 2) * N * sN ^ 2 by ring, hsN2]; ring
      nlinarith
    · -- the tail term
      rw [norm_mul, norm_pow, hwn]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (norm_sum_le _ _).trans ?_
      have : ∀ i ∈ range M, ‖lam1 i‖ ≤ (M : ℝ) := by
        intro i hi
        have := norm_lam1_le_succ i
        have : (i : ℝ) + 1 ≤ M := by exact_mod_cast (mem_range.mp hi)
        linarith
      refine (sum_le_sum this).trans (le_of_eq ?_)
      rw [sum_const, card_range, nsmul_eq_mul]; ring
  -- the limit
  have hT : Tendsto (fun M : ℕ => ‖∑ n ∈ range M, (Real.exp (-(n / N)) : ℂ) * (lam1 n * eL (n * α))‖)
      atTop (𝓝 ‖LeanLab.LZCesaroShort.St N α - 1 / (1 - Complex.exp (-(LeanLab.LZCesaroShort.zz N α)))‖) :=
    (hasSum_weighted hN α).tendsto_sum_nat.norm
  have hT2 : Tendsto (fun M : ℕ => B + q ^ M * (M : ℝ) ^ 2) atTop (𝓝 (B + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (r := q)
      (by rw [abs_of_pos hq0]; exact hq1)
    refine h.congr fun M => ?_
    ring
  rw [add_zero] at hT2
  have hlim := le_of_tendsto_of_tendsto' hT hT2 hpart
  refine hlim.trans ?_
  -- `B ≤ C √N (1 + N|α|)`
  have hw1 : ‖1 - w‖ ≤ 1 / N + 2 * Real.pi * |α| := by
    have := norm_one_sub_qe hq0.le hq1.le α
    rw [← hwdef] at this
    linarith
  have hpi := Real.pi_lt_d2
  have hb1 : ‖1 - w‖ * N ≤ 7 * (1 + N * |α|) := by
    have := mul_le_mul_of_nonneg_right hw1 hN0.le
    have e : (1 / (N : ℝ) + 2 * Real.pi * |α|) * N = 1 + 2 * Real.pi * (N * |α|) := by
      field_simp
    rw [e] at this
    nlinarith [abs_nonneg α, mul_nonneg hN0.le (abs_nonneg α)]
  rw [hB]
  have : ‖1 - w‖ * ((K + 2) * N * sN) = (K + 2) * sN * (‖1 - w‖ * N) := by ring
  rw [this]
  have := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ (K + 2) * sN)
  have h0 : 0 ≤ sN * (1 + N * |α|) := by positivity
  nlinarith

/-- The integrand `‖S̃(α) - 1/z‖²` is continuous. -/
lemma continuous_lz_integrand {N : ℕ} (hN : 1 ≤ N) :
    Continuous (fun α => ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hpow : ∀ n : ℕ, Real.exp (-n / N) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  have hus : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0.le hq1
    refine (h1.add h2).congr fun n => ?_
    simp only [pow_one]; ring
  have hStc : Continuous (LeanLab.LZCesaroShort.St N) := by
    have : LeanLab.LZCesaroShort.St N =
        fun α => ∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * eL (n * α) := by
      ext α; simp [LeanLab.LZCesaroShort.St]
    rw [this]
    refine continuous_tsum (fun n => continuous_const.mul (continuous_e_mul _)) hus fun n α => ?_
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      hpow, abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (pow_nonneg hq0.le n))]
    have h2 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log n ≤ n := Real.log_le_self (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le n)
  have hzzc : Continuous (LeanLab.LZCesaroShort.zz N) := by
    show Continuous (fun α => LeanLab.LZCesaroShort.zz N α)
    unfold LeanLab.LZCesaroShort.zz; fun_prop
  have hzz0 : ∀ α, LeanLab.LZCesaroShort.zz N α ≠ 0 := by
    intro α h
    have := congrArg Complex.re h
    simp [LeanLab.LZCesaroShort.zz] at this
    exact absurd this (by positivity)
  exact ((hStc.sub (continuous_const.div hzzc hzz0)).norm).pow 2

set_option maxHeartbeats 1000000 in
/-- **P0058 Lemma 1 for `0 ≤ ξ ≤ 1/N`, under RH.** -/
theorem lz_lemma1_tiny (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 / N → ξ ≤ 1 / 2 →
    ∫ α in (-ξ)..ξ, ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2
      ≤ C * N * ξ := by
  obtain ⟨C, hC, hp⟩ := tiny_pointwise hRH
  refine ⟨16 * C ^ 2 + 256, by positivity, fun N hN ξ hξ0 hξ1 hξh => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hξle : -ξ ≤ ξ := by linarith
  have hpt : ∀ α ∈ Set.Icc (-ξ) ξ,
      ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2 ≤ (16 * C ^ 2 + 256) * N / 2 := by
    intro α hα
    have hαξ : |α| ≤ ξ := abs_le.mpr ⟨hα.1, hα.2⟩
    have hNα : N * |α| ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (hαξ.trans hξ1) hN0.le
      rwa [mul_one_div_cancel hN0.ne'] at this
    set zz := LeanLab.LZCesaroShort.zz N α with hzz
    have hre : zz.re = 1 / N := by simp [hzz, LeanLab.LZCesaroShort.zz]
    have him : zz.im = -(2 * Real.pi * α) := by simp [hzz, LeanLab.LZCesaroShort.zz]
    have hb := geom_sub_inv_le (z := zz) (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          have : |α| ≤ 1 / 2 := hαξ.trans hξh
          nlinarith [Real.pi_pos])
    have h1 := hp N hN α
    rw [← hzz] at h1
    have h2 : ‖LeanLab.LZCesaroShort.St N α - 1 / (1 - Complex.exp (-zz))‖ ≤ 2 * C * Real.sqrt N := by
      refine h1.trans ?_
      have := mul_le_mul_of_nonneg_left (show 1 + N * |α| ≤ 2 by linarith)
        (by positivity : 0 ≤ C * Real.sqrt N)
      linarith
    have hsplit : LeanLab.LZCesaroShort.St N α - 1 / zz =
        (LeanLab.LZCesaroShort.St N α - 1 / (1 - Complex.exp (-zz))) +
          (1 / (1 - Complex.exp (-zz)) - 1 / zz) := by ring
    rw [hsplit]
    have h3 := norm_add_le (LeanLab.LZCesaroShort.St N α - 1 / (1 - Complex.exp (-zz)))
      (1 / (1 - Complex.exp (-zz)) - 1 / zz)
    have h4 : ‖LeanLab.LZCesaroShort.St N α - 1 / (1 - Complex.exp (-zz)) +
        (1 / (1 - Complex.exp (-zz)) - 1 / zz)‖ ≤ 2 * C * Real.sqrt N + 8 := by linarith
    have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    refine h5.trans ?_
    have : (2 * C * Real.sqrt N + 8) ^ 2 ≤ 2 * (2 * C * Real.sqrt N) ^ 2 + 128 := by
      nlinarith [sq_nonneg (2 * C * Real.sqrt N - 8)]
    have e : 2 * (2 * C * Real.sqrt N) ^ 2 = 8 * C ^ 2 * N := by
      rw [mul_pow, mul_pow, hs2]; ring
    nlinarith
  have hint := intervalIntegral.integral_mono_on hξle
    ((continuous_lz_integrand hN).intervalIntegrable (μ := volume) _ _)
    (intervalIntegrable_const (μ := volume)) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  refine hint.trans (le_of_eq ?_)
  ring

end LeanLab.PNTPort.Selberg

