module

public import LeanLab.PNTPort.Selberg.LZLemma1Range
public import LeanLab.PNTPort.Selberg.WeightedMeanB

/-!
# P0058 Lemma 1 from RH alone for every ξ from about log N/√N to 1/2

Lab proof, unit U-6016, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058. AI
wrote this file: `lz_lemma1_range` of `LZLemma1Range.lean` on `weighted_mean_b`. CONDITIONAL ON
RiemannHypothesis only.

`lz_lemma1_range_b`: for naturals `1 ≤ L ≤ N`,
`∫_{-1/(2L)}^{1/(2L)} abs(S̃(α) - 1/z)² dα ≤ C (N (log(N/L) + 3)²/L + N (log N + 2)²/(√L L²) + L (log N + 1)²)`.
With `ξ = 1/(2L)` the second term is at most the first, up to `log N` against `log(N/L)`, for
every `L ≥ 1`, so the bound is `≪ Nξ log²(1/ξ)` from `ξ = 1/2` down to `ξ ≈ log N/√N`, where
the edge term `L log² N` of Gallagher's lemma takes over. P0058's Lemma 1 asks for every
`ξ ∈ [0, 1/2]`; below `log N/√N` it remains cited.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PNTPort.Gallagher

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

set_option maxHeartbeats 2000000 in
/-- **P0058 Lemma 1 for `ξ = 1/(2L)`, under RH.** -/
theorem lz_lemma1_range_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N L : ℕ, 1 ≤ L → L ≤ N →
    ∫ α in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2 ≤
      C * (N * (Real.log (N / L) + 3) ^ 2 / L + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
        + L * (Real.log N + 1) ^ 2) := by
  obtain ⟨Cw, hCw, hwm⟩ := weighted_mean_b hRH
  refine ⟨2 * Cw + 128, by positivity, fun N L hL hLN => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN : 1 ≤ N := hL.trans hLN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set W := N * (Real.log (N / L) + 3) ^ 2 / L + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
    + L * (Real.log N + 1) ^ 2 with hW
  set ξ := 1 / (2 * (L : ℝ)) with hξ
  have hξ0 : 0 < ξ := by positivity
  have hξle : -ξ ≤ ξ := by linarith
  set St := LeanLab.LZCesaroShort.St N with hStd
  set zz := LeanLab.LZCesaroShort.zz N with hzzd
  set D : ℝ → ℂ := fun α => St α - 1 / (1 - Complex.exp (-(zz α))) with hD
  set g : ℕ → ℝ → ℂ := fun n α => (Real.exp (-(n / N)) : ℂ) * (lam1 n * eL (n * α)) with hg
  -- the dominating series
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hpow : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  set u : ℕ → ℝ := fun n => ((n : ℝ) + 1) * q ^ n with hu
  have hus : Summable u := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0.le hq1
    refine (h1.add h2).congr fun n => ?_
    simp only [hu, pow_one]; ring
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hgu : ∀ n α, ‖g n α‖ ≤ u n := by
    intro n α
    simp only [hg, hu]
    rw [norm_mul, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hpow, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_lam1_le_succ n) (pow_nonneg hq0.le n)
  have hgc : ∀ n, Continuous (g n) := fun n =>
    continuous_const.mul (continuous_const.mul (continuous_e_mul _))
  -- (i) the limit
  have hlimint : ∫ α in (-ξ)..ξ, ‖D α‖ ^ 2 ≤ Cw * W := by
    have hT : Tendsto (fun M : ℕ => ∫ α in (-ξ)..ξ, ‖∑ n ∈ range M, g n α‖ ^ 2) atTop
        (𝓝 (∫ α in (-ξ)..ξ, ‖D α‖ ^ 2)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => (∑' n, u n) ^ 2) ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun M =>
          ((continuous_finsetSum _ fun n _ => hgc n).norm.pow 2).aestronglyMeasurable
      · refine Eventually.of_forall fun M => ae_of_all _ fun α _ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : ‖∑ n ∈ range M, g n α‖ ≤ ∑' n, u n :=
          (norm_sum_le _ _).trans ((sum_le_sum fun n _ => hgu n α).trans
            (hus.sum_le_tsum _ fun n _ => hu0 n))
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      · refine ae_of_all _ fun α _ => ?_
        exact ((hasSum_weighted hN α).tendsto_sum_nat.norm).pow 2
    refine le_of_tendsto' hT fun M => ?_
    exact hwm N L M hL hLN
  -- (ii) the pointwise comparison
  have hpt : ∀ α ∈ Set.uIcc (-ξ) ξ, ‖St α - 1 / zz α‖ ^ 2 ≤ 2 * ‖D α‖ ^ 2 + 128 := by
    intro α hα
    rw [Set.uIcc_of_le hξle] at hα
    have hre : (zz α).re = 1 / N := by simp [hzzd, LeanLab.LZCesaroShort.zz]
    have him : (zz α).im = -(2 * Real.pi * α) := by simp [hzzd, LeanLab.LZCesaroShort.zz]
    have hαb : |α| ≤ 1 / 2 := by
      rw [abs_le]
      have : ξ ≤ 1 / 2 := by rw [hξ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      constructor <;> linarith [hα.1, hα.2]
    have hb := geom_sub_inv_le (z := zz α) (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          nlinarith [Real.pi_pos])
    have hsplit : St α - 1 / zz α = D α + (1 / (1 - Complex.exp (-(zz α))) - 1 / zz α) := by
      simp only [hD]; ring
    rw [hsplit]
    have h1 := norm_add_le (D α) (1 / (1 - Complex.exp (-(zz α))) - 1 / zz α)
    have h2 : (‖D α‖ + ‖1 / (1 - Complex.exp (-(zz α))) - 1 / zz α‖) ^ 2 ≤ 2 * ‖D α‖ ^ 2 + 128 := by
      nlinarith [sq_nonneg (‖D α‖ - ‖1 / (1 - Complex.exp (-(zz α))) - 1 / zz α‖),
        norm_nonneg (1 / (1 - Complex.exp (-(zz α))) - 1 / zz α)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  -- (iii) continuity
  have hStc : Continuous St := by
    have : St = fun α => ∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * eL (n * α) := by
      ext α; simp [hStd, LeanLab.LZCesaroShort.St]
    rw [this]
    refine continuous_tsum (fun n => continuous_const.mul (continuous_e_mul _)) hus fun n α => ?_
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      neg_div, hpow, abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (pow_nonneg hq0.le n))]
    have h2 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log n ≤ n := Real.log_le_self (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le n)
  have hzzc : Continuous zz := by
    show Continuous (fun α => LeanLab.LZCesaroShort.zz N α)
    unfold LeanLab.LZCesaroShort.zz; fun_prop
  have hzz0 : ∀ α, zz α ≠ 0 := by
    intro α h
    have := congrArg Complex.re h
    simp [hzzd, LeanLab.LZCesaroShort.zz] at this
    exact absurd this (by positivity)
  have hden0 : ∀ α, 1 - Complex.exp (-(zz α)) ≠ 0 := by
    intro α h
    have h1 : Complex.exp (-(zz α)) = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [cexp_neg_zz, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one] at h2
    linarith
  have hDc : Continuous D := by
    simp only [hD]
    exact hStc.sub (continuous_const.div (continuous_const.sub (hzzc.neg.cexp)) hden0)
  have hLc : Continuous (fun α => ‖St α - 1 / zz α‖ ^ 2) :=
    ((hStc.sub (continuous_const.div hzzc hzz0)).norm).pow 2
  have hRc : Continuous (fun α => 2 * ‖D α‖ ^ 2 + 128) :=
    (continuous_const.mul (hDc.norm.pow 2)).add continuous_const
  -- (iv) assembly
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hξle
    (hLc.intervalIntegrable (μ := volume) _ _)
    (hRc.intervalIntegrable (μ := volume) _ _)
    (fun α hα => hpt α (by rw [Set.uIcc_of_le hξle]; exact hα))
  have hDi : IntervalIntegrable (fun α => 2 * ‖D α‖ ^ 2) volume (-ξ) ξ :=
    (continuous_const.mul (hDc.norm.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hDi intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have hlen : ξ - -ξ = 1 / L := by rw [hξ]; field_simp; ring
  rw [hlen] at hmono
  have hW1 : 1 / (L : ℝ) ≤ W := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
    have h1 : 1 / (L : ℝ) ≤ L * (Real.log N + 1) ^ 2 := by
      rw [div_le_iff₀ hL0]
      have hb : 1 ≤ (Real.log N + 1) ^ 2 := by nlinarith
      have hLL : 1 ≤ (L : ℝ) * L := by nlinarith
      have : (L : ℝ) * L ≤ L * (Real.log N + 1) ^ 2 * L := by
        have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ L * L)
        nlinarith
      linarith
    have : 0 ≤ (N : ℝ) * (Real.log (N / L) + 3) ^ 2 / L := by positivity
    have : 0 ≤ N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 := by positivity
    rw [hW]; linarith
  calc ∫ α in (-ξ)..ξ, ‖St α - 1 / zz α‖ ^ 2
      ≤ 2 * (∫ α in (-ξ)..ξ, ‖D α‖ ^ 2) + 1 / L * 128 := hmono
    _ ≤ 2 * (Cw * W) + 128 * W := by linarith
    _ = (2 * Cw + 128) * W := by ring

end LeanLab.PNTPort.Selberg

