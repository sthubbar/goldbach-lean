module

public import LeanLab.PNTPort.Selberg.LZLemma1Range
public import LeanLab.LZCesaroShort.Lemma3Parseval
public import LeanLab.Zinoviev1997.Lemma15

/-!
# P0058 Lemma 3, the upper bound the paper uses

Lab proof, unit U-6101, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 3, Lemma 3: `∫_{-1/2}^{1/2} |S̃(α) − 1/z|² dα = (N/2) log N +
O(N (log N)^{1/2})`. Its only uses, in (15) of Lemma 6 and so in Theorem 2, need the upper bound
`≪ N log N`. This file proves it explicitly for `N ≥ 10^20`:

* `lemma3_upper`: `∫_{-1/2}^{1/2} ‖S̃(α) − 1/z‖² dα ≤ 2 N log N + N + 130`.

Route: `S̃ − 1/(1 − e^{−z}) = Σ e^{−n/N} (Λ(n) − 1) e(nα)` (`hasSum_weighted`), Parseval
(`parseval_tsum`), `(Λ − 1)² ≤ Λ² + 1`, and Zinoviev 1997 Lemma 1.5 as proved in the lab,
`Zinoviev1997.lemma15`: `Σ_{n ≤ M} Λ(n)² e^{−2n/N} ≤ 0.96 N log N`; the gap
`1/(1 − e^{−z}) − 1/z` is at most `8` by `geom_sub_inv_le`. A connection: one lemma serves
Zinoviev's ternary Lemma 1.5 and Languasco-Zaccagnini's Lemma 3.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PNTPort.Gallagher LeanLab.PNTPort.Selberg

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- `1/(1 − e^{−x}) ≤ 1 + 1/x` for `x > 0`. -/
lemma inv_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) : 1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have he : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have hlt : Real.exp (-x) < 1 := by
    rw [he, div_lt_one hpos]; linarith
  have hd : 0 < 1 - Real.exp (-x) := by linarith
  rw [div_le_iff₀ hd]
  rw [he]
  have : (1 + 1 / x) * (1 - 1 / Real.exp x) = (1 + 1 / x) - (1 + 1 / x) / Real.exp x := by ring
  rw [this]
  have h2 : (1 + 1 / x) / Real.exp x ≤ 1 / x := by
    rw [div_le_iff₀ hpos]
    have : (1 + 1 / x) = (1 / x) * (1 + x) := by field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

set_option maxHeartbeats 2000000 in
/-- **P0058 Lemma 3, upper bound**: for `N ≥ 10^20`,
`∫_{-1/2}^{1/2} ‖S̃(α) − 1/z‖² dα ≤ 2 N log N + N + 130`. -/
theorem lemma3_upper (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖St N α - 1 / zz N α‖ ^ 2
      ≤ 2 * N * Real.log N + N + 130 := by
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  set D : ℝ → ℂ := fun α => St N α - 1 / (1 - Complex.exp (-(zz N α))) with hD
  set c : ℕ → ℂ := fun n => (Real.exp (-(n / N)) : ℂ) * lam1 n with hc
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hpow : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  have hcn : ∀ n, ‖c n‖ ≤ ((n : ℝ) + 1) * q ^ n := by
    intro n
    simp only [hc]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hpow,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_lam1_le_succ n) (pow_nonneg hq0.le n)
  have hus : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0.le hq1
    refine (h1.add h2).congr fun n => ?_
    simp only [pow_one]; ring
  have hcs : Summable (fun n => ‖c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hcn hus
  -- `D = Σ' c n e(nα)`
  have hDeq : ∀ α, D α = ∑' n, c n * eL (n * α) := by
    intro α
    simp only [hD]
    rw [← (hasSum_weighted hNn α).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hc]; ring
  -- (i) Parseval
  have hpars : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖D α‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
    simp_rw [hDeq]; exact parseval_tsum c hcs
  -- the coefficient sum
  have hcsq : ∀ n : ℕ, ‖c n‖ ^ 2 ≤ Λ n ^ 2 * Real.exp (-2 * n / N) + Real.exp (-2 * n / N) := by
    intro n
    simp only [hc, lam1]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, sq_abs]
    have he : Real.exp (-(n / N)) ^ 2 = Real.exp (-2 * n / N) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he]
    have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have : (Λ n - 1) ^ 2 ≤ Λ n ^ 2 + 1 := by nlinarith
    have hp := Real.exp_pos (-2 * n / N)
    nlinarith
  have hq2 : ∀ n : ℕ, Real.exp (-2 * n / N) = (q ^ 2) ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hgs : Summable (fun n : ℕ => Real.exp (-2 * n / N)) := by
    simp_rw [hq2]; exact summable_geometric_of_lt_one (by positivity) hq21
  have hΛs : Summable (fun n : ℕ => Λ n ^ 2 * Real.exp (-2 * n / N)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hus.mul_left 4)
    have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have h1 : Λ n ≤ n := ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_self (Nat.cast_nonneg n))
    rw [hq2]
    have hq2le : (q ^ 2) ^ n ≤ q ^ n := by
      rw [← pow_mul]; exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    have : Λ n ^ 2 ≤ 4 * ((n : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hl : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
        have hl1 : Real.log n ≤ 2 * Real.sqrt n := by
          have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast h : (0:ℝ) < n))
          rw [Real.log_sqrt (Nat.cast_nonneg n)] at this
          have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
          linarith
        have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
        nlinarith
    calc Λ n ^ 2 * (q ^ 2) ^ n ≤ (4 * ((n : ℝ) + 1)) * q ^ n :=
          mul_le_mul this hq2le (by positivity) (by positivity)
      _ = _ := by ring
  have hΛb : ∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N) ≤ 0.96 * N * Real.log N := by
    refine hΛs.tsum_le_of_sum_range_le fun M => ?_
    have h := LeanLab.Zinoviev1997.lemma15 N hN M
    refine le_trans ?_ h
    have hsub : range M ⊆ insert 0 (Icc 1 M) := by
      intro n hn; simp only [mem_range, mem_insert, mem_Icc] at hn ⊢; omega
    calc ∑ n ∈ range M, Λ n ^ 2 * Real.exp (-2 * n / N)
        ≤ ∑ n ∈ insert 0 (Icc 1 M), Λ n ^ 2 * Real.exp (-2 * n / N) :=
          sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
      _ = _ := by
          rw [sum_insert (by simp)]; simp
  have hgb : ∑' n : ℕ, Real.exp (-2 * n / N) ≤ 1 + N / 2 := by
    simp_rw [hq2]
    rw [tsum_geometric_of_lt_one (by positivity) hq21]
    have e : q ^ 2 = Real.exp (-(2 / N)) := by
      rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [← one_div, e]
    have := inv_one_sub_exp_neg_le (x := 2 / (N : ℝ)) (by positivity)
    rwa [one_div_div] at this
  have hsumc : ∑' n, ‖c n‖ ^ 2 ≤ 0.96 * N * Real.log N + (1 + N / 2) := by
    have hs2 : Summable (fun n => ‖c n‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun n => by positivity) hcsq (hΛs.add hgs)
    calc ∑' n, ‖c n‖ ^ 2 ≤ ∑' n : ℕ, (Λ n ^ 2 * Real.exp (-2 * n / N) + Real.exp (-2 * n / N)) :=
          hs2.tsum_le_tsum hcsq (hΛs.add hgs)
      _ = _ := hΛs.tsum_add hgs
      _ ≤ _ := add_le_add hΛb hgb
  -- (ii) the pointwise comparison
  have hξle : -(1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hpt : ∀ α ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2), ‖St N α - 1 / zz N α‖ ^ 2 ≤ 2 * ‖D α‖ ^ 2 + 128 := by
    intro α hα
    rw [Set.uIcc_of_le hξle] at hα
    have hre : (zz N α).re = 1 / N := by simp [zz]
    have him : (zz N α).im = -(2 * Real.pi * α) := by simp [zz]
    have hαb : |α| ≤ 1 / 2 := by rw [abs_le]; exact ⟨hα.1, hα.2⟩
    have hb := geom_sub_inv_le (z := zz N α) (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          nlinarith [Real.pi_pos])
    have hsplit : St N α - 1 / zz N α = D α + (1 / (1 - Complex.exp (-(zz N α))) - 1 / zz N α) := by
      simp only [hD]; ring
    rw [hsplit]
    have h1 := norm_add_le (D α) (1 / (1 - Complex.exp (-(zz N α))) - 1 / zz N α)
    have h2 : (‖D α‖ + ‖1 / (1 - Complex.exp (-(zz N α))) - 1 / zz N α‖) ^ 2 ≤ 2 * ‖D α‖ ^ 2 + 128 := by
      nlinarith [sq_nonneg (‖D α‖ - ‖1 / (1 - Complex.exp (-(zz N α))) - 1 / zz N α‖),
        norm_nonneg (1 / (1 - Complex.exp (-(zz N α))) - 1 / zz N α)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  -- (iii) continuity
  have hStc : Continuous (St N) := by
    have : St N = fun α => ∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * eL (n * α) := by
      ext α; simp [St]
    rw [this]
    refine continuous_tsum (fun n => continuous_const.mul (continuous_e_mul _)) hus fun n α => ?_
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      neg_div, hpow, abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (pow_nonneg hq0.le n))]
    have h2 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log n ≤ n := Real.log_le_self (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le n)
  have hzzc : Continuous (zz N) := by
    unfold zz; fun_prop
  have hzz0 : ∀ α, zz N α ≠ 0 := by
    intro α h
    have := congrArg Complex.re h
    simp [zz] at this
    exact absurd this (by positivity)
  have hden0 : ∀ α, 1 - Complex.exp (-(zz N α)) ≠ 0 := by
    intro α h
    have h1 : Complex.exp (-(zz N α)) = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [cexp_neg_zz, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one] at h2
    linarith
  have hDc : Continuous D := by
    simp only [hD]
    exact hStc.sub (continuous_const.div (continuous_const.sub (hzzc.neg.cexp)) hden0)
  have hLc : Continuous (fun α => ‖St N α - 1 / zz N α‖ ^ 2) :=
    ((hStc.sub (continuous_const.div hzzc hzz0)).norm).pow 2
  have hRc : Continuous (fun α => 2 * ‖D α‖ ^ 2 + 128) :=
    (continuous_const.mul (hDc.norm.pow 2)).add continuous_const
  -- (iv) assembly
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hξle
    (hLc.intervalIntegrable (μ := volume) _ _)
    (hRc.intervalIntegrable (μ := volume) _ _)
    (fun α hα => hpt α (by rw [Set.uIcc_of_le hξle]; exact hα))
  have hDi : IntervalIntegrable (fun α => 2 * ‖D α‖ ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (continuous_const.mul (hDc.norm.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hDi intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, hpars] at hmono
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have : 0 ≤ (N : ℝ) * Real.log N := by positivity
  nlinarith

end LeanLab.LZCesaroShort

