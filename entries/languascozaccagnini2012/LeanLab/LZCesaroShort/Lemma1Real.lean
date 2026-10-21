module

public import LeanLab.PNTPort.Selberg.LZLemma1RangeB

/-!
# P0058 Lemma 1 for real `ξ` from `(log N + 1)/√N` to `1/2`, from RH alone

Lab proof, unit U-6102, CLOUD 20261020T0618Z-cloud36. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `PNTPort.Selberg.lz_lemma1_range_b`, which is stated on the grid
`ξ = 1/(2L)`. Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 3, Lemma 1: `∫_{-ξ}^{ξ} |S̃(α) − 1/z|² dα ≪ Nξ (1 + log(2Nξ))²`
for `0 ≤ ξ ≤ 1/2`.

* `lemma1_real`: **under RH**, for every `N ≥ 2` and real `ξ` with `(log N + 1)/√N ≤ ξ ≤ 1/2`,
  `∫_{-ξ}^{ξ} ‖S̃(α) − 1/z‖² dα ≤ K N ξ (1 + log(2Nξ))²`, the paper's shape exactly.

Below `(log N + 1)/√N` the lab still cites `lz_lemma1`; P0058 uses Lemma 1 only at
`ξ = 2^k/H`, so this covers every use with `H ≤ √N/(log N + 1)`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open MeasureTheory

/-- The integral of a nonnegative continuous-free integrand over `[-a, a]` grows with `a`. -/
lemma integral_sym_mono {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hi : IntervalIntegrable f volume (-b) b) :
    ∫ x in (-a)..a, f x ≤ ∫ x in (-b)..b, f x := by
  have h1 : IntervalIntegrable f volume (-b) (-a) := hi.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable f volume (-a) a := hi.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) (by linarith))
  have h3 : IntervalIntegrable f volume a b := hi.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 (h2.trans h3),
    ← intervalIntegral.integral_add_adjacent_intervals h2 h3]
  have p1 : 0 ≤ ∫ x in (-b)..(-a), f x :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => hf x
  have p3 : 0 ≤ ∫ x in a..b, f x := intervalIntegral.integral_nonneg hab fun x _ => hf x
  linarith

/-- `S̃ − 1/z` is continuous. -/
lemma continuous_St_sub {N : ℕ} (hN : 1 ≤ N) : Continuous (fun α => ‖St N α - 1 / zz N α‖ ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hpow : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  have hus : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0.le hq1
    refine (h1.add h2).congr fun n => ?_
    simp only [pow_one]; ring
  have hStc : Continuous (St N) := by
    have : St N = fun α => ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n * Real.exp (-n / N) : ℝ) : ℂ)
        * LeanLab.PNTPort.LargeSieve.e (n * α) := by
      ext α; simp [St]
    rw [this]
    refine continuous_tsum (fun n => continuous_const.mul
      (LeanLab.PNTPort.Gallagher.continuous_e_mul _)) hus fun n α => ?_
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      neg_div, hpow, abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (pow_nonneg hq0.le n))]
    have h2 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log n ≤ n := Real.log_le_self (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le n)
  have hzzc : Continuous (zz N) := by unfold zz; fun_prop
  have hzz0 : ∀ α, zz N α ≠ 0 := by
    intro α h
    have := congrArg Complex.re h
    simp [zz] at this
    exact absurd this (by positivity)
  exact ((hStc.sub (continuous_const.div hzzc hzz0)).norm).pow 2

set_option maxHeartbeats 2000000 in
/-- **P0058 Lemma 1 for real `ξ ≥ (log N + 1)/√N`, under RH**, in the paper's shape. -/
theorem lemma1_real (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 2 ≤ N → ∀ ξ : ℝ, (Real.log N + 1) / Real.sqrt N ≤ ξ → ξ ≤ 1 / 2 →
      ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2 ≤ K * N * ξ * (1 + Real.log (2 * N * ξ)) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := LeanLab.PNTPort.Selberg.lz_lemma1_range_b hRH
  refine ⟨C * 1000, by positivity, fun N hN ξ hξlo hξhi => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξlo
  -- `ξ² N ≥ (log N + 1)²`
  have hξsq : (Real.log N + 1) ^ 2 ≤ ξ ^ 2 * N := by
    have h1 : Real.log N + 1 ≤ ξ * Real.sqrt N := by rwa [div_le_iff₀ hsN] at hξlo
    have h0 : 0 ≤ Real.log N + 1 := by linarith
    calc (Real.log N + 1) ^ 2 ≤ (ξ * Real.sqrt N) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = ξ ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hN0.le]
  -- the grid point `L = ⌊1/(2ξ)⌋₊`
  set L : ℕ := ⌊1 / (2 * ξ)⌋₊ with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Nat.one_le_floor_iff, le_div_iff₀ (by positivity)]; linarith
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hLle : (L : ℝ) ≤ 1 / (2 * ξ) := Nat.floor_le (by positivity)
  have hLgt : 1 / (2 * ξ) < L + 1 := Nat.lt_floor_add_one _
  have hξL : ξ ≤ 1 / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hLle; linarith
  have hinvL : 1 / (L : ℝ) ≤ 4 * ξ := by
    have : 1 / (2 * ξ) < 2 * L := by linarith
    rw [div_lt_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hL0]; linarith
  have hLξ : (L : ℝ) * ξ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hLle; linarith
  -- `L ≤ N`
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := by
      have h1 : (L : ℝ) ≤ 1 / (2 * ξ) := hLle
      have h2 : 1 / (2 * ξ) ≤ N := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 ≤ ξ * Real.sqrt N := by
          have := (div_le_iff₀ hsN).mp hξlo; nlinarith
        have hs1 : Real.sqrt N ≤ N := by nlinarith
        nlinarith
      linarith
    exact_mod_cast this
  have hint := hb N L hL1 hLN
  -- monotonicity in the interval
  have hmono : ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2
      ≤ ∫ α in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖St N α - 1 / zz N α‖ ^ 2 :=
    integral_sym_mono (fun _ => by positivity) hξ0.le hξL
      ((continuous_St_sub (by omega)).intervalIntegrable _ _)
  -- the logs: `a = log(2Nξ) ≥ 0` and the three terms of `hint`
  set a := Real.log (2 * N * ξ) with ha
  have h2Nξ : 1 ≤ 2 * N * ξ := by
    have : 1 ≤ ξ * Real.sqrt N := by
      have := (div_le_iff₀ hsN).mp hξlo; nlinarith
    have hs1 : Real.sqrt N ≤ N := by nlinarith
    nlinarith
  have ha0 : 0 ≤ a := Real.log_nonneg h2Nξ
  -- `log(N/L) ≤ log 2 + a`
  have hNL : Real.log (N / L) ≤ 1 + a := by
    have h1 : (N : ℝ) / L ≤ 2 * (2 * N * ξ) := by
      rw [div_le_iff₀ hL0]
      have := mul_le_mul_of_nonneg_left hinvL hN0.le
      have e : (N : ℝ) * (1 / L) * L = N := by field_simp
      nlinarith
    have h2 : Real.log ((N : ℝ) / L) ≤ Real.log (2 * (2 * N * ξ)) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h2
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hNL0 : 0 ≤ Real.log (N / L) := Real.log_nonneg (by
    rw [le_div_iff₀ hL0, one_mul]; exact_mod_cast hLN)
  -- `log N ≤ 2 a + 2`: from `2Nξ ≥ 2√N`
  have hlogNa : Real.log N ≤ 2 * a + 2 := by
    have h1 : Real.sqrt N ≤ 2 * N * ξ := by
      have : 1 ≤ ξ * Real.sqrt N := by
        have := (div_le_iff₀ hsN).mp hξlo; nlinarith
      nlinarith
    have h2 : Real.log (Real.sqrt N) ≤ a := Real.log_le_log hsN h1
    rw [Real.log_sqrt hN0.le] at h2
    linarith
  -- term 1
  have t1 : (N : ℝ) * (Real.log (N / L) + 3) ^ 2 / L ≤ 4 * N * ξ * (16 * (1 + a) ^ 2) := by
    have hsq1 : (Real.log (N / L) + 3) ^ 2 ≤ 16 * (1 + a) ^ 2 := by nlinarith
    calc (N : ℝ) * (Real.log (N / L) + 3) ^ 2 / L = (N : ℝ) * (Real.log (N / L) + 3) ^ 2 * (1 / L) := by
          ring
      _ ≤ (N : ℝ) * (16 * (1 + a) ^ 2) * (4 * ξ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq1 hN0.le) hinvL (by positivity)
            (by positivity)
      _ = _ := by ring
  -- term 2
  have t2 : (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
      ≤ 4 * N * ξ * (16 * (1 + a) ^ 2) := by
    have hsL : 1 ≤ Real.sqrt (L : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL1r
    have hlg : (Real.log N + 2) ^ 2 ≤ 16 * (1 + a) ^ 2 := by nlinarith
    have h1 : (Real.log N + 2) ^ 2 / Real.sqrt L ≤ 16 * (1 + a) ^ 2 :=
      (div_le_self (by positivity) hsL).trans hlg
    have h2 : 1 / (L : ℝ) ^ 2 ≤ 4 * ξ := by
      have : 1 / (L : ℝ) ^ 2 ≤ 1 / L := by
        rw [div_le_div_iff₀ (by positivity) hL0]; nlinarith
      linarith
    calc (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
        = (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) * (1 / (L : ℝ) ^ 2) := by ring
      _ ≤ (N : ℝ) * (16 * (1 + a) ^ 2) * (4 * ξ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hN0.le) h2 (by positivity) (by positivity)
      _ = _ := by ring
  -- term 3
  have t3 : (L : ℝ) * (Real.log N + 1) ^ 2 ≤ N * ξ * (1 + a) ^ 2 := by
    have h1 : (L : ℝ) * (Real.log N + 1) ^ 2 ≤ L * (ξ ^ 2 * N) :=
      mul_le_mul_of_nonneg_left hξsq hL0.le
    have h2 : (L : ℝ) * (ξ ^ 2 * N) ≤ N * ξ / 2 := by
      have := mul_le_mul_of_nonneg_right hLξ (show 0 ≤ ξ * N by positivity); nlinarith
    have h3 : 1 ≤ (1 + a) ^ 2 := by nlinarith
    have : N * ξ / 2 ≤ N * ξ * (1 + a) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h3 (show 0 ≤ (N : ℝ) * ξ by positivity); nlinarith
    linarith
  calc ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2
      ≤ C * (N * (Real.log (N / L) + 3) ^ 2 / L
          + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
          + L * (Real.log N + 1) ^ 2) := hmono.trans hint
    _ ≤ C * (4 * N * ξ * (16 * (1 + a) ^ 2) + 4 * N * ξ * (16 * (1 + a) ^ 2)
          + N * ξ * (1 + a) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith
    _ ≤ C * 1000 * N * ξ * (1 + a) ^ 2 := by
        have : 0 ≤ C * (N * ξ * (1 + a) ^ 2) := by positivity
        nlinarith

end LeanLab.LZCesaroShort

