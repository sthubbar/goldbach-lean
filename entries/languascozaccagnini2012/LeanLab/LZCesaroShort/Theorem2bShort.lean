module

public import LeanLab.LZCesaroShort.Circle2
public import LeanLab.LZCesaroShort.Layer
public import LeanLab.LZCesaroShort.Lemma1Real
public import LeanLab.LZCesaroShort.Theorem1Printed

/-!
# P0058 Theorem 2 eq. (3), as printed, under RH, for `2H(log N + 1) ≤ √N`

Lab proof, unit U-6106, CLOUD 20261020T0618Z-cloud36. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `lemma1_real`; every other step is proved here or in the
imported lab files with no cited input. Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 2, Theorem 2 eq. (3): under RH, for `N ≥ 2`, `1 ≤ H ≤ N`,
`|Σ_{n=N−H}^{N+H} e^{−n/N}(R(n) − (2ψ(n) − n))(1 − |n − N|/H)| ≪ N (log(2N/H))²`.

* `I3_bound`: `‖∫ T(−α) R̃(α)² dα‖ ≤ 48 K₁ H N (1 + log(2N/H))²`, eq. (30), by the layer bound
  of `Layer.lean` and Lemma 1 at `ξ_k = min(2^k/H, 1/2)`;
* `theorem2b_short`: **under RH**, there is `K` with `|wsum N H H| ≤ K N (log(2N/H))²` for every
  `N ≥ 10^20` and every `H ≥ 1` with `2H(log N + 1) ≤ √N`.

The range of `H` is where the lab's Lemma 1 holds from RH alone; for larger `H` the paper's
proof needs Lemma 1 at `ξ = 1/H < (log N + 1)/√N`, still cited in the lab.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

/-- `Σ_{k < n} (k + 1)²/2^k = 12 − (n² + 4n + 6)/2^{n−1}`, in a form without subtraction. -/
lemma sum_sq_div_two_pow (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 1) ^ 2 / 2 ^ k + 2 * ((n : ℝ) ^ 2 + 4 * n + 6) / 2 ^ n = 12 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have e : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [e]
    have : ((n : ℝ) + 1) ^ 2 / 2 ^ n + 2 * (((n + 1 : ℕ) : ℝ) ^ 2 + 4 * ((n + 1 : ℕ) : ℝ) + 6) / (2 * 2 ^ n)
        = 2 * ((n : ℝ) ^ 2 + 4 * n + 6) / 2 ^ n := by
      field_simp; push_cast; ring
    linarith

lemma sum_sq_div_two_pow_le (n : ℕ) : ∑ k ∈ range n, ((k : ℝ) + 1) ^ 2 / 2 ^ k ≤ 12 := by
  have := sum_sq_div_two_pow n
  have : 0 ≤ 2 * ((n : ℝ) ^ 2 + 4 * n + 6) / 2 ^ n := by positivity
  linarith

lemma G_neg {H : ℕ} {α : ℝ} (hα : |α| ≤ 1 / 2) : G H (-α) = G H α := by
  have h1 := dist0_eq_abs hα
  have h2 := dist0_eq_abs (show |-α| ≤ 1 / 2 by rwa [abs_neg])
  unfold G; rw [h1, h2, abs_neg]

set_option maxHeartbeats 4000000 in
/-- **`I₃` at `y = H`, eq. (30), under RH.** -/
theorem I3_bound (hRH : RiemannHypothesis) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧
    ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) ^ 2‖
        ≤ 48 * K₁ * H * N * (1 + Real.log (2 * N / H)) ^ 2 := by
  obtain ⟨K₁, hK₁, hl1⟩ := lemma1_real hRH
  refine ⟨K₁, hK₁, fun N H hN hH hHs => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNn : 1 ≤ N := by omega
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hsle : Real.sqrt (N : ℝ) ≤ N := by nlinarith
  have hHN : (H : ℝ) < N := by nlinarith
  have hHNn : H ≤ N := by exact_mod_cast hHN.le
  set f : ℝ → ℝ := fun α => ‖St N α - 1 / zz N α‖ ^ 2 with hf
  have hfc : Continuous f := continuous_St_sub hNn
  have hTc := continuous_TH_neg N H
  have hK : (H : ℝ) ≤ 2 ^ H := by
    have := Nat.lt_two_pow_self (n := H); exact_mod_cast this.le
  -- step 1: `‖∫ T R̃²‖ ≤ ∫ ‖T(−α)‖ f`
  have h1 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (St N α - 1 / zz N α) ^ 2‖
      ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖TH N H H (-α)‖ * f α := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
    congr 1; ext α; rw [norm_mul, norm_pow]
  -- step 2: the layer bound
  have h2 := integral_G_sq_le (H := H) (K := H) hH hK hfc (fun α => by positivity) hTc.norm
    (fun α hα => by
      have hab : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
      rw [← G_neg hab]; exact lemma5_full hHNn (-α))
  -- step 3: Lemma 1 on each window
  set a := Real.log (2 * N / H) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by rw [le_div_iff₀ hH0]; linarith)
  have hlo : (Real.log N + 1) / Real.sqrt N ≤ 1 / (2 * H) := by
    rw [div_le_div_iff₀ hsN (by positivity)]; linarith
  have hwin : ∀ k ∈ range (H + 1), 4 * (H : ℝ) ^ 2 / 4 ^ k * ∫ α in (-xi H k)..(xi H k), f α
      ≤ 4 * K₁ * H * N * (1 + a) ^ 2 * (((k : ℝ) + 1) ^ 2 / 2 ^ k) := by
    intro k _
    have hx0 : 1 / (2 * H) ≤ xi H k := by
      unfold xi
      apply le_min
      · rw [div_le_div_iff₀ (by positivity) hH0]
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hl := hl1 N hN (xi H k) (hlo.trans hx0) (xi_le_half H k)
    have hxi0 : 0 < xi H k := lt_of_lt_of_le (by positivity) hx0
    have hxle := xi_le H k
    -- the log
    have h2N : 1 ≤ 2 * N * xi H k := by
      have : 2 * (N : ℝ) * (1 / (2 * H)) ≤ 2 * N * xi H k :=
        mul_le_mul_of_nonneg_left hx0 (by positivity)
      have e : 2 * (N : ℝ) * (1 / (2 * H)) = N / H := by field_simp
      rw [e] at this
      have : (1 : ℝ) ≤ N / H := by rw [le_div_iff₀ hH0]; linarith
      linarith
    have hlg0 : 0 ≤ Real.log (2 * N * xi H k) := Real.log_nonneg h2N
    have hlg : Real.log (2 * N * xi H k) ≤ a + k := by
      have h1 : 2 * N * xi H k ≤ (2 * N / H) * 2 ^ k := by
        have := mul_le_mul_of_nonneg_left hxle (show (0 : ℝ) ≤ 2 * N by positivity)
        calc 2 * N * xi H k ≤ 2 * N * ((2 : ℝ) ^ k / H) := this
          _ = (2 * N / H) * 2 ^ k := by ring
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (x := 2 * N / H) (y := 2 ^ k) (by positivity) (by positivity), Real.log_pow] at h2
      have : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have : (k : ℝ) * Real.log 2 ≤ k := by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      linarith
    have hsq : (1 + Real.log (2 * N * xi H k)) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2 := by
      have : 1 + Real.log (2 * N * xi H k) ≤ ((k : ℝ) + 1) * (1 + a) := by
        nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) this 2
    have hint : ∫ α in (-xi H k)..(xi H k), f α
        ≤ K₁ * N * ((2 : ℝ) ^ k / H) * (((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2) := by
      refine hl.trans ?_
      have := mul_le_mul hxle hsq (by positivity) (by positivity)
      calc K₁ * N * xi H k * (1 + Real.log (2 * N * xi H k)) ^ 2
          = K₁ * N * (xi H k * (1 + Real.log (2 * N * xi H k)) ^ 2) := by ring
        _ ≤ K₁ * N * ((2 : ℝ) ^ k / H * (((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    calc 4 * (H : ℝ) ^ 2 / 4 ^ k * ∫ α in (-xi H k)..(xi H k), f α
        ≤ 4 * (H : ℝ) ^ 2 / 4 ^ k * (K₁ * N * ((2 : ℝ) ^ k / H) * (((k : ℝ) + 1) ^ 2 * (1 + a) ^ 2)) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = 4 * K₁ * H * N * (1 + a) ^ 2 * (((k : ℝ) + 1) ^ 2 / 2 ^ k) := by
          rw [h4]; field_simp
  have h3 := sum_le_sum hwin
  rw [← mul_sum] at h3
  have h12 := sum_sq_div_two_pow_le (H + 1)
  have : 4 * K₁ * H * N * (1 + a) ^ 2 * ∑ k ∈ range (H + 1), ((k : ℝ) + 1) ^ 2 / 2 ^ k
      ≤ 4 * K₁ * H * N * (1 + a) ^ 2 * 12 := mul_le_mul_of_nonneg_left h12 (by positivity)
  linarith

set_option maxHeartbeats 4000000 in
/-- **P0058 Theorem 2 eq. (3), as printed, under RH, for `2H(log N + 1) ≤ √N`.** -/
theorem theorem2b_short (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N H : ℕ, (10 : ℝ) ^ 20 ≤ N → 1 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      |wsum N H H| ≤ K * N * Real.log (2 * N / H) ^ 2 := by
  obtain ⟨K₁, hK₁, hI3⟩ := I3_bound hRH
  refine ⟨140 + 432 * K₁, by positivity, fun N H hN hH hHs => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN2n : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := le_trans (by norm_num) hN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by linarith
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hsle : Real.sqrt (N : ℝ) ≤ N := by nlinarith
  have hHN : (H : ℝ) < N := by nlinarith
  have hHNn : H < N := by exact_mod_cast hHN
  -- `4 H² (log N + 1)² ≤ N`
  have hH2 : 4 * (H : ℝ) ^ 2 * (Real.log N + 1) ^ 2 ≤ N := by
    have h := pow_le_pow_left₀ (by positivity) hHs 2
    rw [Real.sq_sqrt hN0.le] at h; nlinarith
  -- the pieces
  set T : ℝ → ℂ := fun α => TH N H H (-α)
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α
  set iz : ℝ → ℂ := fun α => 1 / zz N α
  have hTc : Continuous T := continuous_TH_neg N H
  have hStc : Continuous (St N) := continuous_St hNn
  have hizc : Continuous iz := continuous_const.div (continuous_zz N) (zz_ne_zero hNn)
  have hRtc : Continuous Rt := hStc.sub hizc
  have hpt : ∀ α, St N α ^ 2 * TH N H H (-α)
      = T α * iz α ^ 2 + 2 * (T α * Rt α * iz α) + T α * Rt α ^ 2 := by
    intro α; simp only [T, Rt, iz]; ring
  have hQ := Q_eq (H := H) hNn
  have hdec : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), St N α ^ 2 * TH N H H (-α)
      = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2)
        + 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
    simp_rw [hpt]
    have j1 : IntervalIntegrable (fun α => T α * iz α ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (hTc.mul (hizc.pow 2)).intervalIntegrable _ _
    have j2 : IntervalIntegrable (fun α => 2 * (T α * Rt α * iz α)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (continuous_const.mul ((hTc.mul hRtc).mul hizc)).intervalIntegrable _ _
    have j3 : IntervalIntegrable (fun α => T α * Rt α ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      (hTc.mul (hRtc.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (j1.add j2) j3, intervalIntegral.integral_add j1 j2,
      intervalIntegral.integral_const_mul]
  have b1 := I1_bound hNn hHNn
  have b2 := I2_bound hN hHNn
  have b3 := hI3 N H hN2n hH hHs
  -- the real identity
  set M1 : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * (n * Real.exp (-n / N))
  set M2 : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n))
  set Qr : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * Real.exp (-n / N) * R n
  have hw : (H : ℝ) * wsum N H H = Qr - M1 - 2 * M2 := by
    have hfilt : (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + H) = Icc (N - H) (N + H) := by
      apply filter_true_of_mem; intro n hn; rw [mem_Icc] at hn; exact_mod_cast hn.2
    unfold wsum
    rw [hfilt, mul_sum]
    simp only [Qr, M1, M2, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [w_eq hH]
    unfold tw
    rw [neg_div]
    field_simp
    ring
  have hwC : (((H : ℝ) * wsum N H H : ℝ) : ℂ)
      = ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
        + (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
    have : ((Qr : ℝ) : ℂ) = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2)
        + 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
      rw [← hdec, hQ]; simp only [Qr]; push_cast; rfl
    rw [hw]; push_cast; rw [this]; ring
  have hM1 : ((M1 : ℝ) : ℂ) = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ) := by simp only [M1]; push_cast; rfl
  have hM2 : ((M2 : ℝ) : ℂ) = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ) := by
    simp only [M2]; push_cast; rfl
  have hA : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ)‖ ≤ (H : ℝ) ^ 2 := by
    rw [hM1]; exact b1
  have hB : ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ)‖
      ≤ 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N) + 8 * Real.sqrt (1 + N / 2) + 1) := by
    rw [hM2]; exact b2
  have hC : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2‖
      ≤ 48 * K₁ * H * N * (1 + Real.log (2 * N / H)) ^ 2 := b3
  have htot : (H : ℝ) * |wsum N H H| ≤ (H : ℝ) ^ 2
      + 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N) + 8 * Real.sqrt (1 + N / 2) + 1)
      + 48 * K₁ * H * N * (1 + Real.log (2 * N / H)) ^ 2 := by
    have h := norm_add₃_le (a := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
      (b := 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
      (c := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2)
    rw [← hwC, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hH0] at h
    linarith
  -- divide by `H`
  have hlN1 : 1 ≤ (Real.log N + 1) ^ 2 := by nlinarith
  have hlN2 : Real.log N ≤ (Real.log N + 1) ^ 2 := by nlinarith [sq_nonneg (Real.log N)]
  have hH2a : 4 * (H : ℝ) ^ 2 * Real.log N ≤ N := by
    have := mul_le_mul_of_nonneg_left hlN2 (show (0 : ℝ) ≤ 4 * (H : ℝ) ^ 2 by positivity)
    linarith
  have hH2b : 4 * (H : ℝ) ^ 2 ≤ N := by
    have := mul_le_mul_of_nonneg_left hlN1 (show (0 : ℝ) ≤ 4 * (H : ℝ) ^ 2 by positivity)
    linarith
  have hs1 : (H : ℝ) * Real.sqrt (4 * N * Real.log N) ≤ N := by
    apply le_of_pow_le_pow_left₀ two_ne_zero hN0.le
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : (H : ℝ) ^ 2 * (4 * N * Real.log N) = N * (4 * (H : ℝ) ^ 2 * Real.log N) := by ring
    rw [this, sq (N : ℝ)]
    exact mul_le_mul_of_nonneg_left hH2a hN0.le
  have hs2 : (H : ℝ) * Real.sqrt (1 + N / 2) ≤ N := by
    apply le_of_pow_le_pow_left₀ two_ne_zero hN0.le
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h4 : (H : ℝ) ^ 2 ≤ N / 4 := by linarith
    have := mul_le_mul_of_nonneg_right h4 (show (0 : ℝ) ≤ 1 + N / 2 by positivity)
    nlinarith
  set a := Real.log (2 * N / H) with ha
  have ha2 : Real.log 2 ≤ a := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hH0]; linarith
  have hl2 := Real.log_two_gt_d9
  have hdiv : |wsum N H H| ≤ H + 2 * (8 * N + 8 * N + H) + 48 * K₁ * N * (1 + a) ^ 2 := by
    have h := htot
    have e : (H : ℝ) ^ 2 + 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N)
        + 8 * Real.sqrt (1 + N / 2) + 1) + 48 * K₁ * H * N * (1 + a) ^ 2
        = H * (H + 2 * (8 * (H * Real.sqrt (4 * N * Real.log N)) + 8 * (H * Real.sqrt (1 + N / 2)) + H)
          + 48 * K₁ * N * (1 + a) ^ 2) := by ring
    rw [e] at h
    have h' := le_of_mul_le_mul_left h hH0
    nlinarith
  have hfin : (H : ℝ) + 2 * (8 * N + 8 * N + H) + 48 * K₁ * N * (1 + a) ^ 2
      ≤ (140 + 432 * K₁) * N * a ^ 2 := by
    have h1 : (1 + a) ^ 2 ≤ 9 * a ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 4 * a ^ 2 := by nlinarith
    have h3 : 48 * K₁ * N * (1 + a) ^ 2 ≤ 432 * K₁ * N * a ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 48 * K₁ * N by positivity); nlinarith
    have h4 : (H : ℝ) + 2 * (8 * N + 8 * N + H) ≤ 35 * N := by linarith
    have h5 : 35 * (N : ℝ) ≤ 140 * N * a ^ 2 := by nlinarith
    nlinarith
  linarith

/-- The printed Prop `Theorem2bP` holds under RH on the range `2H(log N + 1) ≤ √N`, `N ≥ 10^20`. -/
theorem theorem2bP_short (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ N H : ℕ, (10 : ℝ) ^ 20 ≤ N →
    1 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      |wsum N H H| ≤ K * N * Real.log (2 * (N : ℝ) / H) ^ 2 := by
  obtain ⟨K, _, h⟩ := theorem2b_short hRH
  exact ⟨K, h⟩

/-- Vacuity check: the range of `theorem2b_short` is not empty, `N = 10^20`, `H = 1`. -/
theorem theorem2b_short_range_nonempty :
    2 * ((1 : ℕ) : ℝ) * (Real.log (((10 ^ 20 : ℕ) : ℝ)) + 1) ≤ Real.sqrt (((10 ^ 20 : ℕ) : ℝ)) := by
  have h10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
  have hl : Real.log (((10 ^ 20 : ℕ) : ℝ)) = 20 * Real.log 10 := by
    rw [show (((10 ^ 20 : ℕ) : ℝ)) = (10 : ℝ) ^ 20 by push_cast; ring, Real.log_pow]; norm_num
  have hs : Real.sqrt (((10 ^ 20 : ℕ) : ℝ)) = 10 ^ 10 := by
    rw [show (((10 ^ 20 : ℕ) : ℝ)) = (10 ^ 10) ^ 2 by push_cast; ring]
    exact Real.sqrt_sq (by norm_num)
  rw [hl, hs]; push_cast; nlinarith

end LeanLab.LZCesaroShort

