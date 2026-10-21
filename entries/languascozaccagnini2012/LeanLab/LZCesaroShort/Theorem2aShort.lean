module

public import LeanLab.LZCesaroShort.Theorem2bShort
public import LeanLab.LZCesaroShort.CircleY
public import LeanLab.LZCesaroShort.Layer2

/-!
# P0058 Theorem 2 eq. (2), under RH, for `2H(log N + 1) ≤ √N`

Lab proof, unit U-6111, CLOUD 20261020T0618Z-cloud36. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `lemma1_real`. Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 2, Theorem 2 eq. (2): under RH, uniformly for `y ∈ [−H, H)`,
`|Σ_{N−H ≤ n ≤ N+y} e^{−n/N}(R(n) − (2ψ(n) − n))(1 − |n − N|/H)| ≪ N (log N)² log(2H)`.

* `I3_boundY`: `‖∫ T_H(N, y; −α) R̃(α)² dα‖ ≤ 18 K₁ H N (1 + log N)² log(2H)`, eq. (29), from
  Lemma 5's `3H min(H, 1/(2‖α‖))` and the layers of `Layer2.lean`;
* `theorem2a_short`: **under RH**, `|wsum N H y| ≤ K N (log N)² log(2H)` for `N ≥ 10^20`,
  `H ≥ 1` with `2H(log N + 1) ≤ √N` and every real `y ∈ [−H, H)`, the printed `Theorem2a` on
  that range.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

set_option maxHeartbeats 4000000 in
/-- **`I₃` for `y ∈ [−H, H)`, eq. (29), under RH.** -/
theorem I3_boundY (hRH : RiemannHypothesis) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧
    ∀ N H : ℕ, ∀ y : ℝ, 2 ≤ N → 1 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      -(H : ℝ) ≤ y → y < H →
      ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) ^ 2‖
        ≤ 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * Real.log (2 * H) := by
  obtain ⟨K₁, hK₁, hl1⟩ := lemma1_real hRH
  refine ⟨K₁, hK₁, fun N H y hN hH hHs hy0 hyH => ?_⟩
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
  have hTc := continuous_THY_neg N H y
  set K := Nat.log 2 H + 1 with hKdef
  have hK : (H : ℝ) ≤ 2 ^ K := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) H
    exact_mod_cast this.le
  have h1 : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) ^ 2‖
      ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖TH N H y (-α)‖ * f α := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
    congr 1; ext α; rw [norm_mul, norm_pow]
  have h2 := integral_G_le (H := H) (K := K) hH hK hfc (fun α => by positivity) hTc.norm
    (c := 3 * H) (by positivity)
    (fun α hα => by
      have hab : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
      rw [← G_neg hab]; exact lemma5_partial hH hHNn hy0 hyH (-α))
  have hlo : (Real.log N + 1) / Real.sqrt N ≤ 1 / (2 * H) := by
    rw [div_le_div_iff₀ hsN (by positivity)]; linarith
  have hwin : ∀ k ∈ range (K + 1), 3 * (H : ℝ) * (2 * (H : ℝ) / 2 ^ k) * ∫ α in (-xi H k)..(xi H k), f α
      ≤ 6 * K₁ * H * N * (1 + Real.log N) ^ 2 := by
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
    have h2N : 1 ≤ 2 * N * xi H k := by
      have : 2 * (N : ℝ) * (1 / (2 * H)) ≤ 2 * N * xi H k :=
        mul_le_mul_of_nonneg_left hx0 (by positivity)
      have e : 2 * (N : ℝ) * (1 / (2 * H)) = N / H := by field_simp
      rw [e] at this
      have : (1 : ℝ) ≤ N / H := by rw [le_div_iff₀ hH0]; linarith
      linarith
    have hlg0 : 0 ≤ Real.log (2 * N * xi H k) := Real.log_nonneg h2N
    have hlg : Real.log (2 * N * xi H k) ≤ Real.log N := by
      apply Real.log_le_log (by positivity)
      have := xi_le_half H k
      nlinarith
    have hsq' : (1 + Real.log (2 * N * xi H k)) ^ 2 ≤ (1 + Real.log N) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hint : ∫ α in (-xi H k)..(xi H k), f α ≤ K₁ * N * ((2 : ℝ) ^ k / H) * (1 + Real.log N) ^ 2 := by
      refine hl.trans ?_
      have := mul_le_mul hxle hsq' (by positivity) (by positivity)
      calc K₁ * N * xi H k * (1 + Real.log (2 * N * xi H k)) ^ 2
          = K₁ * N * (xi H k * (1 + Real.log (2 * N * xi H k)) ^ 2) := by ring
        _ ≤ K₁ * N * ((2 : ℝ) ^ k / H * (1 + Real.log N) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    calc 3 * (H : ℝ) * (2 * (H : ℝ) / 2 ^ k) * ∫ α in (-xi H k)..(xi H k), f α
        ≤ 3 * (H : ℝ) * (2 * (H : ℝ) / 2 ^ k) * (K₁ * N * ((2 : ℝ) ^ k / H) * (1 + Real.log N) ^ 2) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = 6 * K₁ * H * N * (1 + Real.log N) ^ 2 := by field_simp; ring
  have h3 := sum_le_sum hwin
  rw [sum_const, card_range, nsmul_eq_mul] at h3
  -- `K + 1 ≤ 3 log(2H)`
  have hKb : ((K + 1 : ℕ) : ℝ) ≤ 3 * Real.log (2 * H) := by
    have hp : 2 ^ Nat.log 2 H ≤ H := Nat.pow_log_le_self 2 (by omega)
    have hp' : ((2 : ℝ)) ^ (Nat.log 2 H) ≤ H := by exact_mod_cast hp
    have hlm : (Nat.log 2 H : ℝ) * Real.log 2 ≤ Real.log H := by
      have := Real.log_le_log (by positivity) hp'
      rwa [Real.log_pow] at this
    have hlH0 : 0 ≤ Real.log H := Real.log_nonneg hH1
    have hl2 := Real.log_two_gt_d9
    have e : Real.log (2 * H) = Real.log 2 + Real.log H := Real.log_mul (by norm_num) (by positivity)
    rw [e, hKdef]; push_cast
    nlinarith
  have hpos : 0 ≤ 6 * K₁ * H * N * (1 + Real.log N) ^ 2 := by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ ((K + 1 : ℕ) : ℝ) * (6 * K₁ * H * N * (1 + Real.log N) ^ 2) := by
        convert h3 using 1
    _ ≤ 3 * Real.log (2 * H) * (6 * K₁ * H * N * (1 + Real.log N) ^ 2) :=
        mul_le_mul_of_nonneg_right hKb hpos
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **P0058 Theorem 2 eq. (2) as printed, under RH, for `2H(log N + 1) ≤ √N`.** -/
theorem theorem2a_short (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N H : ℕ, ∀ y : ℝ, (10 : ℝ) ^ 20 ≤ N → 1 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      -(H : ℝ) ≤ y → y < H →
      |wsum N H y| ≤ K * N * Real.log N ^ 2 * Real.log (2 * H) := by
  obtain ⟨K₁, hK₁, hI3⟩ := I3_boundY hRH
  refine ⟨70 + 72 * K₁, by positivity, fun N H y hN hH hHs hy0 hyH => ?_⟩
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
  set T : ℝ → ℂ := fun α => TH N H y (-α)
  set Rt : ℝ → ℂ := fun α => St N α - 1 / zz N α
  set iz : ℝ → ℂ := fun α => 1 / zz N α
  have hTc : Continuous T := continuous_THY_neg N H y
  have hStc : Continuous (St N) := continuous_St hNn
  have hizc : Continuous iz := continuous_const.div (continuous_zz N) (zz_ne_zero hNn)
  have hRtc : Continuous Rt := hStc.sub hizc
  have hpt : ∀ α, St N α ^ 2 * TH N H y (-α)
      = T α * iz α ^ 2 + 2 * (T α * Rt α * iz α) + T α * Rt α ^ 2 := by
    intro α; simp only [T, Rt, iz]; ring
  have hQ := Q_eqY (H := H) (y := y) hNn
  have hdec : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), St N α ^ 2 * TH N H y (-α)
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
  have b1 := I1_boundY (y := y) hNn hHNn
  have b2 := I2_boundY (y := y) hN hHNn
  have b3 := hI3 N H y hN2n hH hHs hy0 hyH
  -- the real identity
  set M1 : ℝ := ∑ n ∈ Fy N H y, tw N H n * (n * Real.exp (-n / N))
  set M2 : ℝ := ∑ n ∈ Fy N H y, tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n))
  set Qr : ℝ := ∑ n ∈ Fy N H y, tw N H n * Real.exp (-n / N) * R n
  have hw : (H : ℝ) * wsum N H y = Qr - M1 - 2 * M2 := by
    unfold wsum
    rw [mul_sum]
    simp only [Qr, M1, M2, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [w_eq hH]
    unfold tw
    rw [neg_div]
    field_simp
    ring
  have hwC : (((H : ℝ) * wsum N H y : ℝ) : ℂ)
      = ((∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
        + (2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
    have : ((Qr : ℝ) : ℂ) = (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2)
        + 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α)
        + ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2 := by
      rw [← hdec, hQ]; simp only [Qr]; push_cast; rfl
    rw [hw]; push_cast; rw [this]; ring
  have hM1 : ((M1 : ℝ) : ℂ) = ∑ n ∈ Fy N H y,
      ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ) := by simp only [M1]; push_cast; rfl
  have hM2 : ((M2 : ℝ) : ℂ) = ∑ n ∈ Fy N H y,
      ((tw N H n * (Real.exp (-(n / N)) * (ψ (n : ℝ) - n)) : ℝ) : ℂ) := by
    simp only [M2]; push_cast; rfl
  have hA : ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ)‖ ≤ (H : ℝ) ^ 2 := by
    rw [hM1]; exact b1
  have hB : ‖2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ)‖
      ≤ 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N) + 8 * Real.sqrt (1 + N / 2) + 1) := by
    rw [hM2]; exact b2
  have hC : ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2‖
      ≤ 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * Real.log (2 * H) := b3
  have htot : (H : ℝ) * |wsum N H y| ≤ (H : ℝ) ^ 2
      + 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N) + 8 * Real.sqrt (1 + N / 2) + 1)
      + 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * Real.log (2 * H) := by
    have h := norm_add₃_le (a := (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * iz α ^ 2) - (M1 : ℂ))
      (b := 2 * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α * iz α) - 2 * (M2 : ℂ))
      (c := ∫ α in (-(1 / 2 : ℝ))..(1 / 2), T α * Rt α ^ 2)
    rw [← hwC, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hH0] at h
    linarith
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
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := le_trans (by norm_num) hN
    linarith
  have hl2 := Real.log_two_gt_d9
  have hlH : Real.log 2 ≤ Real.log (2 * H) := Real.log_le_log (by norm_num) (by linarith)
  set L := Real.log (2 * H)
  have hdiv : |wsum N H y| ≤ H + 2 * (8 * N + 8 * N + H) + 18 * K₁ * N * (1 + Real.log N) ^ 2 * L := by
    have h := htot
    have e : (H : ℝ) ^ 2 + 2 * (H : ℝ) ^ 2 * (8 * Real.sqrt (4 * N * Real.log N)
        + 8 * Real.sqrt (1 + N / 2) + 1) + 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * L
        = H * (H + 2 * (8 * (H * Real.sqrt (4 * N * Real.log N)) + 8 * (H * Real.sqrt (1 + N / 2)) + H)
          + 18 * K₁ * N * (1 + Real.log N) ^ 2 * L) := by ring
    rw [e] at h
    have h' := le_of_mul_le_mul_left h hH0
    nlinarith
  have hL0 : (1 : ℝ) / 2 ≤ L := by linarith
  have hsqL : (1 + Real.log N) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
  have hP : 1 ≤ Real.log N ^ 2 := by nlinarith
  have h3 : 18 * K₁ * N * (1 + Real.log N) ^ 2 * L ≤ 72 * K₁ * N * Real.log N ^ 2 * L := by
    have := mul_le_mul_of_nonneg_left hsqL (show (0 : ℝ) ≤ 18 * K₁ * N by positivity)
    have hL0' : 0 ≤ L := by linarith
    nlinarith
  have h4 : (H : ℝ) + 2 * (8 * N + 8 * N + H) ≤ 35 * N := by linarith
  have h5 : 35 * (N : ℝ) ≤ 70 * N * Real.log N ^ 2 * L := by
    have : (1 : ℝ) / 2 ≤ Real.log N ^ 2 * L := by nlinarith
    nlinarith
  nlinarith

end LeanLab.LZCesaroShort

