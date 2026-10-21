module

public import LeanLab.LZCesaroShort.Theorem2aShort
public import LeanLab.PNTPort.Selberg.LZLemma1Full

/-!
# P0058 Lemma 1 PROVED from RH, and `I₃` for every `H ≤ N`

Lab proof, unit U-6201, CLOUD 20261020T0817Z-cloud38, T1. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `PNTPort.Selberg.lz_lemma1_explicit`. Binary Goldbach is OPEN.

* `lz_lemma1_proved : RiemannHypothesis → Lemma1`: the cited `lz_lemma1` of
  `Lemma13Statements.lean` is now a theorem, with `N₀ = 1`;
* `lemma1_full`: under RH, for `N ≥ 1` and `1/(2N) ≤ ξ ≤ 1/2`,
  `∫_{-ξ}^{ξ} ‖S̃(α) − 1/z‖² dα ≤ K N ξ (1 + log(2Nξ))²`, the paper's shape, which replaces
  `lemma1_real` and its floor `ξ ≥ (log N + 1)/√N`;
* `I3_boundY_full`: `I3_boundY` of `Theorem2aShort.lean` with `H ≤ N` in place of
  `2H(log N + 1) ≤ √N`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

/-- **Lemma 1 of P0058, PROVED from RH.** -/
theorem lz_lemma1_proved : RiemannHypothesis → Lemma1 := LeanLab.PNTPort.Selberg.lz_lemma1_of_RH

/-- **P0058 Lemma 1 in the paper's shape, under RH, for `ξ ≥ 1/(2N)`.** -/
theorem lemma1_full (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 1 ≤ N → ∀ ξ : ℝ, 1 / (2 * (N : ℝ)) ≤ ξ → ξ ≤ 1 / 2 →
      ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2 ≤ K * N * ξ * (1 + Real.log (2 * N * ξ)) ^ 2 := by
  obtain ⟨K, hK, h⟩ := LeanLab.PNTPort.Selberg.lz_lemma1_explicit hRH
  refine ⟨K, hK, fun N hN ξ hlo hhi => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hlo
  have h1 : 1 ≤ 2 * N * ξ := by
    have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ 2 * N)
    rwa [mul_one_div_cancel (by positivity)] at this
  have hl0 : 0 ≤ Real.log (2 * N * ξ) := Real.log_nonneg h1
  refine (h N hN ξ hξ0.le hhi).trans ?_
  have : 1 + Real.log (2 * N * ξ) ^ 2 ≤ (1 + Real.log (2 * N * ξ)) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

set_option maxHeartbeats 4000000 in
/-- **`I₃` for `y ∈ [−H, H)`, eq. (29), under RH, every `H < N`.** -/
theorem I3_boundY_full (hRH : RiemannHypothesis) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧
    ∀ N H : ℕ, ∀ y : ℝ, 2 ≤ N → 1 ≤ H → H ≤ N →
      -(H : ℝ) ≤ y → y < H →
      ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (St N α - 1 / zz N α) ^ 2‖
        ≤ 18 * K₁ * H * N * (1 + Real.log N) ^ 2 * Real.log (2 * H) := by
  obtain ⟨K₁, hK₁, hl1⟩ := lemma1_full hRH
  refine ⟨K₁, hK₁, fun N H y hN hH hHNlt hy0 hyH => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNn : 1 ≤ N := by omega
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hHN : (H : ℝ) ≤ N := by exact_mod_cast hHNlt
  have hHNn : H ≤ N := hHNlt
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
  have hlo : 1 / (2 * (N : ℝ)) ≤ 1 / (2 * H) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
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
    have hl := hl1 N hNn (xi H k) (hlo.trans hx0) (xi_le_half H k)
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

end LeanLab.LZCesaroShort

