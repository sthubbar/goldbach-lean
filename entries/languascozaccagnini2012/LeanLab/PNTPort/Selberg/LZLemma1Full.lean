module

public import LeanLab.PNTPort.Selberg.LZLemma1RangeC
public import LeanLab.PNTPort.Selberg.LZTiny

/-!
# P0058 Lemma 1 from RH alone, every `ξ ∈ [0, 1/2]`

Lab proof, unit U-6200, CLOUD 20261020T0817Z-cloud38, T2. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only.

`lz_lemma1_explicit`, for every `N ≥ 1`, and `lz_lemma1_of_RH : RiemannHypothesis →
LeanLab.LZCesaroShort.Lemma1`: the lab's statement of
Languasco-Zaccagnini 2016, arXiv 1606.00869, Lemma 1, the one P0058 cites from their 2012 paper:
`∫_{-ξ}^{ξ} |S̃(α) - 1/z|² dα ≤ K N ξ (1 + log²(2Nξ))` for every `N ≥ 1` and `0 ≤ ξ ≤ 1/2`.
For `ξ ≤ 1/N` by `lz_lemma1_tiny`; above, by `lz_lemma1_range_c` at `L = ⌊1/(2ξ)⌋`.
Known mathematics; the lab now proves it from RH with no other cited input.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory

/-- `log x ≤ 2 √x` for `x > 0`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num
  linarith

set_option maxHeartbeats 2000000 in
/-- **Languasco-Zaccagnini Lemma 1 from RH, for every `N ≥ 1`.** -/
theorem lz_lemma1_explicit (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 1 ≤ N → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 / 2 →
    ∫ α in (-ξ)..ξ, ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2
      ≤ K * N * ξ * (1 + Real.log (2 * N * ξ) ^ 2) := by
  obtain ⟨C1, hC1, hr⟩ := lz_lemma1_range_c hRH
  obtain ⟨C2, hC2, ht⟩ := lz_lemma1_tiny hRH
  refine ⟨C2 + 306 * C1, by positivity, fun N hN ξ hξ0 hξ1 => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set ℓ := Real.log (2 * N * ξ) with hℓ
  have hNξ : 0 ≤ (N : ℝ) * ξ := by positivity
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg _
  rcases le_or_gt ξ (1 / N) with hsm | hbig
  · -- tiny `ξ`
    refine (ht N hN ξ hξ0 hsm hξ1).trans ?_
    have h1 : C2 * N * ξ ≤ C2 * (N * ξ * (1 + ℓ ^ 2)) := by
      rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC2; nlinarith
    have h2 : 0 ≤ 306 * C1 * (N * ξ * (1 + ℓ ^ 2)) := by positivity
    nlinarith
  -- `ξ > 1/N`
  have hξpos : 0 < ξ := lt_of_le_of_lt (by positivity) hbig
  have hNξ1 : 1 < N * ξ := by
    have := mul_lt_mul_of_pos_left hbig hN0
    rwa [mul_one_div_cancel hN0.ne'] at this
  set x := 1 / (2 * ξ) with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by positivity)]; linarith
  have hxN : x ≤ N := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  set L := ⌊x⌋₊ with hL
  have hLx : (L : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxL : x < L + 1 := Nat.lt_floor_add_one x
  have hL1 : 1 ≤ L := Nat.le_floor (by exact_mod_cast hx1)
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := hLx.trans hxN
    exact_mod_cast this
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) < L := by linarith
  -- `ξ ≤ 1/(2L)` and `1/L ≤ 4ξ`
  have hξL : ξ ≤ 1 / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    have : (L : ℝ) * (2 * ξ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hLx (by positivity : (0 : ℝ) ≤ 2 * ξ)
      rwa [hx, one_div_mul_cancel (by positivity)] at this
    linarith
  have hL4 : 1 < 4 * L * ξ := by
    have h : x * (2 * ξ) = 1 := by rw [hx]; field_simp
    have : x < 2 * L := by linarith
    nlinarith
  -- monotonicity in the interval
  have hmono : ∫ α in (-ξ)..ξ, ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2
      ≤ ∫ α in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2 := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) hξL
      (Filter.Eventually.of_forall fun α => sq_nonneg _) ?_
    exact (continuous_lz_integrand (by omega)).intervalIntegrable _ _
  refine hmono.trans ((hr N L hL1 hLN).trans ?_)
  -- the three terms
  set y := (N : ℝ) / L with hy
  have hy0 : 0 < y := by positivity
  have hyl : 2 * N * ξ ≤ y := by
    rw [hy, le_div_iff₀ hL0]
    have := mul_le_mul_of_nonneg_left hξL (by positivity : (0 : ℝ) ≤ 2 * N * L)
    have e : 2 * (N : ℝ) * L * (1 / (2 * L)) = N := by field_simp
    nlinarith
  have hyu : y ≤ 4 * N * ξ := by
    rw [hy, div_le_iff₀ hL0]; nlinarith
  have h2Nξ : 1 ≤ 2 * N * ξ := by linarith
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg h2Nξ
  have hlogy : Real.log y ≤ ℓ + 1 := by
    have h1 : Real.log y ≤ Real.log (4 * N * ξ) := Real.log_le_log hy0 hyu
    have e : (4 : ℝ) * N * ξ = 2 * (2 * N * ξ) := by ring
    rw [e, Real.log_mul (by norm_num) (by positivity)] at h1
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    rw [hℓ]; linarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  -- term 1
  have t1 : (N : ℝ) * (Real.log (N / L) + 3) ^ 2 / L ≤ 128 * (N * ξ * (1 + ℓ ^ 2)) := by
    have e : (N : ℝ) * (Real.log (N / L) + 3) ^ 2 / L = y * (Real.log y + 3) ^ 2 := by
      rw [hy]; ring
    rw [e]
    have hA : (Real.log y + 3) ^ 2 ≤ 2 * ℓ ^ 2 + 32 := by
      have h1 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log y + 3) (by linarith : Real.log y + 3 ≤ ℓ + 4) 2
      nlinarith [sq_nonneg (ℓ - 4)]
    have : y * (Real.log y + 3) ^ 2 ≤ 4 * N * ξ * (2 * ℓ ^ 2 + 32) :=
      mul_le_mul hyu hA (by positivity) (by positivity)
    nlinarith
  -- term 2
  have t2 : (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 ≤ 176 * (N * ξ * (1 + ℓ ^ 2)) := by
    have hsL : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL1r
    have hlogN : Real.log N = Real.log y + Real.log L := by
      rw [hy, Real.log_div hN0.ne' hL0.ne']; ring
    have hlogL := log_le_two_sqrt hL0
    have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1r
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
    have hG : (Real.log N + 2) ^ 2 ≤ 2 * (ℓ + 3) ^ 2 + 8 * L := by
      rw [hlogN]
      have : Real.log y + Real.log L + 2 ≤ (ℓ + 3) + 2 * Real.sqrt L := by linarith
      nlinarith [sq_nonneg (ℓ + 3 - 2 * Real.sqrt L)]
    have e : (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 =
        y * ((Real.log N + 2) ^ 2 / (Real.sqrt L * L)) := by
      rw [hy]; field_simp
    rw [e]
    have hq : (Real.log N + 2) ^ 2 / (Real.sqrt L * L) ≤ 44 * (1 + ℓ ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 2 * (ℓ + 3) ^ 2 ≤ 2 * (ℓ + 3) ^ 2 * (Real.sqrt L * L) := by
        have : 1 ≤ Real.sqrt L * L := by nlinarith
        nlinarith [sq_nonneg (ℓ + 3)]
      have h2 : 8 * (L : ℝ) ≤ 8 * (Real.sqrt L * L) := by nlinarith
      have h3 : 2 * (ℓ + 3) ^ 2 + 8 ≤ 44 * (1 + ℓ ^ 2) := by nlinarith
      have h4 : 0 ≤ Real.sqrt L * L := by positivity
      nlinarith
    have : y * ((Real.log N + 2) ^ 2 / (Real.sqrt L * L)) ≤ 4 * N * ξ * (44 * (1 + ℓ ^ 2)) :=
      mul_le_mul hyu hq (by positivity) (by positivity)
    nlinarith
  -- term 3
  have t3 : (1 : ℝ) ≤ 2 * (N * ξ * (1 + ℓ ^ 2)) := by nlinarith
  have hsum := add_le_add (add_le_add t1 t2) t3
  have hfin : C1 * ((N : ℝ) * (Real.log (N / L) + 3) ^ 2 / L
      + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 + 1)
      ≤ C1 * (306 * (N * ξ * (1 + ℓ ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ hC1; linarith
  have : 0 ≤ C2 * (N * ξ * (1 + ℓ ^ 2)) := by positivity
  nlinarith

/-- **Languasco-Zaccagnini Lemma 1 from RH**, the lab's cited Prop, with `N₀ = 1`. -/
theorem lz_lemma1_of_RH (hRH : RiemannHypothesis) : LeanLab.LZCesaroShort.Lemma1 := by
  obtain ⟨K, -, h⟩ := lz_lemma1_explicit hRH
  exact ⟨K, 1, fun N hN => h N hN⟩

end LeanLab.PNTPort.Selberg

