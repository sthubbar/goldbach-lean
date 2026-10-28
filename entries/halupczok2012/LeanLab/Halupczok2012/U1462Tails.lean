module

public import LeanLab.Halupczok2012.U1462Pointwise

/-!
# P0077 Halupczok 2012, `SingSeriesTails` PROVED, unit U-1462

AI wrote the Lean code, Claude, run 20261022T0403Z-7595. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

* `tail_sum_sq_le`: the TAIL sum, squared, is at most
  `log² n · z^{-2σ} Kc³ (Y₁ + n^{2σ}) · (Y₁ (1 + log N)³ + N²)`; by Cauchy-Schwarz over `q`,
  `sum_q_abs_sq_le` and `divisor_moment` of U-1439, `tail_pointwise` and `sum_Hs_sq_le`.
* `euler_sum_le`: the EULER sum is at most `Y₁ z^{-σ} Kc² (1 + log N)`; by `euler_pointwise` and
  `sum_Hs_div_totient_le`.
* `singSeriesTails_holds : SingSeriesTails`. PROVED, no cited input, with `σ = 1/12` and
  `D = 12 (A + 3)`.
* `singSeriesApprox_holds : SingSeriesApprox`. PROVED.
* `theorem2Zeroed_U1462`: the F-0008 repair CONDITIONAL ON `Theorem3` and `Theorem5` only.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset Filter Topology

/-- The window `X₁ < m ≤ X₁ + Y₁`, `m ≤ n`, without the congruence. -/
noncomputable def Wb (n : ℕ) (X1 Y1 : ℝ) : Finset ℕ :=
  (range (n + 1)).filter (fun m => X1 < m ∧ (m : ℝ) ≤ X1 + Y1)

theorem W1_eq (n : ℕ) (X1 Y1 : ℝ) (q : ℕ) (a : ℤ) :
    W1 n X1 Y1 q a = (Wb n X1 Y1).filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]) := by
  unfold W1 Wb; rw [filter_filter]; simp only [and_assoc]

/-- **The TAIL sum, squared.** -/
theorem tail_sum_sq_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) {n : ℕ} {X1 Y1 z : ℝ}
    (hY : 0 ≤ Y1) (hz : 0 < z) (hzX : z ≤ X1) (hn : X1 + Y1 < n) (N : ℕ) (a : ℤ) :
    (∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      ∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Zsq z X1, gS n s m|) ^ 2 ≤
    (Real.log n ^ 2 * (z ^ (-σ)) ^ 2 * Kc σ ^ 3 * (Y1 + (n : ℝ) ^ (2 * σ))) *
      (Y1 * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2) := by
  set w : ℕ → ℝ := fun m => Real.log m * |S (n - m) - ∑ s ∈ Zsq z X1, gS n s m| with hw
  have hw0 : ∀ m, 0 ≤ w m := fun m => mul_nonneg (Real.log_natCast_nonneg m) (abs_nonneg _)
  have hW : ∀ m ∈ Wb n X1 Y1, X1 < m ∧ (m : ℝ) ≤ X1 + Y1 ∧ m < n := by
    intro m hm
    simp only [Wb, mem_filter] at hm
    refine ⟨hm.2.1, hm.2.2, ?_⟩
    have : (m : ℝ) < n := by linarith [hm.2.2]
    exact_mod_cast this
  have hW' : ∀ m ∈ Wb n X1 Y1, X1 < m ∧ (m : ℝ) ≤ X1 + Y1 :=
    fun m hm => ⟨(hW m hm).1, (hW m hm).2.1⟩
  have step0 : ∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      ∑ m ∈ W1 n X1 Y1 q a, w m ≤
      ∑ q ∈ Icc 1 N, |∑ m ∈ (Wb n X1 Y1).filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]), w m| := by
    calc _ ≤ ∑ q ∈ Icc 1 N, ∑ m ∈ W1 n X1 Y1 q a, w m :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun q _ _ => sum_nonneg (fun m _ => hw0 m))
      _ = _ := by
          apply sum_congr rfl; intro q _
          rw [W1_eq, abs_of_nonneg (sum_nonneg (fun m _ => hw0 m))]
  have hL0 : 0 ≤ ∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      ∑ m ∈ W1 n X1 Y1 q a, w m := sum_nonneg (fun q _ => sum_nonneg (fun m _ => hw0 m))
  have hCS := sum_q_abs_sq_le (Wb n X1 Y1) w N a
  have hDM := divisor_moment hY hW' N a
  have step1 : ∑ m ∈ Wb n X1 Y1, w m ^ 2 ≤
      Real.log n ^ 2 * (z ^ (-σ)) ^ 2 * Kc σ ^ 3 * (Y1 + (n : ℝ) ^ (2 * σ)) := by
    have hm : ∀ m ∈ Wb n X1 Y1, w m ^ 2 ≤
        Real.log n ^ 2 * (z ^ (-σ)) ^ 2 * Kc σ ^ 2 * Hs σ (n - m) ^ 2 := by
      intro m hm
      obtain ⟨hxm, -, hmn⟩ := hW m hm
      have hlog : Real.log m ≤ Real.log n := by
        have hm0 : (0 : ℝ) < m := by
          have : (0 : ℝ) < m := by
            by_contra h; push_neg at h
            have : (m : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
            have hz' : z ≤ X1 := hzX
            linarith
          exact this
        exact Real.log_le_log hm0 (by exact_mod_cast hmn.le)
      have ht := tail_pointwise hσ hσ2 hmn hz hzX
      have hb : w m ≤ Real.log n * (z ^ (-σ) * (Kc σ * Hs σ (n - m))) :=
        mul_le_mul hlog ht (abs_nonneg _) (le_trans (Real.log_natCast_nonneg m) hlog)
      calc w m ^ 2 ≤ (Real.log n * (z ^ (-σ) * (Kc σ * Hs σ (n - m)))) ^ 2 :=
            pow_le_pow_left₀ (hw0 m) hb 2
        _ = _ := by ring
    calc _ ≤ ∑ m ∈ Wb n X1 Y1, Real.log n ^ 2 * (z ^ (-σ)) ^ 2 * Kc σ ^ 2 * Hs σ (n - m) ^ 2 :=
          sum_le_sum hm
      _ = Real.log n ^ 2 * (z ^ (-σ)) ^ 2 * Kc σ ^ 2 * ∑ m ∈ Wb n X1 Y1, Hs σ (n - m) ^ 2 := by
          rw [mul_sum]
      _ ≤ Real.log n ^ 2 * (z ^ (-σ)) ^ 2 * Kc σ ^ 2 * (Kc σ * (Y1 + (n : ℝ) ^ (2 * σ))) :=
          mul_le_mul_of_nonneg_left (sum_Hs_sq_le hσ hσ2 hY hW) (by positivity)
      _ = _ := by ring
  have hDq0 : 0 ≤ ∑ m ∈ Wb n X1 Y1, ((Dq N a m : ℕ) : ℝ) ^ 2 := sum_nonneg (fun m _ => sq_nonneg _)
  calc _ ≤ (∑ q ∈ Icc 1 N,
        |∑ m ∈ (Wb n X1 Y1).filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD q]), w m|) ^ 2 :=
        pow_le_pow_left₀ hL0 step0 2
    _ ≤ (∑ m ∈ Wb n X1 Y1, w m ^ 2) * ∑ m ∈ Wb n X1 Y1, ((Dq N a m : ℕ) : ℝ) ^ 2 := hCS
    _ ≤ _ := mul_le_mul step1 hDM hDq0 (by
          have : 0 ≤ (n : ℝ) ^ (2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          have : 0 ≤ Kc σ := (Kc_pos σ).le
          have : 0 ≤ z ^ (-σ) := Real.rpow_nonneg hz.le _
          positivity)

/-- **The EULER sum.** -/
theorem euler_sum_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) {n : ℕ} {X1 Y1 z : ℝ}
    (hY : 0 ≤ Y1) (hz : 0 < z) (hzX : z ≤ X1) (N : ℕ) (a : ℤ) :
    ∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |∑ s ∈ Zsq z X1, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, gS n s b -
        T n q a * Y1| ≤ Y1 * z ^ (-σ) * Kc σ ^ 2 * (1 + Real.log N) := by
  have hz0 : 0 ≤ z ^ (-σ) := Real.rpow_nonneg hz.le _
  have hK0 : 0 ≤ Kc σ := (Kc_pos σ).le
  have hterm : ∀ q ∈ Icc 1 N, 0 ≤ Y1 * (z ^ (-σ) * (Kc σ * Hs σ q) / (q.totient : ℝ)) := by
    intro q _
    have := Hs_nonneg σ q
    positivity
  calc _ ≤ ∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        Y1 * (z ^ (-σ) * (Kc σ * Hs σ q) / (q.totient : ℝ)) := by
        apply sum_le_sum
        intro q hq
        rw [mem_filter, mem_Icc] at hq
        exact euler_pointwise hσ hσ2 (by omega) hq.2 hz hzX hY
    _ ≤ ∑ q ∈ Icc 1 N, Y1 * (z ^ (-σ) * (Kc σ * Hs σ q) / (q.totient : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q hq _ => hterm q hq)
    _ = Y1 * z ^ (-σ) * Kc σ * ∑ q ∈ Icc 1 N, Hs σ q / (q.totient : ℝ) := by
        rw [mul_sum]; apply sum_congr rfl; intro q _; ring
    _ ≤ Y1 * z ^ (-σ) * Kc σ * (Kc σ * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (sum_Hs_div_totient_le hσ hσ2 N) (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **`SingSeriesTails` holds.** PROVED, no cited input. -/
theorem singSeriesTails_holds : SingSeriesTails := by
  intro A ε ε1 ε2 hA hε hε1 hε2
  set σ : ℝ := 1 / 12 with hσdef
  have hσ : 0 < σ := by norm_num
  have hσ2 : σ ≤ 1 / 2 := by norm_num
  set D : ℝ := 12 * (A + 3) with hD
  refine ⟨D, by rw [hD]; linarith, fun B hB c hc c7 hc7 a => ?_⟩
  have c0 := hc 0; have c1 := hc 1; have c2 := hc 2; have c3 := hc 3
  have c4 := hc 4; have c5 := hc 5; have c6 := hc 6
  set K := Kc σ with hKdef
  have hK1 : 1 ≤ K := one_le_Kc σ
  have hK0 : 0 < K := Kc_pos σ
  set kn : ℝ := (c 3 / c 0) ^ 2 + c 3 + (1 / c 1) ^ 2 + 1 + c 5 with hkn
  have hkn0 : 0 < kn := by rw [hkn]; positivity
  set kl : ℝ := |Real.log kn| + 2 with hkl
  set kN : ℝ := 2 + |Real.log (c 6 ^ 2 * c 3)| with hkN
  set k1 : ℝ := 1 + kn ^ (1 / 6 : ℝ) / c 2 with hk1
  have hk10 : 0 ≤ k1 := by
    rw [hk1]; have := Real.rpow_nonneg hkn0.le (1 / 6 : ℝ); positivity
  set M : ℝ := kl ^ 2 * K ^ 3 * k1 * (kN ^ 3 + c 6 ^ 2) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop D (by norm_num : (0 : ℝ) < 1 / 3)).def c2
  obtain ⟨Ya, hYa⟩ := eventually_atTop.mp hlo
  refine ⟨M + 1 + K ^ 2 * kN, max Ya (Real.exp 1), ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ ha
  obtain ⟨hn, hYX1, h0, hYX2, h1, h2, h3, hD0, hD1, hD2, hQ1, hQ2⟩ := hH
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hYe2 : Real.exp 1 ≤ Y2 := le_trans (le_max_right _ _) hY2
  have hYe1 : Real.exp 1 ≤ Y1 := le_trans (le_max_right _ _) hY1
  have hY2pos : 0 < Y2 := by linarith
  have hY1pos : 0 < Y1 := by linarith
  have hY21 : 1 ≤ Y2 := by linarith
  set L := Real.log Y2 with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe2
  have hL0 : 0 < L := by linarith
  have hX1 : 1 ≤ X1 := by linarith
  have hX2 : 1 ≤ X2 := by linarith
  -- `z = L^D ≤ X₁`
  set z := L ^ D with hzdef
  have hz : 0 < z := Real.rpow_pos_of_pos hL0 D
  have hY13 : Y2 ^ (1 / 3 : ℝ) ≤ Y2 ^ (1 / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hY21 (by linarith)
  have hzX : z ≤ X1 := by
    have h := hYa Y2 (le_trans (le_max_left _ _) hY2)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hY2pos.le _)] at h
    calc z ≤ |z| := le_abs_self z
      _ ≤ c 2 * Y2 ^ (1 / 3 : ℝ) := h
      _ ≤ c 2 * Y2 ^ (1 / 3 + ε) := mul_le_mul_of_nonneg_left hY13 c2.le
      _ ≤ Y1 := h2
      _ ≤ X1 := hYX1
  -- the window lies below `n`
  have hnX : X1 + Y1 < n := by have := mul_pos c4 hY2pos; linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  -- `n ≤ kn Y₂²`
  have hX1b : X1 ≤ (c 3 / c 0) ^ 2 * Y2 ^ 2 := by
    have hsq := le_sq_of_rpow c0 hX1 (by linarith) h0
    refine hsq.trans ?_
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ c0]
    calc Y1 ≤ c 3 * Y2 := h3
      _ = c 3 / c 0 * Y2 * c 0 := by field_simp
  have hX2b : X2 ≤ (1 / c 1) ^ 2 * Y2 ^ 2 := by
    have hsq := le_sq_of_rpow c1 hX2 (by linarith) h1
    refine hsq.trans (le_of_eq ?_)
    ring
  have hYY : Y2 ≤ Y2 ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hY2pos.le hY21
  have hnb : (n : ℝ) ≤ kn * Y2 ^ 2 := by
    rw [hkn]
    have : Y1 ≤ c 3 * Y2 ^ 2 := le_trans h3 (mul_le_mul_of_nonneg_left hYY c3.le)
    have : c 5 * Y2 ≤ c 5 * Y2 ^ 2 := mul_le_mul_of_nonneg_left hYY c5.le
    linarith
  -- `log n ≤ kl L`
  have hlogn : Real.log n ≤ kl * L := by
    have h := Real.log_le_log (by linarith) hnb
    rw [Real.log_mul hkn0.ne' (by positivity), Real.log_pow] at h
    have : Real.log kn ≤ |Real.log kn| := le_abs_self _
    have : |Real.log kn| ≤ |Real.log kn| * L := le_mul_of_one_le_right (abs_nonneg _) hL1
    rw [← hLdef] at h
    rw [hkl]; push_cast at h; linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- `Y₁ + n^{1/6} ≤ k1 Y₁`
  have hn6 : Y1 + (n : ℝ) ^ (2 * σ) ≤ k1 * Y1 := by
    have e : (2 * σ) = (1 / 6 : ℝ) := by rw [hσdef]; norm_num
    rw [e]
    have hb1 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (kn * Y2 ^ 2) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hnb (by norm_num)
    have hb2 : (kn * Y2 ^ 2) ^ (1 / 6 : ℝ) = kn ^ (1 / 6 : ℝ) * Y2 ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow hkn0.le (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hY2pos.le]
      norm_num
    have hb3 : Y2 ^ (1 / 3 : ℝ) ≤ Y1 / c 2 := by
      rw [le_div_iff₀ c2]; linarith [mul_le_mul_of_nonneg_left hY13 c2.le]
    have hkp : 0 ≤ kn ^ (1 / 6 : ℝ) := Real.rpow_nonneg hkn0.le _
    calc Y1 + (n : ℝ) ^ (1 / 6 : ℝ) ≤ Y1 + kn ^ (1 / 6 : ℝ) * (Y1 / c 2) := by
          rw [hb2] at hb1
          linarith [mul_le_mul_of_nonneg_left hb3 hkp]
      _ = k1 * Y1 := by rw [hk1]; ring
  -- `N² ≤ c₆² Y₁` and `1 + log N ≤ kN L`
  set N := ⌊Q⌋₊ with hNdef
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hLB : L ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hXh : X1 ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have hXh0 : 0 < X1 ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hXsq : (X1 ^ (-(1 / 2) : ℝ)) ^ 2 = X1⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
      show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hQb : Q ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) := by
    calc Q ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * L ^ (-B) := hQ2
      _ ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hLB (by positivity)
      _ = _ := mul_one _
  have hN2 : (N : ℝ) ^ 2 ≤ c 6 ^ 2 * Y1 := by
    calc (N : ℝ) ^ 2 ≤ (c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hN0 (hNQ.trans hQb) 2
      _ = c 6 ^ 2 * (Y1 * (Y1 / X1)) := by rw [mul_pow, mul_pow, hXsq]; ring
      _ ≤ c 6 ^ 2 * (Y1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hY1pos.le
          rw [div_le_one (by linarith)]; exact hYX1
      _ = _ := by ring
  have hlogN : 1 + Real.log N ≤ kN * L := by
    have hab : 0 ≤ |Real.log (c 6 ^ 2 * c 3)| := abs_nonneg _
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN]; simp only [Nat.cast_zero, Real.log_zero, add_zero]
      rw [hkN]; linarith [mul_nonneg hab hL0.le]
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNb : (N : ℝ) ≤ c 6 ^ 2 * c 3 * Y2 := by
        calc (N : ℝ) ≤ (N : ℝ) ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hN0 hN1
          _ ≤ c 6 ^ 2 * Y1 := hN2
          _ ≤ c 6 ^ 2 * (c 3 * Y2) := mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = _ := by ring
      have h := Real.log_le_log (by linarith) hNb
      rw [Real.log_mul (by positivity) hY2pos.ne', ← hLdef] at h
      have : Real.log (c 6 ^ 2 * c 3) ≤ |Real.log (c 6 ^ 2 * c 3)| := le_abs_self _
      have : |Real.log (c 6 ^ 2 * c 3)| ≤ |Real.log (c 6 ^ 2 * c 3)| * L :=
        le_mul_of_one_le_right hab hL1
      rw [hkN]; linarith
  have hlogN0 : 0 ≤ 1 + Real.log N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN]; simp
    · have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      linarith
  -- `z^{-σ} = L^{-A}/L³`
  set Λ := L ^ (-A) with hΛ
  have hΛ0 : 0 < Λ := Real.rpow_pos_of_pos hL0 _
  have hzσ : z ^ (-σ) = Λ / L ^ 3 := by
    rw [hzdef, ← Real.rpow_mul hL0.le, hD, hσdef,
      show 12 * (A + 3) * -(1 / 12 : ℝ) = -A + -((3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hL0, Real.rpow_neg hL0.le ((3 : ℕ) : ℝ), Real.rpow_natCast, hΛ]
    ring
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hLne : L ≠ 0 := hL0.ne'
  have hL30 : 0 < L ^ 3 := by positivity
  refine ⟨?_, ?_⟩
  · -- TAIL
    have hT := tail_sum_sq_le hσ hσ2 hY1pos.le hz hzX hnX N a
    rw [hzσ] at hT
    have hLHS0 : 0 ≤ ∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        ∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Zsq z X1, gS n s m| :=
      sum_nonneg (fun q _ => sum_nonneg (fun m _ =>
        mul_nonneg (Real.log_natCast_nonneg m) (abs_nonneg _)))
    have A1 : Real.log n ^ 2 ≤ (kl * L) ^ 2 := pow_le_pow_left₀ hlogn0 hlogn 2
    have A3 : Y1 * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2 ≤ (kN ^ 3 + c 6 ^ 2) * Y1 * L ^ 3 := by
      have h1' : (1 + Real.log N) ^ 3 ≤ (kN * L) ^ 3 := pow_le_pow_left₀ hlogN0 hlogN 3
      have h2' : c 6 ^ 2 * Y1 ≤ c 6 ^ 2 * Y1 * L ^ 3 :=
        le_mul_of_one_le_right (by positivity) hL3
      calc _ ≤ Y1 * (kN * L) ^ 3 + c 6 ^ 2 * Y1 * L ^ 3 :=
            add_le_add (mul_le_mul_of_nonneg_left h1' hY1pos.le) (hN2.trans h2')
        _ = _ := by ring
    have hP1 : Real.log n ^ 2 * (Λ / L ^ 3) ^ 2 * K ^ 3 * (Y1 + (n : ℝ) ^ (2 * σ)) ≤
        (kl * L) ^ 2 * (Λ / L ^ 3) ^ 2 * K ^ 3 * (k1 * Y1) := by
      apply mul_le_mul _ hn6 (by
        have : 0 ≤ (n : ℝ) ^ (2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right A1 (by positivity)
    have hP2 : 0 ≤ Y1 * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2 := by positivity
    have hsq : (∑ q ∈ (Icc 1 N).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
        ∑ m ∈ W1 n X1 Y1 q a, Real.log m * |S (n - m) - ∑ s ∈ Zsq z X1, gS n s m|) ^ 2 ≤
        ((M + 1) * Y1 * Λ) ^ 2 := by
      refine hT.trans ?_
      calc _ ≤ ((kl * L) ^ 2 * (Λ / L ^ 3) ^ 2 * K ^ 3 * (k1 * Y1)) *
            ((kN ^ 3 + c 6 ^ 2) * Y1 * L ^ 3) := mul_le_mul hP1 A3 hP2 (by positivity)
        _ = M * Y1 ^ 2 * Λ ^ 2 / L := by rw [hM]; field_simp
        _ ≤ M * Y1 ^ 2 * Λ ^ 2 := div_le_self (by positivity) hL1
        _ ≤ ((M + 1) * Y1 * Λ) ^ 2 := by
            have : M ≤ (M + 1) ^ 2 := by
              have h := sq_nonneg M
              linarith [show (M + 1) ^ 2 = M ^ 2 + 2 * M + 1 by ring]
            calc M * Y1 ^ 2 * Λ ^ 2 ≤ (M + 1) ^ 2 * Y1 ^ 2 * Λ ^ 2 := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact mul_le_mul_of_nonneg_right this (by positivity)
              _ = _ := by ring
    have hle := (pow_le_pow_iff_left₀ hLHS0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    refine hle.trans ?_
    have : (M + 1) * Y1 * Λ ≤ (M + 1 + K ^ 2 * kN) * Y1 * Λ := by
      apply mul_le_mul_of_nonneg_right _ hΛ0.le
      apply mul_le_mul_of_nonneg_right _ hY1pos.le
      have : 0 ≤ K ^ 2 * kN := by positivity
      linarith
    exact this
  · -- EULER
    have hE := euler_sum_le (n := n) hσ hσ2 hY1pos.le hz hzX N a
    rw [hzσ] at hE
    refine hE.trans ?_
    calc Y1 * (Λ / L ^ 3) * K ^ 2 * (1 + Real.log N) ≤ Y1 * (Λ / L ^ 3) * K ^ 2 * (kN * L) :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
      _ = K ^ 2 * kN * Y1 * Λ / L ^ 2 := by field_simp
      _ ≤ K ^ 2 * kN * Y1 * Λ := div_le_self (by positivity) (one_le_pow₀ hL1)
      _ ≤ (M + 1 + K ^ 2 * kN) * Y1 * Λ := by
          apply mul_le_mul_of_nonneg_right _ hΛ0.le
          apply mul_le_mul_of_nonneg_right _ hY1pos.le
          linarith

/-- **`SingSeriesApprox` holds.** PROVED, no cited input. -/
theorem singSeriesApprox_holds : SingSeriesApprox :=
  singSeriesApprox_of_tails singSeriesTails_holds

/-- **HEADLINE. The F-0008 repair, CONDITIONAL ON `Theorem3` and `Theorem5` only.** -/
theorem theorem2Zeroed_U1462 (h3 : Theorem3) (h5 : Theorem5) : Theorem2Zeroed :=
  theorem2Zeroed_of_tails h3 h5 singSeriesTails_holds

/-- Theorem 2 in the lab's coprime reading, CONDITIONAL ON `Theorem3` and `Theorem5` only. -/
theorem theorem2_U1462 (h3 : Theorem3) (h5 : Theorem5) : Theorem2 :=
  theorem2_of_three h3 h5 singSeriesApprox_holds

end LeanLab.Halupczok2012
