module

public import Mathlib
public import LeanLab.HeathBrown1985.Section3
public import LeanLab.HeathBrown1985.Lemma2
public import LeanLab.HeathBrown1985.Bound24

/-!
P0096 Heath-Brown 1985, page 54: `Σ₂ ≪ L x Σ_{k ≤ uv} k⁻¹ δ₁(x, k, Q)`, hence by Lemma 2
`Σ₂ ≪ x² Q^{-1/2} L⁸`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `|c_k| ≤ log k`. -/
theorem abs_ck_le (U V k : ℕ) : |ck U V k| ≤ Real.log k := by
  rw [← ck_eq, ArithmeticFunction.mul_apply]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x ∈ k.divisorsAntidiagonal, |muLe U x.1 * lamLe V x.2|
      ≤ ∑ x ∈ k.divisorsAntidiagonal, Λ x.2 := by
        apply sum_le_sum; intro x _
        simp only [muLe, lamLe, ArithmeticFunction.coe_mk]
        have h0 : 0 ≤ Λ x.2 := ArithmeticFunction.vonMangoldt_nonneg
        have h1 : |(μ x.1 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        split_ifs <;> simp [abs_mul, abs_of_nonneg h0] <;> nlinarith [abs_nonneg (μ x.1 : ℝ)]
    _ = ∑ d ∈ k.divisors, Λ d := by
        rw [Nat.sum_divisorsAntidiagonal' (fun _ b => Λ b)]
    _ = Real.log k := ArithmeticFunction.vonMangoldt_sum

/-- The inner sum of `S₂` is a progression sum of `Δ_Q`. -/
theorem inner_S2_eq (x Q : ℝ) (hx : 1 ≤ x) (m k : ℕ) (hk : 1 ≤ k) (hm : m ∈ mRange x) :
    ∑ r ∈ Icc 1 (⌊3 * x⌋₊ / k), fm x Q m (k * r) = resSum (DeltaQ Q) ⌊x⌋₊ k (m % k) := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, hm2⟩ := hm
  have hx0 : 0 < x := by linarith
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfxm : ⌊x⌋₊ < m := by
    have : (⌊x⌋₊ : ℝ) < m := by linarith
    exact_mod_cast this
  unfold resSum
  rw [← sum_filter_ne_zero]
  symm; rw [← sum_filter_ne_zero]; symm
  apply Finset.sum_nbij' (fun r => m - k * r) (fun n => (m - n) / k)
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr ⊢
    obtain ⟨⟨hr1, hrN⟩, hne⟩ := hr
    unfold fm at hne
    split_ifs at hne with hc
    · obtain ⟨h1, h2⟩ := hc
      have hkrR : ((k * r : ℕ) : ℝ) ≥ (m : ℝ) - x := h1
      refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, hne⟩
      · have : ((m - k * r : ℕ) : ℝ) ≤ x := by push_cast [h2.le] at h1 ⊢; linarith
        exact Nat.le_floor this
      · have h3 : m - k * r + k * r = m := Nat.sub_add_cancel h2.le
        have : (m - k * r) % k = m % k := by
          conv_rhs => rw [← h3]
          rw [Nat.add_mul_mod_self_left]
        exact this
    · exact absurd rfl hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨⟨hn1, hnx⟩, hmod⟩, hne⟩ := hn
    have hnR : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) hfx
    have hlt : n < m := by omega
    have hdvd : k ∣ m - n := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    obtain ⟨r, hr⟩ := hdvd
    have hrv : (m - n) / k = r := by rw [hr]; exact Nat.mul_div_cancel_left r (by omega)
    rw [hrv]
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h, mul_zero] at hr; omega
      · exact h
    have hkr : k * r = m - n := hr.symm
    have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
    refine ⟨⟨hr1, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le hk]
      have : k * r ≤ m := by omega
      linarith [Nat.mul_comm r k]
    · unfold fm
      have hsubR : ((k * r : ℕ) : ℝ) = (m : ℝ) - n := by rw [hkr]; push_cast [hlt.le]; ring
      rw [if_pos ⟨by rw [hsubR]; linarith, by omega⟩]
      rw [hkr, Nat.sub_sub_self hlt.le]; exact hne
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr
    obtain ⟨_, hne⟩ := hr
    unfold fm at hne
    split_ifs at hne with hc
    · have h2 := hc.2
      rw [Nat.sub_sub_self h2.le]; exact Nat.mul_div_cancel_left r (by omega)
    · exact absurd rfl hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnx⟩, hmod⟩, _⟩ := hn
    have hlt : n < m := by omega
    have hdvd : k ∣ m - n := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    rw [Nat.mul_div_cancel' hdvd]; omega
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr
    obtain ⟨_, hne⟩ := hr
    unfold fm at hne ⊢
    split_ifs at hne with hc
    · have h2 := hc.2
      rw [if_pos hc]
    · exact absurd rfl hne

/-- Each residue class mod `k` meets `(2x, 3x]` at most `2x/k` times, for `1 ≤ k ≤ x`. -/
theorem card_mRange_mod_le (x : ℝ) (hx : 1 ≤ x) (k r : ℕ) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x) :
    (((mRange x).filter (fun m => m % k = r)).card : ℝ) ≤ 2 * x / k := by
  set a := ⌊2 * x⌋₊ + 1
  set b := ⌊3 * x⌋₊
  have hx0 : 0 < x := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsub : ((mRange x).filter (fun m => m % k = r)).card ≤ ((b - a) / k + 1) := by
    have : ((mRange x).filter (fun m => m % k = r)).card ≤ (range ((b - a) / k + 1)).card := by
      apply card_le_card_of_injOn (fun m => (m - a) / k)
      · intro m hm
        simp only [coe_filter, mRange, mem_filter, mem_Icc, Set.mem_setOf_eq] at hm
        simp only [coe_range, Set.mem_Iio]
        have : m - a ≤ b - a := Nat.sub_le_sub_right hm.1.1.2 a
        exact Nat.lt_succ_of_le (Nat.div_le_div_right this)
      · intro m hm m' hm' h
        simp only [coe_filter, mRange, mem_filter, mem_Icc, Set.mem_setOf_eq] at hm hm'
        simp only at h
        have ha : a ≤ m := by
          have : (⌊2 * x⌋₊ : ℝ) < m := lt_of_le_of_lt (Nat.floor_le (by linarith)) hm.1.2
          have : ⌊2 * x⌋₊ < m := by exact_mod_cast this
          omega
        have ha' : a ≤ m' := by
          have : (⌊2 * x⌋₊ : ℝ) < m' := lt_of_le_of_lt (Nat.floor_le (by linarith)) hm'.1.2
          have : ⌊2 * x⌋₊ < m' := by exact_mod_cast this
          omega
        have hmod : (m - a) % k = (m' - a) % k := by
          have e1 : (m - a + a) % k = (m' - a + a) % k := by
            rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel ha', hm.2, hm'.2]
          have := Nat.ModEq.add_right_cancel' a e1
          exact this
        have : m - a = m' - a := by
          rw [← Nat.div_add_mod (m - a) k, ← Nat.div_add_mod (m' - a) k, h, hmod]
        omega
    simpa using this
  have hba : ((b - a : ℕ) : ℝ) ≤ x := by
    rcases le_or_gt a b with h | h
    · rw [Nat.cast_sub h]
      have h1 : (b : ℝ) ≤ 3 * x := Nat.floor_le (by linarith)
      have h2 : 2 * x < (a : ℝ) := by
        have := Nat.lt_floor_add_one (2 * x)
        simp only [a]; push_cast; linarith
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith
  calc (((mRange x).filter (fun m => m % k = r)).card : ℝ) ≤ (((b - a) / k + 1 : ℕ) : ℝ) := by
        exact_mod_cast hsub
    _ ≤ x / k + 1 := by
        push_cast
        have : (((b - a) / k : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) / k := Nat.cast_div_le
        have : ((b - a : ℕ) : ℝ) / k ≤ x / k := div_le_div_of_nonneg_right hba hkR.le
        linarith
    _ ≤ 2 * x / k := by
        have : 1 ≤ x / k := by rw [le_div_iff₀ hkR]; linarith
        have e : 2 * x / k = x / k + x / k := by ring
        linarith

/-- `Σ_{2x < m ≤ 3x} |Σ_{n ≤ x, n ≡ m (k)} Δ_Q(n)| ≤ (2x/k) δ₁(x, k, Q)`. -/
theorem sum_m_resSum_le (x Q : ℝ) (hx : 1 ≤ x) (k : ℕ) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x) :
    ∑ m ∈ mRange x, |resSum (DeltaQ Q) ⌊x⌋₊ k (m % k)| ≤ 2 * x / k * delta1 x k Q := by
  rw [delta1_eq x k Q hk]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m => m % k) (t := range k)
    (fun m _ => by simp only [mem_range]; exact Nat.mod_lt _ (by omega))]
  rw [mul_sum]
  apply sum_le_sum; intro r _
  rw [sum_congr rfl (fun m hm => by rw [(mem_filter.mp hm).2]), sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_mRange_mod_le x hx k r hk hkx) (abs_nonneg _)

/-- **Page 54: `Σ₂ ≪ x² Q^{-1/2} L⁸` from Lemma 2.** -/
theorem boundSigma2_of (h2 : Lemma2) : BoundSigma2 := by
  intro B hB
  obtain ⟨C, hC⟩ := h2 B hB
  refine ⟨2 * |C|, fun x hx => ?_⟩
  set L := Real.log x
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  set Q := L ^ B
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hL0 _
  set U := ⌊Q⌋₊
  set V := ⌊x / Q ^ 2⌋₊
  have hUV : ((U * V : ℕ) : ℝ) ≤ x / Q := by
    push_cast
    have hU : (U : ℝ) ≤ Q := Nat.floor_le hQ0.le
    have hV : (V : ℝ) ≤ x / Q ^ 2 := Nat.floor_le (by positivity)
    calc (U : ℝ) * V ≤ Q * (x / Q ^ 2) := mul_le_mul hU hV (by positivity) hQ0.le
      _ = x / Q := by field_simp
  have hUVx : ((U * V : ℕ) : ℝ) ≤ x := by
    rcases le_or_gt 1 Q with h | h
    · exact hUV.trans (div_le_self hx0.le h)
    · have : U = 0 := Nat.floor_eq_zero.mpr h
      rw [this]; simp; linarith
  have hstep : ∀ m ∈ mRange x, |S2 U V ⌊3 * x⌋₊ (fm x Q m)| ≤
      ∑ k ∈ Icc 1 (U * V), L * |resSum (DeltaQ Q) ⌊x⌋₊ k (m % k)| := by
    intro m hm
    unfold S2
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun k hk => ?_))
    have hk1 := (mem_Icc.mp hk).1
    have hkx : (k : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hk).2) hUVx
    rw [abs_mul, inner_S2_eq x Q (by linarith) m k hk1 hm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact (abs_ck_le U V k).trans (Real.log_le_log (by exact_mod_cast hk1) hkx)
  have hsum : Sigma2 x Q ≤ 2 * L * x * ∑ k ∈ Icc 1 (U * V), delta1 x k Q / k := by
    unfold Sigma2
    refine (sum_le_sum hstep).trans ?_
    rw [sum_comm]
    rw [mul_sum]
    apply sum_le_sum; intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hkx : (k : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hk).2) hUVx
    rw [← mul_sum]
    have h := sum_m_resSum_le x Q (by linarith) k hk1 hkx
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    calc L * ∑ m ∈ mRange x, |resSum (DeltaQ Q) ⌊x⌋₊ k (m % k)| ≤ L * (2 * x / k * delta1 x k Q) :=
          mul_le_mul_of_nonneg_left h hL0.le
      _ = 2 * L * x * (delta1 x k Q / k) := by field_simp
  have hL2 := hC x hx ((U * V : ℕ) : ℝ) hUV
  rw [Nat.floor_natCast] at hL2
  refine hsum.trans ?_
  have hP : 0 ≤ x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 := by positivity
  calc 2 * L * x * ∑ k ∈ Icc 1 (U * V), delta1 x k Q / k
      ≤ 2 * L * x * (C * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7) :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ ≤ 2 * L * x * (|C| * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have e1 : C * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 = C * (x * Q ^ (-(1 : ℝ) / 2) * L ^ 7) := by ring
        have e2 : |C| * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 =
            |C| * (x * Q ^ (-(1 : ℝ) / 2) * L ^ 7) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hP
    _ = 2 * |C| * x ^ 2 * Q ^ (-(1 : ℝ) / 2) * L ^ 8 := by ring

/-- `Σ₂ ≪ x² Q^{-1/2} L⁸` from the Siegel-Walfisz theorem 1.1 alone. Fully proved. -/
theorem boundSigma2_of_siegelWalfisz (hSW : SiegelWalfisz) : BoundSigma2 :=
  boundSigma2_of (lemma2_of (lemma1_7_of (bound2_4_of hSW)) bound2_5 divMoment2 divMoment3)

end LeanLab.HeathBrown1985
