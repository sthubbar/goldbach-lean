module

public import Mathlib
public import LeanLab.HeathBrown1985.Section3

/-!
P0096 Heath-Brown 1985, page 54: the inner sum of S₁ for fixed m and c, rewritten with
n = m - c r as a sum over n ≤ x, n ≡ m mod c, of Δ_Q(n) log((m - n)/c), and bounded by
discrete partial summation against the antitone nonnegative weight log((m - n)/c).
PROVED here: abel_antitone, inner_S1_eq, abs_inner_S1_le.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- Discrete partial summation: an antitone nonnegative weight costs at most its first value. -/
theorem abel_antitone (a w : ℕ → ℝ) (C : ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ t, 1 ≤ t → t ≤ M → |∑ n ∈ Icc 1 t, a n| ≤ C)
    (hw : ∀ n, 1 ≤ n → n < M → w (n + 1) ≤ w n) (hw0 : 0 ≤ w M) :
    |∑ n ∈ Icc 1 M, a n * w n| ≤ C * w 1 := by
  have key : ∀ k, 1 ≤ k → k ≤ M →
      |∑ n ∈ Icc 1 k, a n * w n - (∑ n ∈ Icc 1 k, a n) * w k| ≤ C * (w 1 - w k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; simp
    | succ k hk ih =>
      intro hkM
      have ih' := ih (by omega)
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
      have hAk := hA k hk (by omega)
      have hwk := hw k hk (by omega)
      have e : ∑ n ∈ Icc 1 k, a n * w n + a (k + 1) * w (k + 1) -
          (∑ n ∈ Icc 1 k, a n + a (k + 1)) * w (k + 1) =
          (∑ n ∈ Icc 1 k, a n * w n - (∑ n ∈ Icc 1 k, a n) * w k) +
            (∑ n ∈ Icc 1 k, a n) * (w k - w (k + 1)) := by ring
      rw [e]
      have h2 : |(∑ n ∈ Icc 1 k, a n) * (w k - w (k + 1))| ≤ C * (w k - w (k + 1)) := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w k - w (k + 1))]
        exact mul_le_mul_of_nonneg_right hAk (by linarith)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ C * (w 1 - w k) + C * (w k - w (k + 1)) := add_le_add ih' h2
        _ = C * (w 1 - w (k + 1)) := by ring
  have h1 := key M hM le_rfl
  have h2 : |(∑ n ∈ Icc 1 M, a n) * w M| ≤ C * w M := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hA M hM le_rfl) hw0
  have e : ∑ n ∈ Icc 1 M, a n * w n =
      (∑ n ∈ Icc 1 M, a n * w n - (∑ n ∈ Icc 1 M, a n) * w M) + (∑ n ∈ Icc 1 M, a n) * w M := by
    ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ C * (w 1 - w M) + C * w M := add_le_add h1 h2
    _ = C * w 1 := by ring

/-- The weight `log((m - n)/c)`. -/
def wt (m c n : ℕ) : ℝ := Real.log (((m : ℝ) - n) / c)

/-- `Δ_Q(n)` restricted to `n ≡ m mod c`. -/
def aC (Q : ℝ) (c m n : ℕ) : ℝ := if n % c = m % c then DeltaQ Q n else 0

theorem sum_aC_eq (Q : ℝ) (c m t : ℕ) :
    ∑ n ∈ Icc 1 t, aC Q c m n = apSum (DeltaQ Q) (t : ℝ) c m := by
  unfold apSum aC; rw [Nat.floor_natCast, sum_filter]

theorem wt_sub (m c r : ℕ) (hc : 1 ≤ c) (h : c * r < m) : wt m c (m - c * r) = Real.log r := by
  have hcR : (c : ℝ) ≠ 0 := by
    have : (0 : ℝ) < c := by exact_mod_cast hc
    exact this.ne'
  unfold wt
  rw [Nat.cast_sub h.le]; push_cast
  congr 1; field_simp; ring

/-- The inner sum of `S₁` as a weighted progression sum of `Δ_Q`. -/
theorem inner_S1_eq (x Q : ℝ) (hx : 1 ≤ x) (m c : ℕ) (hc : 1 ≤ c) (hm : m ∈ mRange x) :
    ∑ r ∈ Icc 1 (⌊3 * x⌋₊ / c), Real.log r * fm x Q m (c * r) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, aC Q c m n * wt m c n := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, hm2⟩ := hm
  have hx0 : 0 < x := by linarith
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfxm : ⌊x⌋₊ < m := by
    have : (⌊x⌋₊ : ℝ) < m := by linarith
    exact_mod_cast this
  have eR : ∑ n ∈ Icc 1 ⌊x⌋₊, aC Q c m n * wt m c n =
      ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % c = m % c), DeltaQ Q n * wt m c n := by
    rw [sum_filter]; apply sum_congr rfl; intro n _; unfold aC; split_ifs <;> simp
  rw [eR, ← sum_filter_ne_zero]
  symm; rw [← sum_filter_ne_zero]; symm
  apply Finset.sum_nbij' (fun r => m - c * r) (fun n => (m - n) / c)
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr ⊢
    obtain ⟨⟨hr1, hrN⟩, hne⟩ := hr
    unfold fm at hne
    split_ifs at hne with hcd
    · obtain ⟨h1, h2⟩ := hcd
      refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
      · have : ((m - c * r : ℕ) : ℝ) ≤ x := by push_cast [h2.le] at h1 ⊢; linarith
        exact Nat.le_floor this
      · have h3 : m - c * r + c * r = m := Nat.sub_add_cancel h2.le
        have : (m - c * r) % c = m % c := by
          conv_rhs => rw [← h3]
          rw [Nat.add_mul_mod_self_left]
        exact this
      · rw [wt_sub m c r hc h2, mul_comm]; exact hne
    · exact absurd (mul_zero _) hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨⟨hn1, hnx⟩, hmod⟩, hne⟩ := hn
    have hnR : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) hfx
    have hlt : n < m := by omega
    have hdvd : c ∣ m - n := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    obtain ⟨r, hr⟩ := hdvd
    have hrv : (m - n) / c = r := by rw [hr]; exact Nat.mul_div_cancel_left r (by omega)
    rw [hrv]
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h, mul_zero] at hr; omega
      · exact h
    have hcr : c * r = m - n := hr.symm
    have hcrm : c * r < m := by omega
    refine ⟨⟨hr1, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le hc]
      have : c * r ≤ m := by omega
      linarith [Nat.mul_comm r c]
    · unfold fm
      have hsubR : ((c * r : ℕ) : ℝ) = (m : ℝ) - n := by rw [hcr]; push_cast [hlt.le]; ring
      rw [if_pos ⟨by rw [hsubR]; linarith, hcrm⟩]
      have hn' : m - c * r = n := by omega
      have := wt_sub m c r hc hcrm
      rw [hn'] at this
      rw [hn', ← this, mul_comm]; exact hne
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr
    obtain ⟨_, hne⟩ := hr
    unfold fm at hne
    split_ifs at hne with hcd
    · have h2 := hcd.2
      rw [Nat.sub_sub_self h2.le]; exact Nat.mul_div_cancel_left r (by omega)
    · exact absurd (mul_zero _) hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnx⟩, hmod⟩, _⟩ := hn
    have hlt : n < m := by omega
    have hdvd : c ∣ m - n := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    rw [Nat.mul_div_cancel' hdvd]; omega
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr
    obtain ⟨_, hne⟩ := hr
    unfold fm at hne ⊢
    split_ifs at hne with hcd
    · rw [if_pos hcd, wt_sub m c r hc hcd.2]; ring
    · exact absurd (mul_zero _) hne

/-- **Page 54, one `m`, one `c`**: if every partial sum
`|Σ_{n ≤ t, n ≡ m (c)} Δ_Q(n)|`, `1 ≤ t ≤ x`, is at most `C`, the inner sum of `S₁` is at most
`C log(3x)`. -/
theorem abs_inner_S1_le (x Q : ℝ) (hx : 1 ≤ x) (m c : ℕ) (hc : 1 ≤ c) (hcx : (c : ℝ) ≤ x)
    (hm : m ∈ mRange x) (C : ℝ)
    (hA : ∀ t : ℕ, 1 ≤ t → t ≤ ⌊x⌋₊ → |apSum (DeltaQ Q) (t : ℝ) c m| ≤ C) :
    |∑ r ∈ Icc 1 (⌊3 * x⌋₊ / c), Real.log r * fm x Q m (c * r)| ≤ C * Real.log (3 * x) := by
  have hm' := hm
  simp only [mRange, mem_filter, mem_Icc] at hm'
  obtain ⟨⟨hm1, hm3⟩, hm2⟩ := hm'
  have hx0 : 0 < x := by linarith
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hM : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfxm : ⌊x⌋₊ < m := by
    have : (⌊x⌋₊ : ℝ) < m := by linarith
    exact_mod_cast this
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  rw [inner_S1_eq x Q hx m c hc hm]
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hA 1 le_rfl hM)
  have hab := abel_antitone (aC Q c m) (wt m c) C ⌊x⌋₊ hM
    (fun t ht htM => by rw [sum_aC_eq]; exact hA t ht htM)
    (fun n hn hnM => by
      unfold wt
      have hn1 : ((n + 1 : ℕ) : ℝ) < m := by
        have : n + 1 < m := by omega
        exact_mod_cast this
      apply Real.log_le_log
      · apply div_pos _ hcR; linarith
      · apply div_le_div_of_nonneg_right _ hcR.le; push_cast; linarith)
    (by
      unfold wt
      apply Real.log_nonneg
      rw [le_div_iff₀ hcR]; linarith)
  refine hab.trans (mul_le_mul_of_nonneg_left ?_ hC)
  unfold wt
  have hm2R : (2 : ℝ) < m := by linarith
  apply Real.log_le_log
  · apply div_pos _ hcR; push_cast; linarith
  · calc ((m : ℝ) - ((1 : ℕ) : ℝ)) / c ≤ ((m : ℝ) - ((1 : ℕ) : ℝ)) / 1 :=
          div_le_div_of_nonneg_left (by push_cast; linarith) one_pos (by exact_mod_cast hc)
      _ ≤ 3 * x := by push_cast; linarith

end LeanLab.HeathBrown1985
