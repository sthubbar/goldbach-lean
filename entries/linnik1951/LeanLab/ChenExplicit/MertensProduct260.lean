module

public import LeanLab.ChenExplicit.TwinCNumeric

/-!
AI wrote the Lean code. Codex task260, 2026-11-04.
Dusart 2010, arXiv 1002.0442, page 11 Theorem 6.12.
The cited input remains an OPEN LEAF. All uses are CONDITIONAL ON it.
The elementary product comparisons support Yamada 2015 page 11 eq 43.
Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.Mertens260


/-- The logarithm of an odd twin factor has a quadratic lower bound. -/
theorem twin_log_lower (n : ℕ) (hn : 2 < n) :
    -(2 * (1 / ((n : ℝ) - 1) ^ 2)) ≤ aT n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ 1 / ((n : ℝ) - 1) ^ 2 := by positivity
  have hx4 : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  unfold aT
  split_ifs with hp
  · have hg : 0 < gT n := gT_pos hn
    have h := one_sub_inv_le_log_of_pos hg
    have hi : (gT n)⁻¹ ≤ 1 + 2 * (1 / ((n : ℝ) - 1) ^ 2) := by
      rw [inv_le_iff_one_le_mul₀ hg]
      unfold gT
      nlinarith
    linarith
  · linarith

/-- The reciprocal square tail is bounded by a telescoping reciprocal tail. -/
theorem reciprocal_square_tail (k : ℕ) (hk : 2 < k) :
    (∑' n : ℕ, 1 / (((n + k : ℕ) : ℝ) - 1) ^ 2) ≤ 1 / ((k : ℝ) - 2) := by
  have hkR : (2 : ℝ) < k := by exact_mod_cast hk
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro B
  have hb : (∑ n ∈ range B, 1 / (((n + k : ℕ) : ℝ) - 1) ^ 2) ≤
      1 / ((k : ℝ) - 2) - 1 / ((B : ℝ) + k - 2) := by
    induction B with
    | zero => simp
    | succ B ih =>
      rw [sum_range_succ]
      push_cast at *
      have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
      have he : 1 / ((B : ℝ) + k - 1) ^ 2 ≤
          1 / ((B : ℝ) + k - 2) - 1 / ((B : ℝ) + 1 + k - 2) := by
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      linarith
  have hnon : 0 ≤ 1 / ((B : ℝ) + k - 2) := by
    apply div_nonneg zero_le_one
    have := Nat.cast_nonneg (α := ℝ) B
    linarith
  linarith

/-- The finite odd twin product loses at most an explicit exponential tail. -/
theorem finite_twin_product_le (k : ℕ) (hk : 2 < k) :
    (∏ p ∈ (range k).filter (fun p => p.Prime ∧ 2 < p), gT p) ≤
      twinC * exp (2 / ((k : ℝ) - 2)) := by
  have hs : Summable (fun n : ℕ => 1 / (((n + k : ℕ) : ℝ) - 1) ^ 2) :=
    (summable_nat_add_iff k).mpr summable_inv_sub_one_sq
  have ht : -(2 / ((k : ℝ) - 2)) ≤ ∑' n : ℕ, aT (n + k) := by
    have h := (hs.mul_left (-2)).tsum_le_tsum
      (fun n => by simpa only [neg_mul] using twin_log_lower (n + k) (by omega))
      ((summable_nat_add_iff k).mpr summable_aT)
    rw [hs.tsum_mul_left] at h
    have hb := reciprocal_square_tail k hk
    calc
      -(2 / ((k : ℝ) - 2)) = -2 * (1 / ((k : ℝ) - 2)) := by ring
      _ ≤ -2 * (∑' n : ℕ, 1 / (((n + k : ℕ) : ℝ) - 1) ^ 2) :=
        mul_le_mul_of_nonpos_left hb (by norm_num)
      _ ≤ _ := h
  have he := exp_le_exp.mpr ht
  have hhead : exp (∑ n ∈ range k, aT n) =
      ∏ p ∈ (range k).filter (fun p => p.Prime ∧ 2 < p), gT p := by
    unfold aT
    rw [← sum_filter, exp_sum]
    apply prod_congr rfl
    intro p hp
    exact exp_log (gT_pos (mem_filter.mp hp).2.2)
  rw [twinC_eq_exp, ← summable_aT.sum_add_tsum_nat_add k, exp_add, hhead]
  have hp : 0 ≤ ∏ p ∈ (range k).filter (fun p => p.Prime ∧ 2 < p), gT p :=
    prod_nonneg (fun p hp => (gT_pos (mem_filter.mp hp).2.2).le)
  have hm := mul_le_mul_of_nonneg_left he hp
  have hm' := mul_le_mul_of_nonneg_right hm (exp_pos (2 / ((k : ℝ) - 2))).le
  rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one] at hm'
  exact hm'

/-- Changing from inclusive to strict prime cutoffs costs at most two over x. -/
theorem strict_product_le_inclusive (x : ℝ) (hx : 2 ≤ x) :
    (∏ p ∈ (range ⌈x⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) ≤
      (∏ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) *
        (1 + 2 / x) := by
  have hnon (s : Finset ℕ) : 0 ≤ ∏ p ∈ s.filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hi : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  by_cases he : x = (⌊x⌋₊ : ℝ)
  · have hc : ⌈x⌉₊ = ⌊x⌋₊ := by
      calc ⌈x⌉₊ = ⌈(⌊x⌋₊ : ℝ)⌉₊ := congrArg (fun t : ℝ => ⌈t⌉₊) he
           _ = _ := Nat.ceil_natCast _
    rw [hc, prod_filter, prod_filter, prod_range_succ]
    by_cases hp : (⌊x⌋₊).Prime
    · rw [if_pos hp]
      have hs := hnon (range ⌊x⌋₊)
      rw [prod_filter] at hs
      have hfactor : 1 ≤ (1 - 1 / x) * (1 + 2 / x) := by
        apply (mul_le_mul_iff_right₀ (show 0 < x ^ 2 by positivity)).mp
        field_simp
        nlinarith
      rw [← he]
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hfactor)]
    · rw [if_neg hp, mul_one]
      exact le_mul_of_one_le_right (by simpa only [prod_filter] using hnon (range ⌊x⌋₊))
        (le_add_of_nonneg_right (by positivity))
  · have hc : ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
      have h1 := Nat.floor_le_ceil x
      have h2 := Nat.ceil_le_floor_add_one x
      have hne : ⌊x⌋₊ ≠ ⌈x⌉₊ := by
        intro h
        apply he
        apply le_antisymm
        · simpa only [h] using Nat.le_ceil x
        · exact Nat.floor_le (by linarith)
      omega
    rw [hc]
    exact le_mul_of_one_le_right (hnon _) (le_add_of_nonneg_right (by positivity))

/-- A linear bound for the finite twin product tail at a real cutoff. -/
theorem finite_twin_product_linear (x : ℝ) (hx : 16 ≤ x) :
    (∏ p ∈ (range ⌈x⌉₊).filter (fun p => p.Prime ∧ 2 < p), gT p) ≤
      twinC * (1 + 8 / x) := by
  have hk := Nat.le_ceil x
  have hk2 : 2 < ⌈x⌉₊ := by
    have : (2 : ℝ) < ⌈x⌉₊ := by linarith
    exact_mod_cast this
  have he : 2 / ((⌈x⌉₊ : ℝ) - 2) ≤ 4 / x := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have h4 : (4 : ℝ) / x < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hb := exp_bound_div_one_sub_of_interval (show 0 ≤ 4 / x by positivity) h4
  have hb' : 1 / (1 - 4 / x) ≤ 1 + 8 / x := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - 4 / x)).mpr
    apply (mul_le_mul_iff_left₀ (show 0 < x ^ 2 by positivity)).mp
    field_simp
    nlinarith
  exact (finite_twin_product_le _ hk2).trans
    (mul_le_mul_of_nonneg_left ((exp_le_exp.mpr he).trans (hb.trans hb')) twinC_pos.le)

/-- Removing finitely many odd factors is bounded by their full inverse product. -/
theorem remove_odd_factors_le (s t : Finset ℕ)
    (hs : ∀ p ∈ s, 2 < p) (ht : ∀ p ∈ t, 2 < p) :
    (∏ p ∈ s.filter (fun p => p ∉ t), (1 - 1 / ((p : ℝ) - 1))) ≤
      (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))) *
        ∏ p ∈ t, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  let f : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1)
  let g : ℕ → ℝ := fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)
  have hf (p : ℕ) (hp : 2 < p) : 0 ≤ f p := by
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp
    dsimp [f]
    have hi : 1 / ((p : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hg (p : ℕ) (hp : 2 < p) : 1 ≤ g p := by
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp
    dsimp [g]
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hfg (p : ℕ) (hp : 2 < p) : f p * g p = 1 := by
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp
    dsimp [f, g]
    field_simp [ne_of_gt (show (0 : ℝ) < (p : ℝ) - 1 by linarith),
      ne_of_gt (show (0 : ℝ) < (p : ℝ) - 2 by linarith)]
    <;> ring
  have heq : (∏ p ∈ s.filter (fun p => p ∉ t), f p) =
      (∏ p ∈ s, f p) * ∏ p ∈ s.filter (fun p => p ∈ t), g p := by
    rw [prod_filter, prod_filter, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases hpt : p ∈ t
    · simp only [hpt, not_true_eq_false, if_false, if_true]
      exact (hfg p (hs p hp)).symm
    · simp [hpt]
  have hsub : s.filter (fun p => p ∈ t) ⊆ t := by
    intro p hp
    exact (mem_filter.mp hp).2
  have hprod : (∏ p ∈ s.filter (fun p => p ∈ t), g p) ≤ ∏ p ∈ t, g p := by
    apply prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p hp
      exact (hg p (ht p (hsub hp))).trans' (by norm_num)
    · intro p hp _
      exact hg p (ht p hp)
  change (∏ p ∈ s.filter (fun p => p ∉ t), f p) ≤ (∏ p ∈ s, f p) * ∏ p ∈ t, g p
  rw [heq]
  exact mul_le_mul_of_nonneg_left hprod (prod_nonneg (fun p hp => hf p (hs p hp)))

end LeanLab.ChenExplicit.Mertens260
