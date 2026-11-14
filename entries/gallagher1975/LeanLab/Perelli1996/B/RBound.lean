module

public import Mathlib
public import LeanLab.Perelli1996.B.Definitions

/-!
P0083 Perelli 1996, page 478, the step from Corollary 1 part 1 to part 2: when `m` is not a
sum of two primes, every pair in `R(m) = ∑_{r+s=m} Λ(r)Λ(s)` has a proper prime power, so
`R(m) ≤ 2 (√m + 1)(log₂ m + 1) log² m`, and this is at most `m/4` once `m ≥ 17408^8`.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Perelli1996.B
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- The proper prime powers `p^j`, `j ≥ 2`, in `[0, m]`. -/
def PP (m : ℕ) : Finset ℕ := (range (m + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime)

/-- **Count of proper prime powers**: at most `(√m + 1)(log₂ m + 1)` of them up to `m`. -/
theorem card_PP_le (m : ℕ) : (PP m).card ≤ (Nat.sqrt m + 1) * (Nat.log 2 m + 1) := by
  have hsub : PP m ⊆ ((range (Nat.sqrt m + 1)) ×ˢ (range (Nat.log 2 m + 1))).image
      (fun x => x.1 ^ x.2) := by
    intro k hk
    simp only [PP, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkm, hpp, hnp⟩ := hk
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hj2 : 2 ≤ j := by
      by_contra h
      have : j = 1 := by omega
      subst this
      exact hnp (by simpa using hp)
    rw [Finset.mem_image]
    refine ⟨(p, j), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have hp1 : 1 ≤ p := hp.one_lt.le
    constructor
    · have : p ^ 2 ≤ m := le_trans (Nat.pow_le_pow_right hp1 hj2) (by omega)
      have := Nat.le_sqrt'.2 this
      omega
    · have : 2 ^ j ≤ m := le_trans (Nat.pow_le_pow_left hp.two_le j) (by omega)
      have := Nat.le_log_of_pow_le (by norm_num) this
      omega
  calc (PP m).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by rw [Finset.card_product]; simp

theorem log_nat_mono {k m : ℕ} (h : k ≤ m) : Real.log k ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.log_natCast_nonneg m
  · exact Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast h)

/-- `R(m)` as a sum over `k ≤ m`. -/
theorem R_eq (m : ℕ) : R m = ∑ k ∈ range (m + 1), Λ k * Λ (m - k) := by
  unfold R
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **`R(m) ≤ 2 |PP m| log² m` when `m` is not a sum of two primes.** -/
theorem R_le_of_not_goldbach {m : ℕ} (hm : ¬ IsGoldbachSum m) :
    R m ≤ 2 * ((PP m).card : ℝ) * Real.log m ^ 2 := by
  rw [R_eq]
  set L := Real.log m
  have hL : 0 ≤ L := Real.log_natCast_nonneg m
  have hterm : ∀ k ∈ range (m + 1), Λ k * Λ (m - k) ≤
      ((if k ∈ PP m then 1 else 0) + (if m - k ∈ PP m then 1 else 0)) * L ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hΛk : Λ k ≤ L := le_trans ArithmeticFunction.vonMangoldt_le_log
      (log_nat_mono (by omega))
    have hΛs : Λ (m - k) ≤ L := le_trans ArithmeticFunction.vonMangoldt_le_log
      (log_nat_mono (Nat.sub_le m k))
    have h0k := ArithmeticFunction.vonMangoldt_nonneg (n := k)
    have h0s := ArithmeticFunction.vonMangoldt_nonneg (n := m - k)
    by_cases hz : Λ k * Λ (m - k) = 0
    · rw [hz]; positivity
    · have hk0 : Λ k ≠ 0 := left_ne_zero_of_mul hz
      have hs0 : Λ (m - k) ≠ 0 := right_ne_zero_of_mul hz
      have hpk : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hk0
      have hps : IsPrimePow (m - k) := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hs0
      have hone : ¬ k.Prime ∨ ¬ (m - k).Prime := by
        by_contra h
        rw [not_or, not_not, not_not] at h
        exact hm ⟨k, m - k, h.1, h.2, by omega⟩
      have hprod : Λ k * Λ (m - k) ≤ L ^ 2 := by
        rw [sq]; exact mul_le_mul hΛk hΛs h0s hL
      rcases hone with h | h
      · have : k ∈ PP m := by
          simp only [PP, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hpk, h⟩
        rw [if_pos this]
        have : (0 : ℝ) ≤ (if m - k ∈ PP m then 1 else 0) := by split_ifs <;> norm_num
        nlinarith [sq_nonneg L]
      · have : m - k ∈ PP m := by
          simp only [PP, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hps, h⟩
        rw [if_pos this]
        have : (0 : ℝ) ≤ (if k ∈ PP m then 1 else 0) := by split_ifs <;> norm_num
        nlinarith [sq_nonneg L]
  calc ∑ k ∈ range (m + 1), Λ k * Λ (m - k)
      ≤ ∑ k ∈ range (m + 1), ((if k ∈ PP m then 1 else 0) +
          (if m - k ∈ PP m then 1 else 0)) * L ^ 2 := Finset.sum_le_sum hterm
    _ = ((∑ k ∈ range (m + 1), (if k ∈ PP m then (1 : ℝ) else 0)) +
          ∑ k ∈ range (m + 1), (if m - k ∈ PP m then (1 : ℝ) else 0)) * L ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
    _ = 2 * ((PP m).card : ℝ) * L ^ 2 := by
        have h1 : ∑ k ∈ range (m + 1), (if k ∈ PP m then (1 : ℝ) else 0) = (PP m).card := by
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 2
          exact Finset.inter_eq_right.2 (Finset.filter_subset _ _)
        have h2 : ∑ k ∈ range (m + 1), (if m - k ∈ PP m then (1 : ℝ) else 0) =
            ∑ k ∈ range (m + 1), (if k ∈ PP m then (1 : ℝ) else 0) := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          congr 2
          omega
        rw [h2, h1]; ring

/-- `log₂ m ≤ 2 log m` as reals, for `m ≥ 1`. -/
theorem natLog_le (m : ℕ) (hm : 1 ≤ m) : (Nat.log 2 m : ℝ) ≤ 2 * Real.log m := by
  have h := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have h' : ((2 : ℝ) ^ (Nat.log 2 m)) ≤ m := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at hlog
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hk : (0 : ℝ) ≤ Nat.log 2 m := Nat.cast_nonneg _
  nlinarith

/-- **`2 (√m + 1)(log₂ m + 1) log² m ≤ m / 4` for `m ≥ 17408^8`.** Uses `log x ≤ 8 x^{1/8}`. -/
theorem pp_bound_le (m : ℕ) (hm : (17408 : ℝ) ^ 8 ≤ m) :
    2 * (((Nat.sqrt m + 1) * (Nat.log 2 m + 1) : ℕ) : ℝ) * Real.log m ^ 2 ≤ (m : ℝ) / 4 := by
  set x : ℝ := (m : ℝ) with hxdef
  have hx1 : 1 ≤ x := le_trans (by norm_num) hm
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ 8 * x ^ ((1 : ℝ) / 8) := by
    have := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 8)
    linarith [show x ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * x ^ ((1 : ℝ) / 8) by ring]
  set e := x ^ ((1 : ℝ) / 8) with he
  have he1 : 1 ≤ e := Real.one_le_rpow hx1 (by norm_num)
  have he17 : 17408 ≤ e := by
    have := Real.rpow_le_rpow (by positivity) hm (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rwa [show ((17408 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) = 17408 by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num] at this
  have hx8 : x = e ^ 8 := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hsq : (Nat.sqrt m : ℝ) ≤ e ^ 4 := by
    have h1 : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ x := by rw [hxdef]; exact_mod_cast Nat.sqrt_le' m
    have h2 : 0 ≤ (Nat.sqrt m : ℝ) := Nat.cast_nonneg _
    have : (e ^ 4) ^ 2 = x := by rw [hx8]; ring
    exact (pow_le_pow_iff_left₀ h2 (by positivity) two_ne_zero).1 (by rw [this]; exact h1)
  have hlg : (Nat.log 2 m : ℝ) ≤ 16 * e := by
    have := natLog_le m (by have h : (1 : ℝ) ≤ (m : ℝ) := hx1; exact_mod_cast h); linarith
  push_cast
  have hA : (Nat.sqrt m : ℝ) + 1 ≤ 2 * e ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) he1 4]
  have hB : (Nat.log 2 m : ℝ) + 1 ≤ 17 * e := by linarith
  have hC : Real.log x ^ 2 ≤ 64 * e ^ 2 := by nlinarith
  have hA0 : 0 ≤ (Nat.sqrt m : ℝ) + 1 := by positivity
  have hB0 : 0 ≤ (Nat.log 2 m : ℝ) + 1 := by positivity
  calc 2 * (((Nat.sqrt m : ℝ) + 1) * ((Nat.log 2 m : ℝ) + 1)) * Real.log x ^ 2
      ≤ 2 * ((2 * e ^ 4) * (17 * e)) * (64 * e ^ 2) := by
        gcongr
    _ = 4352 * e ^ 7 := by ring
    _ ≤ e ^ 8 / 4 := by
        have : 0 ≤ e ^ 7 := by positivity
        nlinarith
    _ = x / 4 := by rw [hx8]

/-- **`R(m) ≤ m/4` when `m ≥ 17408^8` is not a sum of two primes.** -/
theorem R_le_quarter {m : ℕ} (hm : (17408 : ℝ) ^ 8 ≤ m) (hg : ¬ IsGoldbachSum m) :
    R m ≤ (m : ℝ) / 4 := by
  have h1 := R_le_of_not_goldbach hg
  have h2 : ((PP m).card : ℝ) ≤ (((Nat.sqrt m + 1) * (Nat.log 2 m + 1) : ℕ) : ℝ) := by
    exact_mod_cast card_PP_le m
  have h3 := pp_bound_le m hm
  have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
  calc R m ≤ 2 * ((PP m).card : ℝ) * Real.log m ^ 2 := h1
    _ ≤ 2 * (((Nat.sqrt m + 1) * (Nat.log 2 m + 1) : ℕ) : ℝ) * Real.log m ^ 2 := by gcongr
    _ ≤ _ := h3

end LeanLab.Perelli1996.B

