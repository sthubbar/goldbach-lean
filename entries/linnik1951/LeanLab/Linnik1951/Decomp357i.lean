module

public import LeanLab.Linnik1951.Decomp280b

/-!
P0093 page 161 equation 7.1. Elementary dyadic damping bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 161 equation 7.1. Split at the integer base two logarithm.
The initial terms are at most one and the dyadic tail has sum at most two. -/
theorem power_abs_le_log357 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖powerFourier111 N α‖ ≤ Real.log N / Real.log 2 + 2 := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let L := Nat.log 2 N
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have ha : Summable a := (damping_summable111 N hN).comp_injective hi
  have hL : (L : ℝ) ≤ Real.log N / Real.log 2 := by
    have hpow : (2 : ℝ) ^ L ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) L) hpow
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
  have hNpow : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have htail (j : ℕ) : a (j + L) ≤ (1 / 2 : ℝ) ^ j := by
    have hratio : (2 : ℝ) ^ j ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) / N := by
      apply (le_div_iff₀ hpos).mpr
      push_cast
      rw [show j + L + 1 = j + (L + 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left hNpow (by positivity)
    calc
      _ ≤ Real.exp (-((2 : ℝ) ^ j)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hratio
      _ = 1 / Real.exp ((2 : ℝ) ^ j) := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (2 : ℝ) ^ j := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith [Real.add_one_le_exp ((2 : ℝ) ^ j)]
      _ = _ := (one_div_pow _ _).symm
  have htailSum : (∑' j : ℕ, a (j + L)) ≤ 2 := by
    have hg : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    calc
      _ ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
        Summable.tsum_le_tsum htail (ha.comp_injective (add_left_injective L)) hg
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]; norm_num
  have hhead : ∑ j ∈ range L, a j ≤ L := by
    calc
      _ ≤ ∑ _j ∈ range L, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.exp_le_one_iff.mpr
        rw [neg_div]
        exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) hpos.le)
      _ = _ := by simp
  have hnorm : ‖powerFourier111 N α‖ ≤ ∑' j : ℕ, a j := by
    have ht := norm_tsum_le_tsum_norm (power_fourier_summable111 N hN α).norm
    simpa only [powerFourier111, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using ht
  calc
    _ ≤ ∑' j : ℕ, a j := hnorm
    _ = ∑ j ∈ range L, a j + ∑' j : ℕ, a (j + L) := (ha.sum_add_tsum_nat_add L).symm
    _ ≤ L + 2 := add_le_add hhead htailSum
    _ ≤ _ := by linarith

/-- P0093 page 161 equation 7.1. Exact power_uniform_log357 statement,
with explicit A equal to one over log 2 plus two and log N at least one. -/
theorem power_uniform_log_proved357 :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, ‖powerFourier111 N α‖ ≤ A * Real.log N := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨1 / Real.log 2 + 2, by positivity, max 1 N0, ?_⟩
  intro N hN α
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNN : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hnR : (N0 : ℝ) < (N : ℝ) := by exact_mod_cast hNN
  have hlog : 1 ≤ Real.log N := by
    have ht := Real.log_le_log (Real.exp_pos 1) (hN0.trans hnR).le
    simpa only [Real.log_exp] using ht
  have h := power_abs_le_log357 N (by omega) α
  calc
    _ ≤ Real.log N / Real.log 2 + 2 := h
    _ ≤ (1 / Real.log 2 + 2) * Real.log N := by
      rw [add_mul, one_div_mul_eq_div]
      linarith

end LeanLab.Linnik1951
