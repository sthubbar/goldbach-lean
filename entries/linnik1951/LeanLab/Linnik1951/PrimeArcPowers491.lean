module

public import Mathlib

/-!
P0093 page 159. The proper prime powers, which the logarithm of the L function
carries and the prime series does not. Their damped count is of size square root
of N, an elementary bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 159 passes from the logarithm of L to the prime series without
mentioning the proper prime powers; this is the formalizer's filling. The weight of a
natural number in the logarithm of zeta minus its weight in the prime series is
one over k at a proper prime power p to the k and zero elsewhere, so it is
nonnegative. -/
theorem proper_power_weight_nonneg491 (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0) := by
  by_cases hp : n.Prime
  · have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp only [hp, ↓reduceIte]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hl, sub_self]
  · simp only [hp, ↓reduceIte, sub_zero]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

private lemma weight_le_one491 (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0) ≤ 1 := by
  have h1 : ArithmeticFunction.vonMangoldt n / Real.log n ≤ 1 :=
    div_le_one_of_le₀ ArithmeticFunction.vonMangoldt_le_log (Real.log_natCast_nonneg n)
  have h2 : (0 : ℝ) ≤ (if n.Prime then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  linarith

private lemma weight_ne_zero491 (n : ℕ)
    (h : ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0) ≠ 0) :
    ∃ a k : ℕ, (a + 2) ^ (k + 2) = n := by
  by_cases hp : n.Prime
  · exfalso
    apply h
    have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp only [hp, ↓reduceIte]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hl, sub_self]
  · have hL : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro h0
      apply h
      simp [h0, hp]
    rw [Ne, ArithmeticFunction.vonMangoldt_eq_zero_iff, not_not] at hL
    obtain ⟨p, k, hpp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hL
    have hk2 : 2 ≤ k := by
      by_contra hk'
      have : k = 1 := by omega
      subst this
      exact hp (by simpa using hpp)
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hpp.two_le
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk2
    exact ⟨a, j, rfl⟩

private lemma sum_split491 (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) (L M : ℕ) :
    ∑ x ∈ range M, f x ≤ ∑ x ∈ range L, f x + ∑ j ∈ range M, f (L + j) := by
  rw [← Finset.sum_range_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun x _ _ => hf x)

private lemma exp_neg_le_inv491 (t : ℝ) (ht : 0 < t) : Real.exp (-t) ≤ 1 / t := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ ht (by linarith [Real.add_one_le_exp t])

private lemma tele491 (m : ℕ) (hm : 1 ≤ m) (K : ℕ) :
    ∑ j ∈ range K, 1 / (((m + 1 + j : ℕ) : ℝ)) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hx : (0 : ℝ) < (m : ℝ) + K := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      positivity
    have key : 1 / (((m + 1 + K : ℕ) : ℝ)) ^ 2 ≤ 1 / ((m : ℝ) + K) - 1 / ((m : ℝ) + (K + 1 : ℕ)) := by
      push_cast
      rw [div_sub_div _ _ hx.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private lemma sumA491 (N M : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ range M, Real.exp (-((a : ℝ) ^ 2 / (2 * N))) ≤ 8 * Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set m := Nat.sqrt N + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hNm : (N : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : N < m ^ 2 := by rw [hm]; exact Nat.lt_succ_sqrt' N
    exact_mod_cast this.le
  have h0 := sum_split491 (fun a : ℕ => Real.exp (-((a : ℝ) ^ 2 / (2 * N))))
    (fun x => (Real.exp_pos _).le) (m + 1) M
  have h1 : ∑ a ∈ range (m + 1), Real.exp (-((a : ℝ) ^ 2 / (2 * N))) ≤ (m : ℝ) + 1 := by
    calc ∑ a ∈ range (m + 1), Real.exp (-((a : ℝ) ^ 2 / (2 * N)))
        ≤ ∑ a ∈ range (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ (a : ℝ) ^ 2 / (2 * N) := by positivity
          linarith
      _ = (m : ℝ) + 1 := by simp
  have h2 : ∑ j ∈ range M, Real.exp (-((((m + 1 + j : ℕ) : ℝ)) ^ 2 / (2 * N))) ≤ 2 * (m : ℝ) := by
    calc ∑ j ∈ range M, Real.exp (-((((m + 1 + j : ℕ) : ℝ)) ^ 2 / (2 * N)))
        ≤ ∑ j ∈ range M, 2 * (m : ℝ) ^ 2 * (1 / (((m + 1 + j : ℕ) : ℝ)) ^ 2) := by
          apply Finset.sum_le_sum
          intro j _
          have hpos : (0 : ℝ) < (((m + 1 + j : ℕ) : ℝ)) ^ 2 := by
            have : (0 : ℝ) < ((m + 1 + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1 + j)
            positivity
          refine (exp_neg_le_inv491 _ (by positivity)).trans ?_
          rw [one_div_div, mul_one_div]
          apply div_le_div_of_nonneg_right _ hpos.le
          linarith
      _ = 2 * (m : ℝ) ^ 2 * ∑ j ∈ range M, 1 / (((m + 1 + j : ℕ) : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (m : ℝ) ^ 2 * (1 / (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := tele491 m hm1 M
          have h3 : (0 : ℝ) ≤ 1 / ((m : ℝ) + M) := by positivity
          linarith
      _ = 2 * (m : ℝ) := by field_simp
  have hs : (m : ℝ) ≤ 2 * Real.sqrt N := by
    have ha : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    have hb : (1 : ℝ) ≤ Real.sqrt N := by
      rw [Real.one_le_sqrt]; exact_mod_cast hN
    rw [hm]; push_cast; linarith
  linarith

private lemma sumB491 (N M : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) ≤ 5 * (Real.log N + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set L := Nat.log 2 N + 1 with hL
  have hNL : (N : ℝ) ≤ (2 : ℝ) ^ L := by
    have : N < 2 ^ L := by rw [hL]; exact Nat.lt_pow_succ_log_self (by norm_num) N
    exact_mod_cast this.le
  have h0 := sum_split491 (fun k : ℕ => Real.exp (-((2 : ℝ) ^ k / (2 * N))))
    (fun x => (Real.exp_pos _).le) L M
  have h1 : ∑ k ∈ range L, Real.exp (-((2 : ℝ) ^ k / (2 * N))) ≤ (L : ℝ) := by
    calc ∑ k ∈ range L, Real.exp (-((2 : ℝ) ^ k / (2 * N)))
        ≤ ∑ k ∈ range L, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ (2 : ℝ) ^ a / (2 * N) := by positivity
          linarith
      _ = (L : ℝ) := by simp
  have h2 : ∑ j ∈ range M, Real.exp (-((2 : ℝ) ^ (L + j) / (2 * N))) ≤ 4 := by
    calc ∑ j ∈ range M, Real.exp (-((2 : ℝ) ^ (L + j) / (2 * N)))
        ≤ ∑ j ∈ range M, 2 * (1 / 2 : ℝ) ^ j := by
          apply Finset.sum_le_sum
          intro j _
          refine (exp_neg_le_inv491 _ (by positivity)).trans ?_
          rw [one_div_div, one_div_pow, mul_one_div, pow_add,
            div_le_div_iff₀ (by positivity) (by positivity)]
          have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
          nlinarith
      _ = 2 * ∑ j ∈ range M, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ 2 * 2 := by
          apply mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by norm_num)
      _ = 4 := by norm_num
  have hlog : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have hp : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h3 := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at h3
    have h4 := Real.log_two_gt_d9
    have h5 : (0 : ℝ) ≤ (Nat.log 2 N : ℕ) := by positivity
    nlinarith
  have hLR : (L : ℝ) = (Nat.log 2 N : ℕ) + 1 := by rw [hL]; push_cast; ring
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  linarith

private lemma pair_bound491 (N a k : ℕ) (hN : 1 ≤ N) :
    Real.exp (-((((a + 2) ^ (k + 2) : ℕ) : ℝ) / N)) ≤
      Real.exp (-((a : ℝ) ^ 2 / (2 * N))) * Real.exp (-((2 : ℝ) ^ k / (2 * N))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.exp_add, Real.exp_le_exp]
  have ha : a ^ 2 ≤ (a + 2) ^ (k + 2) :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hk : 2 ^ k ≤ (a + 2) ^ (k + 2) :=
    (Nat.pow_le_pow_right (by omega) (by omega : k ≤ k + 2)).trans
      (Nat.pow_le_pow_left (by omega) _)
  have ha' : (a : ℝ) ^ 2 ≤ (((a + 2) ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast ha
  have hk' : (2 : ℝ) ^ k ≤ (((a + 2) ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hk
  have e : -((a : ℝ) ^ 2 / (2 * N)) + -((2 : ℝ) ^ k / (2 * N)) =
      -((((a : ℝ) ^ 2 + (2 : ℝ) ^ k) / 2) / N) := by field_simp; ring
  rw [e, neg_le_neg_iff]
  apply div_le_div_of_nonneg_right _ hN0.le
  linarith

/-- P0093 page 159 passes from the logarithm of L to the prime series without
mentioning the proper prime powers; this elementary bound is the formalizer's
filling. The damped sum of
the proper prime power weights is at most a constant times the square root of N
times ln N plus one, uniformly in the truncation. -/
theorem proper_power_damped491 : ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, 1 ≤ N →
    ∑ n ∈ range M, Real.exp (-(n / N : ℝ)) *
      (ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0)) ≤
      C * Real.sqrt N * (Real.log N + 1) := by
  refine ⟨40, by norm_num, fun N M hN => ?_⟩
  have h1 : ∀ n ∈ range M, Real.exp (-(n / N : ℝ)) *
      (ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0)) ≤
      ∑ p ∈ range M ×ˢ range M,
        (if (p.1 + 2) ^ (p.2 + 2) = n then Real.exp (-(n / N : ℝ)) else 0) := by
    intro n hn
    have hnM : n < M := Finset.mem_range.1 hn
    have hnn : ∀ q ∈ range M ×ˢ range M, (0 : ℝ) ≤
        (if (q.1 + 2) ^ (q.2 + 2) = n then Real.exp (-(n / N : ℝ)) else 0) := by
      intro q _
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    by_cases h0 : ArithmeticFunction.vonMangoldt n / Real.log n -
        (if n.Prime then (1 : ℝ) else 0) = 0
    · rw [h0, mul_zero]
      exact Finset.sum_nonneg hnn
    · obtain ⟨a, k, hak⟩ := weight_ne_zero491 n h0
      have ha : a + 2 ≤ (a + 2) ^ (k + 2) := Nat.le_self_pow (by omega) _
      have hk : k + 2 < (a + 2) ^ (k + 2) :=
        (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by omega) _)
      have hmem : (a, k) ∈ range M ×ˢ range M := by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        constructor <;> simp only <;> omega
      calc Real.exp (-(n / N : ℝ)) *
            (ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0))
          ≤ Real.exp (-(n / N : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left (weight_le_one491 n) (Real.exp_pos _).le
        _ = (if (((a, k) : ℕ × ℕ).1 + 2) ^ (((a, k) : ℕ × ℕ).2 + 2) = n
              then Real.exp (-(n / N : ℝ)) else 0) := by simp [hak]
        _ ≤ _ := Finset.single_le_sum hnn hmem
  have h2 : ∑ n ∈ range M, ∑ p ∈ range M ×ˢ range M,
        (if (p.1 + 2) ^ (p.2 + 2) = n then Real.exp (-(n / N : ℝ)) else 0) ≤
      ∑ p ∈ range M ×ˢ range M,
        Real.exp (-((((p.1 + 2) ^ (p.2 + 2) : ℕ) : ℝ) / N)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro p _
    rw [Finset.sum_ite_eq]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have h3 : ∑ p ∈ range M ×ˢ range M,
        Real.exp (-((((p.1 + 2) ^ (p.2 + 2) : ℕ) : ℝ) / N)) ≤
      (∑ a ∈ range M, Real.exp (-((a : ℝ) ^ 2 / (2 * N)))) *
        ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_le_sum
    intro p _
    exact pair_bound491 N p.1 p.2 hN
  have hA := sumA491 N M hN
  have hB := sumB491 N M hN
  have hBn : (0 : ℝ) ≤ ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have h4 : (∑ a ∈ range M, Real.exp (-((a : ℝ) ^ 2 / (2 * N)))) *
        ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) ≤
      (8 * Real.sqrt N) * (5 * (Real.log N + 1)) :=
    mul_le_mul hA hB hBn (by positivity)
  calc _ ≤ _ := Finset.sum_le_sum h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
    _ = 40 * Real.sqrt N * (Real.log N + 1) := by ring

end LeanLab.Linnik1951
