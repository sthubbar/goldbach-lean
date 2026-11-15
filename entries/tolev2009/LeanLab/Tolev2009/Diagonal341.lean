module

public import LeanLab.Tolev2009.Progressions341

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 page 84 displays 56 to 58.
The diagonal bound includes the progression endpoint term.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Diagonal341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286b LeanLab.Tolev2009.Decomp310b
open LeanLab.Tolev2009.Decomp341a LeanLab.Tolev2009.Progressions341
open LeanLab.HeathBrown1985

/-- Dropping the positive divisor weights in display 58 preserves its bound. -/
theorem unweighted_lcm_sum (K : ℕ) :
    ∑ p ∈ Icc 1 K ×ˢ Icc 1 K, (1 : ℝ) / Nat.lcm p.1 p.2 ≤ Hn (K*K) ^ (16 : ℕ) := by
  apply (sum_le_sum (fun p hp => ?_)).trans (lcm_divisor_sum K)
  obtain ⟨h₁,h₂⟩ := mem_product.mp hp
  have hc₁ : (1 : ℝ) ≤ p.1.divisors.card := by
    exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp h₁).1; omega))
  have hc₂ : (1 : ℝ) ≤ p.2.divisors.card := by
    exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr (by have := (mem_Icc.mp h₂).1; omega))
  exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

/-- The exact diagonal regrouping before Tolev 1999 display 56. -/
theorem diagonal_eq (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) :
    diagonal l₃ K N α x M M₁ H H₁ =
      ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2 *
        ∑ k₁ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ∑ k₂ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          ‖correlation l₃ N α x M M₁ (l,k₁) (l,k₂)‖ := by
  classical
  simp only [diagonal, indices, sum_product]
  apply sum_congr rfl
  intro l hl
  rw [mul_sum]
  apply sum_congr rfl
  intro k₁ hk₁
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro k₂ hk₂
  simp only [sum_ite_eq, hl, ite_true, pow_two]

/-- The diagonal progression bound with its lcm sum and endpoint count separated.
This is the finite arithmetic content of Tolev 1999 display 56. -/
theorem diagonal_le_separated (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) :
    diagonal l₃ K N α x M M₁ H H₁ ≤
      (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ) ^ 2) *
        (2*M*Hn (K*K) ^ (16 : ℕ) + (K : ℝ)^2) := by
  classical
  rw [diagonal_eq, sum_mul]
  apply sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ k₁ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ∑ k₂ ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
          (2*M / Nat.lcm k₁ k₂ + 1) := by
      apply sum_le_sum
      intro k₁ hk₁
      apply sum_le_sum
      intro k₂ hk₂
      exact correlation_diagonal_bound l₃ N α x M M₁ l k₁ k₂
        (mem_Icc.mp (mem_filter.mp hk₁).1).1 (mem_Icc.mp (mem_filter.mp hk₂).1).1
        (mem_filter.mp hk₁).2 (mem_filter.mp hk₂).2 hM hM₁
    _ ≤ ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K, (2*M / Nat.lcm k₁ k₂ + 1) := by
      apply (sum_le_sum (fun k₁ hk₁ =>
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₂ hk₂ hnot => by positivity))).trans
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k₁ hk₁ hnot =>
        sum_nonneg (fun k₂ hk₂ => by positivity))
    _ = 2*M*(∑ p ∈ Icc 1 K ×ˢ Icc 1 K, (1:ℝ) / Nat.lcm p.1 p.2) + (K:ℝ)^2 := by
      simp only [← sum_product', sum_add_distrib, sum_const, card_product,
        Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul, nsmul_eq_mul, mul_one, mul_sum]
      congr 1
      · apply sum_congr rfl
        intro p hp
        ring
      · ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (unweighted_lcm_sum K) (show 0 ≤ 2*M by positivity)) le_rfl

/-- The unweighted tau5 square mean in the diagonal part of display 56. -/
theorem tau5_square_sum (H H₁ : ℝ) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H) :
    ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (tau5 l : ℝ)^2 ≤
      2*H*Hn ⌊2*H⌋₊ ^ (24 : ℕ) := by
  have hs : Ioc ⌊H⌋₊ ⌊H₁⌋₊ ⊆ Icc 1 ⌊2*H⌋₊ := by
    intro l hl
    obtain ⟨hl0,hl1⟩ := mem_Ioc.mp hl
    exact mem_Icc.mpr ⟨by omega,hl1.trans (Nat.floor_le_floor hH₁)⟩
  calc
    _ ≤ ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (((ArithmeticFunction.zeta ^ 25) l : ℕ) : ℝ) := by
      apply sum_le_sum
      intro l hl
      exact_mod_cast tau5_sq_le_zeta25 l
    _ ≤ ∑ l ∈ Icc 1 ⌊2*H⌋₊, (((ArithmeticFunction.zeta ^ 25) l : ℕ) : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hs (fun l hl hnot => Nat.cast_nonneg _)
    _ ≤ (⌊2*H⌋₊ : ℝ) * Hn ⌊2*H⌋₊ ^ (24 : ℕ) := zeta_power_sum 24 _
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)

/-- A fully explicit finite diagonal bound for Tolev 1999 display 56.
The final K squared term records progression endpoints. -/
theorem diagonal_finite_bound (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2*M) (hH : 0 < H) (hH₁ : H₁ ≤ 2*H) :
    diagonal l₃ K N α x M M₁ H H₁ ≤
      (2*H*Hn ⌊2*H⌋₊ ^ (24 : ℕ)) *
        (2*M*Hn (K*K) ^ (16 : ℕ) + (K : ℝ)^2) := by
  exact (diagonal_le_separated l₃ K N α x M M₁ H H₁ hM hM₁).trans
    (mul_le_mul_of_nonneg_right (tau5_square_sum H H₁ hH hH₁) (by positivity))

end LeanLab.Tolev2009.Diagonal341
