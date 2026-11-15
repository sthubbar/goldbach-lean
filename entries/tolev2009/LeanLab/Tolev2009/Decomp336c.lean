module

public import LeanLab.Tolev2009.Decomp336b

/-!
AI wrote this Lean code. Codex task336.
Binary Goldbach is open.
Source: Tolev 1999 page 86 displays 64 to 66.
The exact Type I parent statement follows from the two proved row estimates.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp336c

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a

/-- The exact Type I estimate from the source constant and logarithmic cases.
No cited analytic input is retained. The original parent file remains unchanged. -/
theorem typeI_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ))) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := LeanLab.Tolev2009.Decomp336a.constant_rows A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := LeanLab.Tolev2009.Decomp336a.logarithmic_rows A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize a b ha hb
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  apply (bilinear_norm_le_rows lam l₃ _ N α x M M₁ H H₁ a b ha).trans
  rcases hb with rfl | rfl
  · apply (h₁ N hodd hN₁ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · apply (h₂ N hodd hN₂ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)

end LeanLab.Tolev2009.Decomp336c
