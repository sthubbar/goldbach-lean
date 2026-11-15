module

public import LeanLab.Tolev2009.Decomp341c

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 83 to 86 displays 55 to 63.
The exact Type II supply uses the proved row energy and coefficient moment.
-/

@[expose] public section

open Finset Real ComplexConjugate
namespace LeanLab.Tolev2009.TypeII341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp310b

/-- The exact Type II bound from the proved coefficient mass and row energy.
Tolev 1999 page 86 display 63 with the sealed full interval adaptation. -/
theorem typeII_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨D, hD, hm⟩ := coefficient_mass
  obtain ⟨C, N₀, hC, he⟩ := Decomp341c.row_energy A hA l₃ hl₃
  refine ⟨D + C + 1, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi a b ha hb
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN3nat : 3 ≤ N := by exact_mod_cast hN3
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith : 1 ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).trans hlo
  have hMbound : M ≤ 2 * N := by nlinarith
  have hmass := hm N hN3nat M M₁ hM hMM₁ hM₁ hMbound a ha
  have henergy := he N hodd hN₀ lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi b hb
  have hE0 : 0 ≤ energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := by
    unfold energy
    positivity
  have hp : Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A) =
      (Real.log N ^ (330 - 4 * A)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL, ← Real.rpow_mul_natCast hL.le]
    congr 1
    ring
  have hs := (bilinear_sq_le_energy lam l₃ _ N α x M M₁ H H₁ a b).trans
    (mul_le_mul_of_nonneg_right hmass hE0)
  have hs' : ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (D * C) * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 := by
    calc
      _ ≤ (D * M * Real.log N ^ (26 : ℕ)) *
          energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := hs
      _ = (D * Real.log N ^ (26 : ℕ)) *
          (M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b) := by ring
      _ ≤ (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by rw [show (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) =
          D * C * (N : ℝ) ^ 2 *
            (Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A)) by ring, hp]
  have hc : D * C ≤ (D + C + 1) ^ 2 := by nlinarith [sq_nonneg (D - C)]
  have hs'' := hs'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ)))
    (sq_nonneg (Real.log N ^ (330 - 4 * A))))
  have ht : (D + C + 1) ^ 2 * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 =
      ((D + C + 1) * N * Real.log N ^ (330 - 4 * A)) ^ 2 := by ring
  rw [ht] at hs''
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs''

end LeanLab.Tolev2009.TypeII341
