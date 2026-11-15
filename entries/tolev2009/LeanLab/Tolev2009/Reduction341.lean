module

public import LeanLab.Tolev2009.TypeII341
public import LeanLab.Tolev2009.MajorArc341
public import LeanLab.Tolev2009.Decomp336c
public import LeanLab.Tolev2009.Decomp310c
public import LeanLab.Tolev2009.PublishedTheorem

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: Tolev 2009 pages 2 to 4 and Tolev 1999 pages 71 and 82 to 86.
Derived from the exact retained identity of Decomp310c only.
No unconditional main theorem is asserted.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Reduction341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.SeriesIdentification
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp310c

section RetainedIdentity

variable (hretained : ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α =
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)))

include hretained

/-- The exact prime decomposition follows from the proved conversion and the retained identity.
Derived from hretained. Source is Tolev 1999 page 82 display 52. -/
theorem prime_decomposition_of_retained :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ r : ℂ, ‖r‖ ≤ C * N * Real.log N ^ (330 - 4 * A) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α = r +
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := prime_power_and_initial_segment A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := hretained A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨J, hJ, x, M, M₁, H, H₁, a, b, c, he, hb⟩ := h₂ N hodd hN₂ lam hlam α
  refine ⟨J, ?_, Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α -
    retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α, ?_,
    x, M, M₁, H, H₁, a, b, c, ?_, ?_⟩
  · exact hJ.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (by positivity))
  · apply (h₁ N hodd hN₁ lam hlam α).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · rw [he]
    ring
  · intro j
    exact ⟨(hb j).1.trans (le_add_of_nonneg_left hC₁), (hb j).2⟩

/-- The minor arc supremum follows from the two proved bilinear supplies.
Derived from hretained only. Source is Tolev 2009 page 4 display 12. -/
theorem minor_arc_sup_of_retained : Sup12Uniform := by
  intro A hA l₃ hl₃
  obtain ⟨Cᵢ, Nᵢ, hCᵢ, hI⟩ := Decomp336c.typeI_estimate A hA l₃ hl₃
  obtain ⟨Cᵢᵢ, Nᵢᵢ, hCᵢᵢ, hII⟩ := TypeII341.typeII_estimate A hA l₃ hl₃
  obtain ⟨D, ND, hD, hdec⟩ := prime_decomposition_of_retained hretained A hA l₃ hl₃
  refine ⟨D + D ^ 2 * (Cᵢ + Cᵢᵢ), max (max Nᵢ Nᵢᵢ) (max ND 3), by positivity, ?_⟩
  intro lam hlam N hodd hN α hα hminor
  have hNᵢ : Nᵢ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNᵢᵢ : Nᵢᵢ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hND : ND ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : (3 : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  obtain ⟨J, hJ, r, hr, x, M, M₁, H, H₁, a, b, c, he, hb⟩ :=
    hdec N hodd hND lam hlam α
  have hterm : ∀ j : Fin J,
      ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
        (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
        (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A) := by
    intro j
    rcases hb j with ⟨hc, hxlo, hxhi, hx, hM, hMM₁, hM₁, hH, hHH₁, hH₁,
      hprodlo, hprodhi, ha, htype⟩
    rcases htype with ⟨hsize, hbI⟩ | ⟨hlo, hhi, hbII⟩
    · have hi := hI N hodd hNᵢ lam hlam α hα hminor
        (x j) (M j) (M₁ j) (H j) (H₁ j)
        hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize (a j) (b j) ha hbI
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCᵢᵢ) (Nat.cast_nonneg N))
        (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
    · have hi := hII N hodd hNᵢᵢ lam hlam α hα hminor
        (x j) (M j) (M₁ j) (H j) (H₁ j)
        hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi (a j) (b j) ha hbII
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCᵢ) (Nat.cast_nonneg N))
        (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
  have hsum : ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
      (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
      (J : ℝ) * (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j : Fin J, D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A)) := by
        apply sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hb j).1 (hterm j) (norm_nonneg _) hD
      _ = _ := by simp
  have hpow : Real.log N ^ (7 : ℕ) * Real.log N ^ (330 - 4 * A) ≤
      Real.log N ^ (350 - 4 * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith)
  have hpow0 : Real.log N ^ (330 - 4 * A) ≤ Real.log N ^ (350 - 4 * A) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hsum' : ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
      (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
      D ^ 2 * (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (350 - 4 * A) := by
    calc
      _ ≤ (J : ℝ) * (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) := hsum
      _ ≤ (D * Real.log N ^ (7 : ℕ)) *
          (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = D ^ 2 * (Cᵢ + Cᵢᵢ) * N *
          (Real.log N ^ (7 : ℕ) * Real.log N ^ (330 - 4 * A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hpow0
    (show 0 ≤ D * (N : ℝ) by positivity))
  rw [he]
  calc
    _ ≤ ‖r‖ + ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
        (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ := norm_add_le _ _
    _ ≤ D * N * Real.log N ^ (350 - 4 * A) +
        D ^ 2 * (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (350 - 4 * A) := add_le_add hr' hsum'
    _ = _ := by ring

/-- The published theorem follows from the proved major arcs and the minor arc reduction.
Derived from hretained only. Source is Tolev 2009 page 2 display 5. -/
theorem published_theorem_of_retained : TheTheorem halupczokSeries :=
  PublishedTheorem.publishedTheorem_of_display9_sup12 MajorArc341.major_arc_leaf
    (minor_arc_sup_of_retained hretained)

end RetainedIdentity
end LeanLab.Tolev2009.Reduction341
