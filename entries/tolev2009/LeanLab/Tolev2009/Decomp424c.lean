module

public import LeanLab.Tolev2009.Decomp424b
public import LeanLab.Tolev2009.Reduction341

/-!
AI wrote this Lean code. Codex task424.
Binary Goldbach is open.
Source: Tolev 1999 page 71 Lemma 4 and page 82 display 52.
The full interval supply is derived from the single annular leaf.
-/

@[expose] public section

open Finset Real
set_option maxHeartbeats 1600000

namespace LeanLab.Tolev2009.Decomp424c

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310c LeanLab.Tolev2009.Decomp424a
open LeanLab.Tolev2009.Decomp424b

/-- The full retained identity follows from the annular leaf and proved shell bookkeeping.
Derived from annular_decomposition. There is no new error input. -/
theorem retained_identity :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
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
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  classical
  intro A hA l₃ hl₃
  obtain ⟨C, X₀, hC, hX₀, hann⟩ := annular_decomposition
  obtain ⟨N₀, hN₀⟩ := eventual_retained_radius A X₀ (by linarith)
  let d : ℝ := 1 / Real.log 2 + 2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨C * d + C, N₀, by positivity, ?_⟩
  intro N hodd hN lam hlam α
  obtain ⟨hL, hY⟩ := hN₀ N hN
  let y : ℝ := (N : ℝ) * Real.log N ^ (-4 * A)
  let t : ℕ := Nat.clog 2 N
  let r : Fin t → ℝ := fun i => y * 2 ^ (i : ℕ)
  have hy : 1 ≤ y := by dsimp [y]; linarith
  have hr : ∀ i : Fin t, y ≤ r i := by
    intro i
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
  have hall : ∀ i : Fin t,
      ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
      ∃ M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
        annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i) =
          ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i)
            (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
        ∀ j : Fin J,
          r i ≤ N ∧ ‖c j‖ ≤ C ∧
          0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
          0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
          (r i) / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * (r i) ∧
          (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
          (((r i) ^ ((249 : ℝ) / 500) ≤ H j ∧
              (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
            ((r i) ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * (r i) ^ ((1 : ℝ) / 3) ∧
              ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
    intro i
    by_cases hi : r i ≤ N
    · obtain ⟨J, hJ, M, M₁, H, H₁, a, b, c, he, hb⟩ :=
        hann N hL (r i) (hY.trans (hr i)) hi lam l₃ _ α
      exact ⟨J, hJ, M, M₁, H, H₁, a, b, c, he, fun j => ⟨hi, hb j⟩⟩
    · refine ⟨0, ?_, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
        Fin.elim0, Fin.elim0, Fin.elim0, ?_, fun j => Fin.elim0 j⟩
      · simpa using mul_nonneg hC (pow_nonneg (show 0 ≤ Real.log N by linarith) 6)
      · simpa using annularMangoldt_eq_zero lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i)
          (le_of_not_ge hi)
  choose Js hJs M M₁ H H₁ a b c he hb using hall
  let U := (i : Fin t) × Fin (Js i)
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  have hcard : (Fintype.card U : ℝ) = ∑ i : Fin t, (Js i : ℝ) := by
    simp [U, Fintype.card_sigma, Nat.cast_sum]
  refine ⟨Fintype.card U, ?_, (fun j => r (e.symm j).1),
    (fun j => M (e.symm j).1 (e.symm j).2), (fun j => M₁ (e.symm j).1 (e.symm j).2),
    (fun j => H (e.symm j).1 (e.symm j).2), (fun j => H₁ (e.symm j).1 (e.symm j).2),
    (fun j => a (e.symm j).1 (e.symm j).2), (fun j => b (e.symm j).1 (e.symm j).2),
    (fun j => c (e.symm j).1 (e.symm j).2), ?_, ?_⟩
  · calc
      (Fintype.card U : ℝ) = ∑ i : Fin t, (Js i : ℝ) := hcard
      _ ≤ ∑ i : Fin t, C * Real.log N ^ (6 : ℕ) := sum_le_sum (fun i _ => hJs i)
      _ = (t : ℝ) * (C * Real.log N ^ (6 : ℕ)) := by simp
      _ ≤ (d * Real.log N) * (C * Real.log N ^ (6 : ℕ)) :=
        mul_le_mul_of_nonneg_right (shell_count_le N hL) (by positivity)
      _ = (C * d) * Real.log N ^ (7 : ℕ) := by ring
      _ ≤ (C * d + C) * Real.log N ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hcover : (N : ℝ) ≤ y * 2 ^ t := by
      have hp : (N : ℝ) ≤ 2 ^ t := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) N
      exact hp.trans (le_mul_of_one_le_left (by positivity) hy)
    calc
      retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α =
          ∑ i : Fin t, annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i) := by
        change _ = ∑ i : Fin t, annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
          (y * 2 ^ (i : ℕ))
        exact (retainedMangoldt_eq_annuli A lam l₃ _ N t α hcover).trans
          (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
            annularMangoldt lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (y * 2 ^ j)) t).symm
      _ = ∑ i : Fin t, ∑ j : Fin (Js i), c i j *
          bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r i)
            (M i j) (M₁ i j) (H i j) (H₁ i j) (a i j) (b i j) := by simp_rw [he]
      _ = ∑ u : U, c u.1 u.2 * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r u.1)
            (M u.1 u.2) (M₁ u.1 u.2) (H u.1 u.2) (H₁ u.1 u.2) (a u.1 u.2) (b u.1 u.2) :=
        (Fintype.sum_sigma (fun u : U => c u.1 u.2 *
          bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α (r u.1)
            (M u.1 u.2) (M₁ u.1 u.2) (H u.1 u.2) (H₁ u.1 u.2) (a u.1 u.2) (b u.1 u.2))).symm
      _ = _ := (e.symm.sum_comp _).symm
  · intro j
    let u := e.symm j
    have hh := hb u.1 u.2
    exact ⟨hh.2.1.trans (by nlinarith [mul_nonneg hC hd]),
      hr u.1, hh.1, by linarith [hY.trans (hr u.1)], hh.2.2⟩

/-- The exact sealed prime decomposition supplied by the annular leaf.
Derived from annular_decomposition only. The conversion error is proved.
This final assembly introduces no open proof step. -/
theorem prime_decomposition :
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
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := Decomp424c.retained_identity A hA l₃ hl₃
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

/-- The minor arc supremum now has only the explicit polynomial grouping leaf open.
Derived from Decomp424a.grouped_annular_decomposition.
Source: Tolev 2009 page 4 display 12. -/
theorem minor_arc_sup_leaf : Sup12Uniform :=
  Reduction341.minor_arc_sup_of_retained Decomp424c.retained_identity

/-- The faithful published theorem follows with the grouping leaf as its only open input.
Derived from Decomp424a.grouped_annular_decomposition.
The sealed opaque legacy series is not identified here.
Source: Tolev 2009 page 2 display 5. -/
theorem published_theorem : TheTheorem SeriesIdentification.halupczokSeries :=
  Reduction341.published_theorem_of_retained Decomp424c.retained_identity

end LeanLab.Tolev2009.Decomp424c
