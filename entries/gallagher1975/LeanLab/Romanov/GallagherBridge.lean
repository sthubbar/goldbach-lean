module

public import LeanLab.Romanov.Moment
public import LeanLab.Linnik.U7206Display6

/-!
# Gallagher's Lemma 12 from the Romanov second moment

AI wrote the Lean code. Known mathematics. Gallagher 1975, page 138.
The Fourier notation is that of the existing Linnik modules.
Binary Goldbach is OPEN.
-/

@[expose] public section


noncomputable section
namespace LeanLab.Romanov

open Finset Real MeasureTheory
open LeanLab.Linnik.U7204 (cf Sg primesLe integral_SG)
open LeanLab.Linnik.U1434Lemma21 (sv)
open LeanLab.Linnik.U1426ChainWire (Gs)

/-- Every coefficient of `S G` counts a subset of the full Romanov representations. -/
theorem cf_one_le_repCount (N L n : ℕ) : cf 1 N L n ≤ repCount n := by
  classical
  have hcf : cf 1 N L n =
      (#{x ∈ primesLe N ×ˢ (univ : Finset (Fin 1 → Fin L)) |
        x.1 + sv x.2 = n} : ℕ) := by
    unfold cf
    rw [card_filter, ← sum_product']
    push_cast
    rfl
  rw [hcf]
  apply Nat.cast_le.mpr
  unfold repCount
  apply card_le_card_of_injOn (fun x : ℕ × (Fin 1 → Fin L) => (x.1, (x.2 0 : ℕ) + 1))
  · intro x hx
    simp only [mem_coe, mem_filter, mem_product, mem_univ, and_true] at hx
    rw [mem_coe, mem_representations]
    have hp := (mem_filter.mp hx.1).2
    refine ⟨hp, ?_, ?_⟩
    · change 1 ≤ (x.2 0 : ℕ) + 1
      omega
    · simpa [f, sv] using hx.2
  · intro a ha b hb hab
    have hp : a.1 = b.1 := congrArg (fun z : ℕ × ℕ => z.1) hab
    have hk : (a.2 0 : ℕ) = (b.2 0 : ℕ) := by
      have := congrArg (fun z : ℕ × ℕ => z.2) hab
      simp only at this
      omega
    apply Prod.ext hp
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    exact Fin.ext hk

/-- Gallagher's Lemma 12 with an explicit absolute constant. -/
theorem gallagher_integral_le (N : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α‖ ^ 2 ≤
      8 * (9 + 2 * R₁) * N := by
  by_cases hN : N = 0
  · subst N
    simp [Gs]
  have hpow := Nat.pow_log_le_self 2 hN
  have hparseval := integral_SG 1 N (Nat.log 2 N) (2 * N + 1) (by omega)
  simp only [pow_one] at hparseval
  rw [hparseval]
  calc ∑ n ∈ range (2 * N + 1), cf 1 N (Nat.log 2 N) n ^ 2
      ≤ ∑ n ∈ range (2 * N + 1), (repCount n : ℝ) ^ 2 := by
        apply sum_le_sum
        intro n _
        exact pow_le_pow_left₀ (LeanLab.Linnik.U7204.cf_nonneg _ _ _ _) (cf_one_le_repCount _ _ _) 2
    _ ≤ 4 * (9 + 2 * R₁) * (2 * N : ℕ) := romanov_second_moment (2 * N)
    _ = 8 * (9 + 2 * R₁) * N := by push_cast; ring

/-- The cited Lemma12 input is now discharged. -/
theorem gallagher_lemma12 : LeanLab.Linnik.U7206.Lemma12 :=
  ⟨8 * (9 + 2 * R₁), gallagher_integral_le⟩

/-- Gallagher display 6, conditional only on its large k case. -/
theorem gallagher_display6_of_large (h : LeanLab.Linnik.U7206.Display6Large) :
    LeanLab.Linnik.U7204.Display6 :=
  LeanLab.Linnik.U7206.display6_of h gallagher_lemma12

/-- Gallagher Theorem 1, conditional only on the large k estimate. -/
theorem gallagher_theorem1_of_large (h : LeanLab.Linnik.U7206.Display6Large) :
    LeanLab.Linnik.Gallagher1975.Theorem1 :=
  LeanLab.Linnik.U7206.theorem1_of_large h gallagher_lemma12

/-- Gallagher Theorem 2 for base two, conditional only on the large k estimate. -/
theorem gallagher_theorem2_of_large (h : LeanLab.Linnik.U7206.Display6Large) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(LeanLab.Linnik.Gallagher1975Thm2.rpp k N : ℝ) -
        2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  LeanLab.Linnik.U7206.theorem2_of_large h gallagher_lemma12

/-- The explicit pointwise bound alone has a constant above Gallagher's leading two. -/
theorem gallagher_pointwise_constant_gt_two :
    2 < 8 * (9 + 2 * R₁) * Real.log 2 ^ 2 := by
  have hl := Real.log_two_gt_d9
  norm_num at hl
  have hsq : (1 / 4 : ℝ) < Real.log 2 ^ 2 := by nlinarith
  have hp : 0 ≤ R₁ * Real.log 2 ^ 2 := mul_nonneg R₁_pos.le (sq_nonneg _)
  nlinarith

/-- The Lemma 12 step on a measurable arc, with no cited input. -/
theorem gallagher_arc_le {k : ℕ} (hk : 1 ≤ k) (N : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAs : A ⊆ Set.Icc 0 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ α ∈ A, ‖Gs (Nat.log 2 N) α‖ ≤ M) :
    ∫ α in A, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      M ^ (2 * k - 2) * (8 * (9 + 2 * R₁) * N) := by
  exact (LeanLab.Linnik.U7206.arc_bound hk N (Nat.log 2 N) hA hAs hM0 hM).trans
    (mul_le_mul_of_nonneg_left (gallagher_integral_le N) (pow_nonneg hM0 _))

/-- The elementary k to the minus two decay in Gallagher's page 139 argument. -/
theorem gallagher_eta_decay (k : ℕ) (hk : 2 ≤ k) :
    (1 - Real.log k / k) ^ (2 * k - 2) ≤ Real.exp 2 / (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog := Real.log_le_sub_one_of_pos hk0
  have hratio : Real.log k / k ≤ 1 := (div_le_one hk0).mpr (by linarith)
  have hbase : 0 ≤ 1 - Real.log k / k := by linarith
  have hexp : 1 - Real.log k / k ≤ Real.exp (-(Real.log k / k)) := by
    have h := Real.add_one_le_exp (-(Real.log k / k))
    linarith
  have hn : ((2 * k - 2 : ℕ) : ℝ) = 2 * (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have heq : ((2 * k - 2 : ℕ) : ℝ) * (-(Real.log k / k)) =
      -2 * Real.log k + 2 * (Real.log k / k) := by
    rw [hn]
    field_simp; ring
  calc (1 - Real.log k / k) ^ (2 * k - 2)
      ≤ (Real.exp (-(Real.log k / k))) ^ (2 * k - 2) :=
        pow_le_pow_left₀ hbase hexp _
    _ = Real.exp (((2 * k - 2 : ℕ) : ℝ) * (-(Real.log k / k))) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (2 - 2 * Real.log k) := Real.exp_le_exp.mpr (by rw [heq]; linarith)
    _ = Real.exp 2 / (k : ℝ) ^ 2 := by
        rw [Real.exp_sub]
        have hlogpow : 2 * Real.log k = Real.log ((k : ℝ) ^ 2) := by
          rw [Real.log_pow]
          norm_num
        rw [hlogpow, Real.exp_log (pow_pos hk0 2)]

/-- The small G arc contributes at most an explicit k to the minus two term. -/
theorem gallagher_eta_arc_le {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAs : A ⊆ Set.Icc 0 1)
    (hM : ∀ α ∈ A, ‖Gs (Nat.log 2 N) α‖ ≤
      (1 - Real.log k / k) * (Nat.log 2 N : ℝ)) :
    ∫ α in A, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      (Real.exp 2 / (k : ℝ) ^ 2) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) *
        (8 * (9 + 2 * R₁) * N) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog := Real.log_le_sub_one_of_pos hk0
  have hb : 0 ≤ 1 - Real.log k / k := by
    have hr : Real.log k / k ≤ 1 := (div_le_one hk0).mpr (by linarith)
    linarith
  have hR := R₁_pos
  calc ∫ α in A, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2
      ≤ ((1 - Real.log k / k) * (Nat.log 2 N : ℝ)) ^ (2 * k - 2) *
          (8 * (9 + 2 * R₁) * N) :=
        gallagher_arc_le (by omega) N hA hAs (mul_nonneg hb (Nat.cast_nonneg _)) hM
    _ = (1 - Real.log k / k) ^ (2 * k - 2) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) *
          (8 * (9 + 2 * R₁) * N) := by rw [mul_pow]
    _ ≤ (Real.exp 2 / (k : ℝ) ^ 2) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) *
          (8 * (9 + 2 * R₁) * N) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (gallagher_eta_decay k hk) (by positivity)) (by positivity)

end LeanLab.Romanov
