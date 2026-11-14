module

public import LeanLab.Linnik.Task37Diagonal

/-!
Li and Liu, https://arxiv.org/pdf/2610.15784, pages 5 and 6, display 19.
Fix two exponents on one side and use uniqueness of a sum of two powers.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Task37Display19
open Finset
open LeanLab.Linnik.U1434Lemma21 (sv)
open LeanLab.Linnik.U1447Display30

/-- At most two ordered pairs of exponents give a prescribed sum. -/
lemma pair_le_two (L A B : ℕ) :
    (∑ x : Fin L, ∑ y : Fin L,
      if 2 ^ ((x : ℕ) + 1) + 2 ^ ((y : ℕ) + 1) + A = B then (1 : ℝ) else 0) ≤ 2 := by
  rw [← Fintype.sum_prod_type', Finset.sum_boole]
  let S := (univ : Finset (Fin L × Fin L)).filter fun p =>
    2 ^ ((p.1 : ℕ) + 1) + 2 ^ ((p.2 : ℕ) + 1) + A = B
  change (S.card : ℝ) ≤ 2
  have hc : S.card ≤ 2 := by
    by_cases hn : S.Nonempty
    · obtain ⟨⟨a, b⟩, hab⟩ := hn
      have hab' : 2 ^ ((a : ℕ) + 1) + 2 ^ ((b : ℕ) + 1) + A = B :=
        (mem_filter.mp hab).2
      have hsub : S ⊆ {(a, b), (b, a)} := by
        rintro ⟨x, y⟩ hxy
        have hxy' : 2 ^ ((x : ℕ) + 1) + 2 ^ ((y : ℕ) + 1) + A = B :=
          (mem_filter.mp hxy).2
        have he : 2 ^ ((x : ℕ) + 1) + 2 ^ ((y : ℕ) + 1) =
            2 ^ ((a : ℕ) + 1) + 2 ^ ((b : ℕ) + 1) := by omega
        rcases pow_pair _ _ _ _ he with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · have hx' : x = a := Fin.ext (by omega)
          have hy' : y = b := Fin.ext (by omega)
          simp [hx', hy']
        · have hx' : x = b := Fin.ext (by omega)
          have hy' : y = a := Fin.ext (by omega)
          simp [hx', hy']
      exact (card_le_card hsub).trans (Finset.card_le_two)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  exact_mod_cast hc

/-- Fix all exponents except two on the left side. -/
lemma Dc_two_left (I J L : ℕ) : Dc (I + 2) J L ≤ 2 * (L : ℝ) ^ (I + J) := by
  unfold Dc
  rw [U1466Display17.sum_cons, U1466Display17.sum_cons]
  simp_rw [U1466Display17.sv_cons]
  calc
    _ = ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L,
      ∑ x : Fin L, ∑ y : Fin L,
        if 2 ^ ((x : ℕ) + 1) + 2 ^ ((y : ℕ) + 1) + sv ν = sv μ then (1 : ℝ) else 0 := by
      refine sum_congr rfl fun ν _ => ?_
      rw [sum_congr rfl fun _ _ => Finset.sum_comm]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun μ _ => ?_
      rw [Finset.sum_comm]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      simp only [Nat.add_assoc]
    _ ≤ ∑ _ν : Fin I → Fin L, ∑ _μ : Fin J → Fin L, (2 : ℝ) :=
      sum_le_sum fun ν _ => sum_le_sum fun μ _ => pair_le_two L (sv ν) (sv μ)
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [pow_add]
      ring

lemma Dc_symm (I J L : ℕ) : Dc I J L = Dc J I L := by
  unfold Dc
  rw [Finset.sum_comm]
  refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => ?_
  simp only [eq_comm]

/-- The exact printed constant in display 19. -/
theorem display19 (i j : Fin 3) (L : ℕ) (hij : ¬ (i = 0 ∧ j = 0)) :
    Dc ((i : ℕ) + 1) ((j : ℕ) + 1) L ≤ 2 * (L : ℝ) ^ ((i : ℕ) + j) := by
  have h10 := Dc_two_left 0 1 L
  have h11 := Dc_two_left 0 2 L
  have h12 := Dc_two_left 0 3 L
  have h20 := Dc_two_left 1 1 L
  have h21 := Dc_two_left 1 2 L
  have h22 := Dc_two_left 1 3 L
  have h01 : Dc 1 2 L ≤ 2 * (L : ℝ) := by simpa [Dc_symm] using h10
  have h02 : Dc 1 3 L ≤ 2 * (L : ℝ) ^ 2 := by simpa [Dc_symm] using h20
  fin_cases i <;> fin_cases j <;> simp_all

/-- A nonempty diagonal example at the largest index pair. -/
theorem diagonal_instance : Dc 3 3 5 ≤ 2 * (5 : ℝ) ^ 4 :=
  display19 2 2 5 (by decide)

end LeanLab.Linnik.Task37Display19

