module

public import LeanLab.Tolev2009.Decomp341a

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 84 to 85 displays 59 to 60.
Finite shifted coefficient counting before the scalar phase estimate.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Shifted341

/-- At each positive distance a fixed integer has at most two partners.
This is the signed difference count in Tolev 1999 display 59. -/
theorem distance_sum_le (S : Finset ℕ) (U l : ℕ) (hl : l ≤ U)
    (hS : ∀ j ∈ S, j ≤ U) (F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r) :
    ∑ j ∈ S, (if l ≠ j then F (Nat.dist l j) else 0) ≤
      2*∑ r ∈ Icc 1 U, F r := by
  classical
  have hlow : ∑ j ∈ S.filter (fun j => j<l), F (l-j) ≤ ∑ r ∈ Icc 1 U, F r := by
    have hi : Set.InjOn (fun j => l-j) (S.filter (fun j => j<l)) := by
      intro a ha b hb he
      dsimp only at he
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      omega
    rw [← sum_image hi]
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hr
      have hj' := (mem_filter.mp hj).2
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro r hr hnot
      exact hF r
  have hhigh : ∑ j ∈ S.filter (fun j => l<j), F (j-l) ≤ ∑ r ∈ Icc 1 U, F r := by
    have hi : Set.InjOn (fun j => j-l) (S.filter (fun j => l<j)) := by
      intro a ha b hb he
      dsimp only at he
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      omega
    rw [← sum_image hi]
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hr
      have hj' := mem_filter.mp hj
      have hjU := hS j hj'.1
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro r hr hnot
      exact hF r
  have he : (∑ j ∈ S, if l ≠ j then F (Nat.dist l j) else 0) =
      (∑ j ∈ S.filter (fun j => j<l), F (l-j)) +
      (∑ j ∈ S.filter (fun j => l<j), F (j-l)) := by
    simp only [sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rcases lt_trichotomy j l with h|h|h
    · simp [show l≠j by omega,h,show ¬l<j by omega,Nat.dist_eq_sub_of_le_right h.le]
    · subst j; simp
    · simp [show l≠j by omega,h,show ¬j<l by omega,Nat.dist_eq_sub_of_le h.le]
  rw [he]
  linarith

/-- The shifted coefficient mass is bounded by twice its square moment.
This is the finite Cauchy step in Tolev 1999 page 85 before display 60. -/
theorem shifted_square_bound (S : Finset ℕ) (U : ℕ) (hS : ∀ j ∈ S, j ≤ U)
    (a F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r) :
    ∑ l ∈ S, ∑ j ∈ S, (if l ≠ j then a l*a j*F (Nat.dist l j) else 0) ≤
      2*(∑ l ∈ S, a l^2)*(∑ r ∈ Icc 1 U, F r) := by
  classical
  let B := ∑ r ∈ Icc 1 U, F r
  have hsquare : ∀ l j : ℕ,
      2*(if l≠j then a l*a j*F (Nat.dist l j) else 0) ≤
        a l^2*(if l≠j then F (Nat.dist l j) else 0) +
        a j^2*(if l≠j then F (Nat.dist l j) else 0) := by
    intro l j
    split_ifs with h
    · nlinarith [mul_nonneg (sq_nonneg (a l-a j)) (hF (Nat.dist l j))]
    · simp
  have hs := sum_le_sum (s:=S) (fun l hl => sum_le_sum (s:=S) (fun j hj => hsquare l j))
  have hsym : (∑ l ∈ S, ∑ j ∈ S, a j^2*(if l≠j then F (Nat.dist l j) else 0)) =
      ∑ l ∈ S, ∑ j ∈ S, a l^2*(if l≠j then F (Nat.dist l j) else 0) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro j hj
    simp [ne_comm,Nat.dist_comm]
  simp only [sum_add_distrib,← mul_sum] at hs
  rw [hsym] at hs
  simp only [← mul_sum] at hs
  have hb : (∑ l ∈ S, a l^2*∑ j ∈ S, if l≠j then F (Nat.dist l j) else 0) ≤
      (∑ l ∈ S, a l^2)*(2*B) := by
    rw [sum_mul]
    apply sum_le_sum
    intro l hl
    exact mul_le_mul_of_nonneg_left (distance_sum_le S U l (hS l hl) hS F hF) (sq_nonneg _)
  dsimp [B] at hb
  nlinarith

end LeanLab.Tolev2009.Shifted341
