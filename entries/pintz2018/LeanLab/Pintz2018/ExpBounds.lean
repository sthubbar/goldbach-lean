module

public import Mathlib

/-!
# Pintz 2018, elementary bounds on `Real.exp`

Helper lemmas for the Section 9 arithmetic of arXiv 1804.09084v2.
`exp x = (exp (x/8))^8` and a Taylor bound of order 15 on `[0, 1]`.
AI wrote the Lean code.
-/

@[expose] public section


namespace LeanLab.Pintz2018

open Finset

/-- Taylor partial sum of order 15 of `exp y`. -/
noncomputable def T15 (y : ℝ) : ℝ := ∑ i ∈ range 15, y ^ i / (i.factorial : ℝ)

theorem exp_ge_T (x : ℝ) (h0 : 0 ≤ x) : (T15 (x / 8)) ^ 8 ≤ Real.exp x := by
  have h : T15 (x / 8) ≤ Real.exp (x / 8) := Real.sum_le_exp_of_nonneg (by positivity) 15
  have hT : 0 ≤ T15 (x / 8) := by
    unfold T15
    apply Finset.sum_nonneg
    intro i _
    positivity
  calc (T15 (x / 8)) ^ 8 ≤ (Real.exp (x / 8)) ^ 8 := pow_le_pow_left₀ hT h 8
    _ = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem exp_le_T (x : ℝ) (h0 : 0 ≤ x) (h8 : x ≤ 8) :
    Real.exp x ≤ (T15 (x / 8) + (x / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℝ) * 15))) ^ 8 := by
  have hy0 : 0 ≤ x / 8 := by positivity
  have hy1 : x / 8 ≤ 1 := by linarith
  have h := Real.exp_bound (x := x / 8) (by rw [abs_of_nonneg hy0]; exact hy1) (n := 15) (by norm_num)
  have h2 : Real.exp (x / 8) ≤ T15 (x / 8) + (x / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℝ) * 15)) := by
    have := (abs_le.mp h).2
    unfold T15
    rw [abs_of_nonneg hy0] at this
    push_cast at this ⊢
    linarith
  calc Real.exp x = (Real.exp (x / 8)) ^ 8 := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h2 8

end LeanLab.Pintz2018

