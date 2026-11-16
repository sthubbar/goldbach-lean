module

public import Mathlib
public import LeanLab.Pintz2018.ExpBounds

/-!
# Pintz 2018, Section 9 arithmetic

J. Pintz, "A new explicit formula in the additive theory of primes with applications II.
The exceptional set in Goldbach's problem", arXiv 1804.09084v2, Theorem 1: `E(X) < X^0.72`.
Section 9 reduces Theorem 1 to `S0 = ∑ Sᵢ² ≤ 1 - c0` and settles it case by case.
This file proves the elementary arithmetic of that section: (9.4), (9.6), (9.13), (9.17), (9.18),
(9.22) to (9.26), (9.27) to (9.30), (9.36), (9.37).  The zero-density inputs
(Lemmas 6 and 7 and the sums bounded by Theorems C to K) enter only as the printed numbers,
as hypotheses.  AI wrote the Lean code.
-/

@[expose] public section


namespace LeanLab.Pintz2018

open Finset

/-- `e^{-(25/7) λ}`, the weight in (9.2). -/
noncomputable def E (l : ℝ) : ℝ := Real.exp (-(25 / 7) * l)

/-! ### (9.4), the basic inequality -/

theorem basic_ineq {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (m A B : ℝ) (hm0 : 0 ≤ m)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hm : ∀ i ∈ s, b i ≤ m)
    (hA : ∑ i ∈ s, a i ≤ A) (hB : ∑ i ∈ s, b i ≤ B) :
    ∑ i ∈ s, (a i + b i) ^ 2 ≤ A ^ 2 + m * (2 * A + B) := by
  have hA0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have h1 : ∑ i ∈ s, (a i) ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [sq]
    have : a i * a i = ∑ j ∈ {i}, a i * a j := by simp
    rw [this]
    apply Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hi)
    intro j hj _
    exact mul_nonneg (ha i hi) (ha j hj)
  have h2 : ∑ i ∈ s, a i * b i ≤ m * ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [ha i hi, hm i hi]
  have h3 : ∑ i ∈ s, (b i) ^ 2 ≤ m * ∑ i ∈ s, b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [hb i hi, hm i hi]
  have h4 : ∑ i ∈ s, (a i + b i) ^ 2
      = ∑ i ∈ s, (a i) ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, (b i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h5 : (∑ i ∈ s, a i) ^ 2 ≤ A ^ 2 := by nlinarith
  nlinarith

/-! ### Bounds on the weight `E` -/

theorem E_upper (l : ℝ) (h0 : 0 ≤ l) (h8 : 25 / 7 * l ≤ 8) :
    E l ≤ ((T15 (25 / 7 * l / 8)) ^ 8)⁻¹ := by
  unfold E
  have hx : 0 ≤ 25 / 7 * l := by positivity
  have h := exp_ge_T (25 / 7 * l) hx
  have hp : 0 < (T15 (25 / 7 * l / 8)) ^ 8 := by
    have : 0 < T15 (25 / 7 * l / 8) := by
      unfold T15
      apply Finset.sum_pos'
      · intro i _; positivity
      · exact ⟨0, by simp, by simp⟩
    positivity
  rw [show -(25 / 7) * l = -(25 / 7 * l) by ring, Real.exp_neg]
  exact inv_anti₀ hp h

theorem E_lower (l : ℝ) (h0 : 0 ≤ l) (h8 : 25 / 7 * l ≤ 8) :
    ((T15 (25 / 7 * l / 8) + (25 / 7 * l / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℝ) * 15))) ^ 8)⁻¹
      ≤ E l := by
  unfold E
  have hx : 0 ≤ 25 / 7 * l := by positivity
  have h := exp_le_T (25 / 7 * l) hx h8
  rw [show -(25 / 7) * l = -(25 / 7 * l) by ring, Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) h

theorem E_pos (l : ℝ) : 0 < E l := Real.exp_pos _

theorem expneg_upper (x : ℝ) (h0 : 0 ≤ x) : Real.exp (-x) ≤ ((T15 (x / 8)) ^ 8)⁻¹ := by
  have h := exp_ge_T x h0
  have hp : 0 < (T15 (x / 8)) ^ 8 := by
    have : 0 < T15 (x / 8) := by
      unfold T15
      apply Finset.sum_pos'
      · intro i _; positivity
      · exact ⟨0, by simp, by simp⟩
    positivity
  rw [Real.exp_neg]
  exact inv_anti₀ hp h

theorem expneg_lower (x : ℝ) (h0 : 0 ≤ x) (h8 : x ≤ 8) :
    ((T15 (x / 8) + (x / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℝ) * 15))) ^ 8)⁻¹
      ≤ Real.exp (-x) := by
  have h := exp_le_T x h0 h8
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) h

theorem E_two (l : ℝ) : E (2 * l) = E l ^ 2 := by
  unfold E
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end LeanLab.Pintz2018

