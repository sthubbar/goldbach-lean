module

public import LeanLab.Tolev2009.Decomp310b

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 83 to 84 display 55.
The finite correlation reduction retains all product cutoffs.
-/

@[expose] public section

open Finset Real ComplexConjugate

namespace LeanLab.Tolev2009.Decomp341a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp310b

/-- The second variable and modulus indices in Tolev 1999 page 83 display 55. -/
noncomputable def indices (l₃ K : ℕ) (H H₁ : ℝ) : Finset (ℕ × ℕ) :=
  Ioc ⌊H⌋₊ ⌊H₁⌋₊ ×ˢ (Icc 1 K).filter (fun k => Nat.Coprime k l₃)

/-- One progression indicator and phase in Tolev 1999 page 83 display 55.
The frequency is alpha rather than the source two alpha. -/
noncomputable def atom (l₃ N : ℕ) (α x : ℝ) (m : ℕ) (i : ℕ × ℕ) : ℂ :=
  if (x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
      (m * i.1) % i.2 = l₃ % i.2 then ee (α * (m * i.1 : ℕ)) else 0

/-- The exact finite progression correlation V on pages 83 to 84.
It is represented as a product of two atoms to expose the Gram identity. -/
noncomputable def correlation (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, atom l₃ N α x m i * conj (atom l₃ N α x m j)

/-- The diagonal scalar sum in Tolev 1999 page 84 display 56.
The bounded modulus coefficients have been removed. -/
noncomputable def diagonal (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) : ℝ :=
  ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
    if i.1 = j.1 then
      (tau5 i.1 : ℝ) * tau5 j.1 * ‖correlation l₃ N α x M M₁ i j‖ else 0

/-- The off diagonal scalar sum in Tolev 1999 pages 84 to 85 displays 56 and 59.
It has no arbitrary coefficient function. -/
noncomputable def offDiagonal (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) : ℝ :=
  ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
    if i.1 ≠ j.1 then
      (tau5 i.1 : ℝ) * tau5 j.1 * ‖correlation l₃ N α x M M₁ i j‖ else 0

/-- Expanding the divisor weight gives the coefficient and atom row on page 83. -/
theorem row_eq_atoms (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ)
    (b : ℕ → ℂ) (m : ℕ) :
    row lam l₃ K N α x H H₁ b m =
      ∑ i ∈ indices l₃ K H H₁, (b i.1 * (lam i.2 : ℂ)) * atom l₃ N α x m i := by
  classical
  simp only [indices, sum_product, row, L2Bound.weight, sum_filter,
    Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, mul_sum]
  apply sum_congr rfl
  intro l hl
  by_cases hc : x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N
  · simp only [hc, ite_true, atom, true_and]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> simp_all; ring
  · simp only [hc, ite_false, atom, false_and, mul_zero, ite_self, sum_const_zero]

/-- The exact Gram expansion before Tolev 1999 display 55. -/
theorem energy_eq_gram (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) :
    (energy lam l₃ K N α x M M₁ H H₁ b : ℂ) =
      ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
        (b i.1 * (lam i.2 : ℂ)) * conj (b j.1 * (lam j.2 : ℂ)) *
          correlation l₃ N α x M M₁ i j := by
  have hpoint (m : ℕ) :
      ((‖row lam l₃ K N α x H H₁ b m‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
          (b i.1 * (lam i.2 : ℂ)) * conj (b j.1 * (lam j.2 : ℂ)) *
            (atom l₃ N α x m i * conj (atom l₃ N α x m j)) := by
    rw [row_eq_atoms, sq_norm_eq_mul_conj, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [map_mul]
    ring
  simp only [energy, Complex.ofReal_sum, hpoint, correlation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]

/-- The scalar diagonal and off diagonal sum partition is exact. -/
theorem diagonal_add_offDiagonal (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) :
    diagonal l₃ K N α x M M₁ H H₁ + offDiagonal l₃ K N α x M M₁ H H₁ =
      ∑ i ∈ indices l₃ K H H₁, ∑ j ∈ indices l₃ K H H₁,
        (tau5 i.1 : ℝ) * tau5 j.1 * ‖correlation l₃ N α x M M₁ i j‖ := by
  classical
  simp only [diagonal, offDiagonal, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases h : i.1 = j.1 <;> simp [h]

/-- The coefficient free energy majorant in Tolev 1999 page 83 display 55.
The source tau modulus factors are not needed since the sealed lambda is bounded by one. -/
theorem energy_le_correlations (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) (hlam : ∀ k, |lam k| ≤ 1) (hL : 0 ≤ Real.log N)
    (hb : ∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) :
    energy lam l₃ K N α x M M₁ H H₁ b ≤
      Real.log N ^ (2 : ℕ) *
        (diagonal l₃ K N α x M M₁ H H₁ + offDiagonal l₃ K N α x M M₁ H H₁) := by
  have hc (i : ℕ × ℕ) : ‖b i.1 * (lam i.2 : ℂ)‖ ≤ (tau5 i.1 : ℝ) * Real.log N := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hlam i.2) (norm_nonneg _)).trans (by simpa using hb i.1)
  have he := congrArg norm (energy_eq_gram lam l₃ K N α x M M₁ H H₁ b)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg ..)] at he
  rw [he, diagonal_add_offDiagonal, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc
    _ ≤ (((tau5 i.1 : ℝ) * Real.log N) * ((tau5 j.1 : ℝ) * Real.log N)) *
        ‖correlation l₃ N α x M M₁ i j‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (hc i) (hc j) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
    _ = _ := by ring

/-- The Gram kernel is the progression V of Tolev 1999 page 83 display 55.
The signed difference phase remains inside the finite sum. -/
theorem correlation_eq_phase (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ) :
    correlation l₃ N α x M M₁ i j =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        if ((x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
            (m * i.1) % i.2 = l₃ % i.2) ∧
           ((x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
            (m * j.1) % j.2 = l₃ % j.2) then
          ee (α * m * ((i.1 : ℝ) - j.1)) else 0 := by
  classical
  unfold correlation
  apply sum_congr rfl
  intro m hm
  by_cases hi : (x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
      (m * i.1) % i.2 = l₃ % i.2
  · by_cases hj : (x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
        (m * j.1) % j.2 = l₃ % j.2
    · simp only [atom, hi, hj, and_self, ite_true, conj_ee]
      rw [← ee_add]
      congr 1
      push_cast
      ring
    · simp only [atom, hi, hj, true_and, ite_true, ite_false, map_zero, mul_zero]
  · simp only [atom, hi, false_and, ite_false, zero_mul]

/-- For equal second variables the phase vanishes and V is a cardinality.
This is the diagonal case before Tolev 1999 display 56. -/
theorem correlation_diagonal (l₃ N : ℕ) (α x M M₁ : ℝ) (l k₁ k₂ : ℕ) :
    correlation l₃ N α x M M₁ (l, k₁) (l, k₂) =
      (((Ioc ⌊M⌋₊ ⌊M₁⌋₊).filter (fun m =>
        (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
          (m * l) % k₁ = l₃ % k₁ ∧ (m * l) % k₂ = l₃ % k₂)).card : ℂ) := by
  rw [correlation_eq_phase]
  simp only [sub_self, mul_zero, ee_zero, ← sum_filter,
    sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext m
  simp only [mem_filter]
  tauto

/-- The diagonal scalar sum is independent of alpha, as used in display 56. -/
theorem diagonal_independent (l₃ K N : ℕ) (α β x M M₁ H H₁ : ℝ) :
    diagonal l₃ K N α x M M₁ H H₁ = diagonal l₃ K N β x M M₁ H H₁ := by
  classical
  unfold diagonal
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases h : i.1 = j.1
  · simp only [h, ite_true]
    obtain ⟨l, k₁⟩ := i
    obtain ⟨l', k₂⟩ := j
    dsimp at h
    subst l'
    rw [correlation_diagonal, correlation_diagonal]
  · simp only [h, ite_false]

/-- Both scalar pieces in the source correlation split are nonnegative. -/
theorem scalar_nonneg (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ) :
    0 ≤ diagonal l₃ K N α x M M₁ H H₁ ∧
      0 ≤ offDiagonal l₃ K N α x M M₁ H H₁ := by
  simp only [diagonal, offDiagonal]
  constructor <;>
    apply sum_nonneg <;> intro i hi <;> apply sum_nonneg <;> intro j hj <;>
    split_ifs <;> positivity

end LeanLab.Tolev2009.Decomp341a
