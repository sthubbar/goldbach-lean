module

public import LeanLab.LanguascoPerelli1996.BadPrimes422

/-!
P0071 page 355 before display 14, individual inducing character comparison.
Use Mathlib's actual primitiveCharacter, not a free replacement function.
The Gauss weighted average still needs its own cancellation estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Primitive422
open Real Finset

/-- Derived pointwise input for the inducing character replacement on page 355.
The difference vanishes on units modulo q and has norm at most one elsewhere. -/
theorem primitive_difference_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (n : ℕ) :
    ‖χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
      if Nat.Coprime n q then (0 : ℝ) else 1 := by
  by_cases hn : Nat.Coprime n q
  · have hh : χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
      simpa only [Int.cast_natCast] using
        χ.primitiveCharacter_apply_of_isCoprime
          (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.mpr hn)
    simp only [hh, sub_self, norm_zero]
    split_ifs <;> norm_num
  · have hz : χ (n : ZMod q) = 0 := MulChar.map_nonunit χ
      (by simpa only [ZMod.isUnit_iff_coprime] using hn)
    simpa only [hz, zero_sub, norm_neg, if_neg hn] using
      χ.primitiveCharacter.norm_le_one (n : ZMod χ.conductor)

/-- Page 355 before display 14, derived individual primitive character error.
Finite sums of Lambda times the character difference have norm at most
log N times log q divided by log two, uniformly in the additive phase. -/
theorem primitive_sum_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) (N : ℕ) (η : ℝ) (hs : ∀ n ∈ s, n ≤ N) :
    ‖∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)) * e ((n : ℝ) * η)‖ ≤
      Real.log N * Real.log q / Real.log 2 := by
  have he (t : ℝ) : ‖e t‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  have hpoint (n : ℕ) :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)) * e ((n : ℝ) * η)‖ ≤
        ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 0 else 1) := by
    simp only [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left (primitive_difference_norm χ n)
      ArithmeticFunction.vonMangoldt_nonneg
  calc
    _ ≤ ∑ n ∈ s, ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)) * e ((n : ℝ) * η)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ s, ArithmeticFunction.vonMangoldt n *
        (if Nat.Coprime n q then 0 else 1) := Finset.sum_le_sum (fun n hn => hpoint n)
    _ = ∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hc : Nat.Coprime n q <;> simp [hc]
    _ ≤ (Nat.log 2 N : ℝ) * Real.log q :=
      BadPrimes422.bad_vonMangoldt_sum s N q (Nat.pos_of_ne_zero (NeZero.ne q)) hs
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (Real.natLog_le_logb N 2)
        (Real.log_natCast_nonneg q)
      simpa only [Real.logb, Nat.cast_ofNat, div_mul_eq_mul_div] using hh

/-- Page 355 before display 14, the actual original and inducing
primitive character polynomials differ by the preceding explicit error.
This is an individual character statement, before Gauss weighted averaging. -/
theorem primitive_polynomial_difference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) (N : ℕ) (η : ℝ) (hs : ∀ n ∈ s, n ≤ N) :
    ‖(∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η)) -
      (∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) *
        χ.primitiveCharacter (n : ZMod χ.conductor) * e ((n : ℝ) * η))‖ ≤
      Real.log N * Real.log q / Real.log 2 := by
  rw [← Finset.sum_sub_distrib]
  have hh : (∑ n ∈ s,
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η) -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          χ.primitiveCharacter (n : ZMod χ.conductor) * e ((n : ℝ) * η))) =
      ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)) * e ((n : ℝ) * η) := by
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hh]
  exact primitive_sum_error χ s N η hs

end LeanLab.LanguascoPerelli1996.Primitive422

