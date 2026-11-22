module

public import Mathlib

/-!
The Vaughan identity, as used on page 5 of Akeno 2026 in the proof of Theorem 2.1.
This file proves the algebraic identity using Mathlib convolution identities.
The dyadic coefficient bounds and analytic transfer remain separate obligations.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Akeno2026.Vaughan86
open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The part of an arithmetic function at arguments at most U. -/
noncomputable def shortPart (f : ArithmeticFunction ℝ) (U : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ U then f n else 0, by simp⟩

/-- Page 5 Vaughan identity. The exact four term convolution decomposition. -/
theorem vaughan_identity (U V : ℝ) :
    vonMangoldt =
      shortPart (moebius : ArithmeticFunction ℝ) U * log -
        shortPart (moebius : ArithmeticFunction ℝ) U * shortPart vonMangoldt V *
          (zeta : ArithmeticFunction ℝ) + shortPart vonMangoldt V +
        ((moebius : ArithmeticFunction ℝ) - shortPart (moebius : ArithmeticFunction ℝ) U) *
          (vonMangoldt - shortPart vonMangoldt V) * (zeta : ArithmeticFunction ℝ) := by
  rw [← vonMangoldt_mul_zeta]
  have hmu : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
    coe_moebius_mul_coe_zeta
  linear_combination - (vonMangoldt - shortPart vonMangoldt V) * hmu

/-- Page 5 Vaughan identity inside any finite complex weighted sum. -/
theorem vaughan_weighted_identity (U V : ℝ) (s : Finset ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ s, (vonMangoldt n : ℂ) * F n) =
      (∑ n ∈ s, ((shortPart (moebius : ArithmeticFunction ℝ) U * log) n : ℂ) * F n) -
      (∑ n ∈ s, ((shortPart (moebius : ArithmeticFunction ℝ) U * shortPart vonMangoldt V *
        (zeta : ArithmeticFunction ℝ)) n : ℂ) * F n) +
      (∑ n ∈ s, (shortPart vonMangoldt V n : ℂ) * F n) +
      (∑ n ∈ s, ((((moebius : ArithmeticFunction ℝ) -
          shortPart (moebius : ArithmeticFunction ℝ) U) *
          (vonMangoldt - shortPart vonMangoldt V) * (zeta : ArithmeticFunction ℝ)) n : ℂ) * F n) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => ∑ n ∈ s, (f n : ℂ) * F n)
    (vaughan_identity U V)
  simpa only [ArithmeticFunction.add_apply, sub_eq_add_neg, ArithmeticFunction.neg_apply, Complex.ofReal_add, Complex.ofReal_sub,
    add_mul, sub_mul, Complex.ofReal_neg, neg_mul, sum_neg_distrib, sum_add_distrib, sum_sub_distrib] using h

end LeanLab.Akeno2026.Vaughan86
