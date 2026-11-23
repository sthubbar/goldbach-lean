module

public import Mathlib

/-!
P0083, page 484, equation 17. An elementary denominator bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Totient

/-- Odd n satisfy n at most phi n squared; all n satisfy twice that bound. -/
theorem totient_sq_lower_aux (n : ℕ) :
    n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p n hp ih =>
    have hp2 := hp.two_le
    have hnodd (h : Odd (p * n)) : Odd n := by
      apply Nat.not_even_iff_odd.mp
      intro hnEven
      exact (Nat.not_even_iff_odd.mpr h) (hnEven.mul_left p)
    by_cases hd : p ∣ n
    · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
      have hpp : p ≤ p ^ 2 := by nlinarith
      constructor
      · calc p * n ≤ p * (2 * n.totient ^ 2) := Nat.mul_le_mul_left p ih.1
          _ ≤ p ^ 2 * (2 * n.totient ^ 2) := Nat.mul_le_mul_right _ hpp
          _ = 2 * (p * n.totient) ^ 2 := by ring
      · intro hodd
        calc p * n ≤ p * n.totient ^ 2 := Nat.mul_le_mul_left p (ih.2 (hnodd hodd))
          _ ≤ p ^ 2 * n.totient ^ 2 := Nat.mul_le_mul_right _ hpp
          _ = (p * n.totient) ^ 2 := by ring
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
      by_cases hpEq : p = 2
      · subst p
        have hno : Odd n := by
          apply Nat.not_even_iff_odd.mp
          intro he
          exact hd he.two_dvd
        constructor
        · simpa using Nat.mul_le_mul_left 2 (ih.2 hno)
        · intro hodd
          exact False.elim ((Nat.not_even_iff_odd.mpr hodd) (even_two_mul n))
      · have hp3 : 3 ≤ p := by omega
        have hpp : p ≤ (p - 1) ^ 2 := by
          have heq : p - 1 + 1 = p := by omega
          have hlow : 2 ≤ p - 1 := by omega
          nlinarith
        constructor
        · calc p * n ≤ p * (2 * n.totient ^ 2) := Nat.mul_le_mul_left p ih.1
            _ ≤ (p - 1) ^ 2 * (2 * n.totient ^ 2) := Nat.mul_le_mul_right _ hpp
            _ = 2 * ((p - 1) * n.totient) ^ 2 := by ring
        · intro hodd
          calc p * n ≤ p * n.totient ^ 2 := Nat.mul_le_mul_left p (ih.2 (hnodd hodd))
            _ ≤ (p - 1) ^ 2 * n.totient ^ 2 := Nat.mul_le_mul_right _ hpp
            _ = ((p - 1) * n.totient) ^ 2 := by ring

/-- The totient denominator bound used for large moduli in equation 17. -/
theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 :=
  (totient_sq_lower_aux n).1

end LeanLab.Perelli1996.Totient
