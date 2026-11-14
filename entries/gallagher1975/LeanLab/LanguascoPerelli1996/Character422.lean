module

public import LeanLab.LanguascoPerelli1996.Window422
public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
P0071 page 355, character expansion before display 14.
Reuse the Mathlib character orthogonality relation and the existing
PNTPort conjugation lemmas. No explicit formula is assumed here.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Character422
open Complex Real Finset

/-- Page 355 before display 14, the finite Gauss reconstruction on units.
This is the algebraic character expansion before the analytic explicit formula. -/
theorem gauss_reconstruction {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    {b : ZMod q} (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ b * gaussSum χ⁻¹ ψ) =
      (q.totient : ℂ) * ψ b := by
  classical
  have horth (x : ZMod q) :
      (∑ χ : DirichletCharacter ℂ q, χ b * χ⁻¹ x) =
        if x = b then (q.totient : ℂ) else 0 := by
    by_cases hx : IsUnit x
    · have hi (χ : DirichletCharacter ℂ q) : χ⁻¹ x = χ x⁻¹ :=
        (LeanLab.PNTPort.LargeSieve.conj_char_eq_inv χ x).symm.trans
          (LeanLab.PNTPort.LargeSieve.conj_char_of_isUnit χ hx)
      simp_rw [hi]
      calc
        _ = ∑ χ : DirichletCharacter ℂ q, χ x⁻¹ * χ b := by
          apply Finset.sum_congr rfl
          intro χ hχ
          ring
        _ = _ := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx b
    · have hxb : x ≠ b := by rintro rfl; exact hx hb
      have hz (χ : DirichletCharacter ℂ q) : χ⁻¹ x = 0 := MulChar.map_nonunit _ hx
      simp only [hz, mul_zero, Finset.sum_const_zero, if_neg hxb]
  unfold gaussSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : ZMod q, (∑ χ : DirichletCharacter ℂ q, χ b * χ⁻¹ x) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = ∑ x : ZMod q, (if x = b then (q.totient : ℂ) else 0) * ψ x := by
      simp_rw [horth]
    _ = _ := by simp

/-- Page 355 before display 14, agreement of the additive phases in the
paper and Mathlib Gauss sums. The equality holds without a coprimality premise. -/
theorem additive_phase {q : ℕ} [NeZero q] (n a : ℕ) :
    ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q)) =
      e ((n : ℝ) * ((a : ℝ) / q)) := by
  have hh := ZMod.stdAddChar_coe (N := q) ((n : ℤ) * (a : ℤ))
  simp only [Int.cast_mul, Int.cast_natCast] at hh
  rw [hh]
  unfold e
  congr 1
  push_cast
  ring

/-- Page 355 before display 14, exact additive to multiplicative
character expansion at coefficients coprime to q. The excluded coefficients
remain a separate arithmetic error term in the paper. -/
theorem additive_character_expansion {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) (hn : Nat.Coprime n q) :
    (q.totient : ℂ) * e ((n : ℝ) * ((a : ℝ) / q)) =
      ∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q) * tau χ⁻¹ * χ (n : ZMod q) := by
  have hna : IsUnit ((n : ZMod q) * (a : ZMod q)) :=
    ((ZMod.isUnit_iff_coprime n q).2 hn).mul ((ZMod.isUnit_iff_coprime a q).2 ha)
  have hh := gauss_reconstruction ZMod.stdAddChar hna
  rw [additive_phase] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [map_mul]
  unfold tau
  ring

/-- Page 355 before display 14, exact finite character expansion.
The sum over coefficients not coprime to q is retained explicitly.
The weights are arbitrary, so stopped and Gallagher window sums are included. -/
theorem weighted_character_expansion {q : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (s : Finset ℕ) (f : ℕ → ℂ) :
    (q.totient : ℂ) * (∑ n ∈ s, f n * e ((n : ℝ) * ((a : ℝ) / q))) =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        (∑ n ∈ s, f n * χ (n : ZMod q))) +
      (q.totient : ℂ) *
        ∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q),
          f n * e ((n : ℝ) * ((a : ℝ) / q)) := by
  classical
  have hswap : (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
      (∑ n ∈ s, f n * χ (n : ZMod q))) =
      ∑ n ∈ s, f n * (∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q) * tau χ⁻¹ * χ (n : ZMod q)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  rw [hswap, Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcop : Nat.Coprime n q
  · rw [if_neg (not_not.mpr hcop), mul_zero, add_zero,
      ← Finset.mul_sum, ← additive_character_expansion a n ha hcop]
    ring
  · have hzero (χ : DirichletCharacter ℂ q) : χ (n : ZMod q) = 0 :=
      MulChar.map_nonunit χ (by simpa only [ZMod.isUnit_iff_coprime] using hcop)
    simp only [hzero, mul_zero, Finset.sum_const_zero, if_pos hcop, zero_add]

/-- Page 355 before display 14, specialized to the actual stopped remainder.
No bad prime power term or endpoint is suppressed. This identity supplies
the finite algebraic part of the remaining explicit formula route. -/
theorem stopped_character_expansion {q : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (X Y η : ℝ) :
    (q.totient : ℂ) * Decomp381a.partialR X Y η q a =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η))) -
      (q.totient : ℂ) * (muPhi q : ℂ) *
        (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η)) +
      (q.totient : ℂ) *
        ∑ n ∈ (Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊).filter (fun n => ¬ Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η) := by
  have hh := weighted_character_expansion a ha (Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * e ((n : ℝ) * η))
  have hterm (n : ℕ) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * e ((n : ℝ) * η) *
          e ((n : ℝ) * ((a : ℝ) / q)) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η) := by ring
  have hchar (n : ℕ) (χ : DirichletCharacter ℂ q) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * e ((n : ℝ) * η) * χ (n : ZMod q) =
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η) := by ring
  simp_rw [hterm, hchar] at hh
  unfold Decomp381a.partialR
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination hh

end LeanLab.LanguascoPerelli1996.Character422

