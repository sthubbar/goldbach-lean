module

public import LeanLab.Grimmelt2019.ComplexRamanujan
public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
AI wrote this Lean code for CODEX task51.
P0074 page 9, equations 25 and 26.
The finite Parseval calculation follows the lab's LargeSieve.Multiplicative proof.
Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- Additive Parseval for all shifts of a Gauss sum, without a primitivity assumption. -/
theorem gauss_shift_second_moment {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ‖gaussSum χ (ZMod.stdAddChar.mulShift a)‖ ^ 2 =
      (q : ℝ) * q.totient := by
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  change ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = _
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow]
  unfold gaussSum
  simp_rw [ofReal_normSq_sum, AddChar.mulShift_apply]
  have hc : ∀ z, (starRingEnd ℂ) (ψ z) = ψ (-z) := fun z => conj_stdAddChar z
  have hexp : ∀ a x y : ZMod q, χ x * ψ (a * x) * (starRingEnd ℂ) (χ y * ψ (a * y)) =
      χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) := by
    intro a x y
    rw [(starRingEnd ℂ).map_mul, hc, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl (fun x _ => Finset.sum_comm)).trans ?_
  have hsum : ∀ x y : ZMod q, ∑ a : ZMod q, χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) =
      if x = y then (q : ℂ) * (χ x * (starRingEnd ℂ) (χ x)) else 0 := by
    intro x y
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
    by_cases hxy : x = y
    · rw [ite_eq_left (sub_eq_zero.mpr hxy), ite_eq_left hxy, hxy]
      ring
    · rw [ite_eq_right (fun h => hxy (sub_eq_zero.mp h)), ite_eq_right hxy, Nat.cast_zero, mul_zero]
  simp_rw [hsum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
  rw [← Complex.ofReal_sum, sum_normSq_char]
  norm_cast

/-- Equation 25 holds for every character, including imprimitive characters. -/
theorem gauss_norm_le_sqrt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt q := by
  have hle : ∑ a : ZMod q, ‖χ⁻¹ a‖ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤
      ∑ a : ZMod q, ‖gaussSum χ (ZMod.stdAddChar.mulShift a)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hu : IsUnit a
    · have hg := gaussSum_mulShift_eq χ ZMod.stdAddChar hu.unit
      rw [hu.unit_spec] at hg
      rw [hg, norm_mul, mul_pow]
    · rw [MulChar.map_nonunit _ hu, norm_zero, zero_pow (by omega), zero_mul]
      exact sq_nonneg _
  rw [← Finset.sum_mul, sum_normSq_char, gauss_shift_second_moment] at hle
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hs : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤ (q : ℝ) := by
    nlinarith only [hle, hφ]
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hs

/-- The standard Gauss sum is exactly the reduced-residue sum printed on page 9. -/
theorem gaussSum_eq_reduced {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    gaussSum χ ZMod.stdAddChar =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        χ (a : ZMod q) * LeanLab.PNTPort.LargeSieve.e ((a : ℝ) / q) := by
  rw [gaussSum, sum_zmod_eq_sum_range, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have he : ZMod.stdAddChar (a : ZMod q) = LeanLab.PNTPort.LargeSieve.e ((a : ℝ) / q) := by
    simpa using stdAddChar_mul_natCast (q := q) 1 a
  by_cases hc : Nat.Coprime a q
  · rw [ite_eq_left hc, he]
  · rw [ite_eq_right hc, MulChar.map_nonunit χ (fun hu => hc ((ZMod.isUnit_iff_coprime a q).mp hu)),
      zero_mul]

/-- Equation 26 identifies the principal Gauss coefficient with the Möbius value. -/
theorem gaussSum_principal {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      (ArithmeticFunction.moebius q : ℂ) := by
  rw [gaussSum_eq_reduced]
  have heq : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      (1 : DirichletCharacter ℂ q) (a : ZMod q) *
        LeanLab.PNTPort.LargeSieve.e ((a : ℝ) / q)) =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        LeanLab.PNTPort.LargeSieve.e ((1 : ℝ) * a / q) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr (Finset.mem_filter.mp ha).2)]
    simp
  rw [heq]
  have h := ram_sum_eq q (1 : ℤ)
  rw [ram_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) (m := 1) (by simp)] at h
  simpa using h

end LeanLab.Grimmelt2019.MainTerm
