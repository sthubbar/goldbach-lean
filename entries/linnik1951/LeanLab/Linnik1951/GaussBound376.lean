module

public import LeanLab.Linnik1951.Gauss376
public import LeanLab.ExceptionalSet.Lu2010Gauss

/-!
P0093 page 156 after Lemma 1. The Gauss norm bound for every character.
The energy calculation adapts the proved calculation in PNTPort.LargeSieve.Multiplicative.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Complex Finset LeanLab.PNTPort.LargeSieve

/-- P0093 page 156 after Lemma 1. Finite additive orthogonality gives
the energy of all additive shifts of a character Gauss sum. Reuse the
proved Lu2010Gauss complete period identity through its Gauss sum bridge. -/
theorem gauss_shift_energy376 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ‖gaussSum χ (ZMod.stdAddChar.mulShift a)‖ ^ 2 =
      (q : ℝ) * (q.totient : ℝ) := by
  simp_rw [← LeanLab.ExceptionalSet.Lu2010Gauss.G_eq_gaussSum]
  exact LeanLab.ExceptionalSet.Lu2010Gauss.G_energy χ

/-- P0093 page 156 after Lemma 1. The unit additive shifts all have the
same Gauss norm. Their contribution is bounded by the full additive
shift energy, which gives the square norm bound without primitivity. -/
theorem gauss_norm_sq_le376 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤ (q : ℝ) := by
  have hpoint (a : ZMod q) : ‖χ⁻¹ a‖ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤
      ‖gaussSum χ (ZMod.stdAddChar.mulShift a)‖ ^ 2 := by
    by_cases ha : IsUnit a
    · rw [← ha.unit_spec, gaussSum_mulShift_eq, norm_mul, mul_pow]
    · rw [MulChar.map_nonunit _ ha, norm_zero, zero_pow (by omega), zero_mul]
      positivity
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (ZMod q))) => hpoint a)
  rw [← Finset.sum_mul, LeanLab.PNTPort.LargeSieve.sum_normSq_char,
    gauss_shift_energy376] at hs
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  nlinarith

/-- P0093 page 156 immediately after Lemma 1. Every Dirichlet character
modulo nonzero q has Gauss sum norm at most the square root of q. -/
theorem gauss_norm_le376 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt q := by
  have hs := gauss_norm_sq_le376 χ
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) q)
  have hnonneg := Real.sqrt_nonneg (q : ℝ)
  nlinarith [norm_nonneg (gaussSum χ ZMod.stdAddChar)]

end LeanLab.Linnik1951
