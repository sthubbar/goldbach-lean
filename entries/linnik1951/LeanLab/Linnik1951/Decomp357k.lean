module

public import LeanLab.Linnik1951.Decomp280b
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
P0093 page 158 final sentence. Reflection of character prime sums.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open scoped ComplexConjugate

/-- P0093 page 158 final sentence and page 159 character sum definition.
Reflection of the phase conjugates the character weighted prime series. -/
theorem character_prime_reflect357 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) :
    characterPrime280 (star χ) N α = conj (characterPrime280 χ N (-α)) := by
  unfold characterPrime280
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro p
  simp only [MulChar.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 1
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- P0093 page 158 final sentence. The reflected square norm equals the
square norm for the conjugate character on the positive side. -/
theorem character_norm_reflect357 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) :
    ‖characterPrime280 χ N (-α)‖ = ‖characterPrime280 (star χ) N α‖ := by
  rw [character_prime_reflect357, Complex.norm_conj]

end LeanLab.Linnik1951
