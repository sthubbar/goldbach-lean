module

public import LeanLab.Linnik1951.Decomp357k

/-!
P0093 pages 157 to 159. Near and far decomposition of the Mellin square bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 159 before equation 5.1. Character weighting preserves the
uniform geometric majorant of the damped prime series. -/
theorem continuous_character_prime357 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) : Continuous (characterPrime280 χ N) := by
  unfold characterPrime280
  apply continuous_tsum
    (u := fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N))
  · intro p
    fun_prop
  · exact (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective
  · intro p α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)



end LeanLab.Linnik1951
