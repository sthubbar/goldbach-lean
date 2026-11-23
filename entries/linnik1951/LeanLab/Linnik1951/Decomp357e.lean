module

public import LeanLab.Linnik1951.Decomp357d

/-!
P0093 page 162 equation 7.4. Absolute convergence of the grouped coefficients.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 162 definition of Psi before equation 7.4. Its finite fiber
is contained in the full square of the bounded prime and exponent indices. -/
theorem prime_power_count_le_square357 (u : ℕ) : primePowerCount111 u ≤ (u + 1) ^ 2 := by
  classical
  unfold primePowerCount111
  calc
    _ ≤ (Finset.univ : Finset (Fin (u + 1) × Fin (u + 1))).card := Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

/-- P0093 page 154 damping and page 162 equation 7.4. A quadratic number
of possible pairs is summable after geometric damping. -/
theorem square_damping_summable357 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun u : ℕ => ((u : ℝ) + 1) ^ 2 * Real.exp (-(u : ℝ) / N)) := by
  let r := Real.exp (-1 / (N : ℝ))
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact div_neg_of_neg_of_pos (by norm_num) hpos
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  have hs := (h2.add (h1.mul_left 2)).add h0
  apply hs.congr
  intro u
  have hexp : r ^ u = Real.exp (-(u : ℝ) / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  simp only [pow_one]
  ring

/-- P0093 page 162 equation 7.4. Exact grouped_summable280 statement.
The crude finite square bound suffices. Romanov is not needed for convergence. -/
theorem grouped_summable_proved357 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun u : ℕ =>
      ((primePowerCount111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ)) := by
  apply Summable.of_norm_bounded (square_damping_summable357 N hN)
  intro u
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (primePowerCount111 u)), abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast prime_power_count_le_square357 u

end LeanLab.Linnik1951
