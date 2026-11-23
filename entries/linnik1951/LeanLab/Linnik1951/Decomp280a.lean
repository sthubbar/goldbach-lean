module

public import LeanLab.Linnik1951.SecondMoment111

/-!
P0093 page 162 equation 7.4. Decomposition of coefficient identification.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 162 equation 7.4, absolute convergence of the grouped
series. The geometric damping dominates the finite prime and power fibers. -/
theorem grouped_summable280 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun u : ℕ =>
      ((primePowerCount111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ)) := by
  exact grouped_summable_proved357_up111 N hN

/-- LEAF. P0093 page 162 equation 7.4, grouping the product by p plus 2 to x.
Absolute convergence of both factors is proved in SecondMoment111. -/
theorem product_grouped280 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111 N α * powerFourier111 N α =
      ∑' u : ℕ, (((primePowerCount111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) := by
  exact product_grouped_proved357_up111 N hN α

/-- LEAF. P0093 page 162 equation 7.4, termwise integration and the phase
integral. This is independent of primes and of the representation count. -/
theorem negative_series_coefficient280 (a : ℕ → ℂ) (ha : Summable a) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => ∑' u : ℕ, a u *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      if i ≤ 0 then a i.natAbs else 0 := by
  exact negative_series_coefficient_proved357_up111 a ha i

/-- P0093 page 162 equation 7.4. The exact statement of fourier_coefficient111
follows from the three smaller leaves. CONDITIONAL on those leaves. -/
theorem fourier_coefficient_decomposed280 (N : ℕ) (hN : 1 ≤ N) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => primeFourier111 N α * powerFourier111 N α) i =
        if i ≤ 0 then
          ((primePowerCount111 i.natAbs : ℝ) * Real.exp (-(i.natAbs : ℝ) / N) : ℂ)
        else 0 := by
  simp_rw [product_grouped280 N hN]
  exact negative_series_coefficient280 _ (grouped_summable280 N hN) i

end LeanLab.Linnik1951
