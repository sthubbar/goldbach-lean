module

public import LeanLab.Linnik1951.Decomp552a

/-!
P0093 pages 154, 155 and 161. Exact prime square window expansion.
No quantitative prime estimate is asserted. Every window keeps its sinc kernel.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open MeasureTheory Finset

/-- P0093 page 154 definition of S. Its natural coefficient is zero
at nonprimes and is the exponential damping at primes. -/
noncomputable def primeCoefficient552 (N k : ℕ) : ℂ :=
  if k.Prime then (Real.exp (-(k : ℝ) / N) : ℂ) else 0

/-- P0093 page 155 equation 3.1 and page 161 equation 6.3.
Auxiliary exact count of ordered prime pairs with prescribed sum. -/
def primePairCount552 (k : ℕ) : ℕ :=
  ((range (k + 1)).filter (fun m => m.Prime ∧ (k - m).Prime)).card

/-- P0093 page 154 damping. The natural prime coefficients are
absolutely summable at every positive scale. -/
theorem prime_coefficients_summable552 (N : ℕ) (hN : 1 ≤ N) :
    Summable (primeCoefficient552 N) := by
  apply Summable.of_norm_bounded (damping_summable111 N hN)
  intro k
  by_cases hk : k.Prime
  · simp only [primeCoefficient552, if_pos hk, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]
  · simp [primeCoefficient552, hk, (Real.exp_pos _).le]

/-- P0093 page 154 definition of S. Zero extension from the prime
subtype gives the natural negative Fourier series. -/
theorem prime_series_nat552 (N : ℕ) (z : ℝ) :
    primeFourier111 N z = ∑' k : ℕ, primeCoefficient552 N k *
      Complex.exp ((-(2 * Real.pi * z * k) : ℝ) * Complex.I) := by
  classical
  let f : ℕ → ℂ := fun k => primeCoefficient552 N k *
    Complex.exp ((-(2 * Real.pi * z * k) : ℝ) * Complex.I)
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro k hk
    by_cases hp : k.Prime
    · exact ⟨⟨k, hp⟩, rfl⟩
    · exact absurd (by simp [f, primeCoefficient552, hp] : f k = 0) hk
  calc
    _ = ∑' p : Nat.Primes, f (p : ℕ) := by
      unfold primeFourier111
      apply tsum_congr
      intro p
      simp [f, primeCoefficient552, p.property]
    _ = ∑' k : ℕ, f k := Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = _ := rfl

/-- P0093 page 155 equation 3.1 and page 161 coefficient extraction.
The convolution coefficient is the ordered prime pair count times its
common damping. This identity supplies no bound on that count. -/
theorem prime_coefficient_convolution552 (N k : ℕ) :
    (∑ m ∈ range (k + 1), primeCoefficient552 N m * primeCoefficient552 N (k - m)) =
      (primePairCount552 k : ℂ) * (Real.exp (-(k : ℝ) / N) : ℂ) := by
  classical
  have hterm (m : ℕ) (hm : m ∈ range (k + 1)) :
      primeCoefficient552 N m * primeCoefficient552 N (k - m) =
        if m.Prime ∧ (k - m).Prime then (Real.exp (-(k : ℝ) / N) : ℂ) else 0 := by
    have hmk : m ≤ k := by have := mem_range.mp hm; omega
    by_cases hp : m.Prime <;> by_cases hp' : (k - m).Prime
    · simp only [primeCoefficient552, if_pos hp, if_pos hp', if_pos (And.intro hp hp')]
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      push_cast [Nat.cast_sub hmk]
      ring
    · simp [primeCoefficient552, hp, hp']
    · simp [primeCoefficient552, hp, hp']
    · simp [primeCoefficient552, hp, hp']
  rw [sum_congr rfl hterm, ← sum_filter]
  simp [primePairCount552]

/-- P0093 page 161 after equation 6.3. No ordered prime pair has
sum below four. This is exact vanishing of the full period coefficient. -/
theorem prime_pair_count_small552 (k : ℕ) (hk : k ≤ 3) :
    primePairCount552 k = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro m hm
  rcases mem_filter.mp hm with ⟨hm, hp, hp'⟩
  have := hp.two_le
  have := hp'.two_le
  have := mem_range.mp hm
  omega

/-- P0093 page 155 equation 3.1. The first nonzero prime pair
coefficient is the single ordered pair two and two. -/
theorem prime_pair_count_four552 : primePairCount552 4 = 1 := by decide

/-- P0093 pages 155 and 161 equations 3.1 and 6.3. Exact auxiliary
prime square formula for any nonnegative radius and any rational or real
centre. No off diagonal frequency is discarded. -/
theorem prime_square_window552 (N : ℕ) (hN : 1 ≤ N)
    (r : ℝ) (hr : 0 ≤ r) (c : ℝ) (n : ℤ) :
    (∫ z in -r..r, primeFourier111 N (c + z) ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * (c + z) : ℝ) : ℂ) * Complex.I)) =
    ∑' k : ℕ, ((primePairCount552 k : ℂ) * (Real.exp (-(k : ℝ) / N) : ℂ)) *
      Complex.exp (((2 * Real.pi * ((n : ℝ) - k) * c : ℝ) : ℂ) * Complex.I) *
      ((2 * r * Real.sinc (2 * Real.pi * ((n : ℝ) - k) * r) : ℝ) : ℂ) := by
  simp_rw [prime_series_nat552]
  rw [square_symmetric_integral552 _ (prime_coefficients_summable552 N hN) r hr c n]
  simp_rw [prime_coefficient_convolution552]

/-- P0093 page 155 equation 3.1. Exact series for the local arc with
its original radius one over q tau. This is an identity, not an error bound. -/
theorem local_arc_kernel552 (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (n : ℤ) :
    localArc1622 N q n =
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ∑' k : ℕ,
      ((primePairCount552 k : ℂ) * (Real.exp (-(k : ℝ) / N) : ℂ)) *
      Complex.exp (((2 * Real.pi * ((n : ℝ) - k) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
      ((2 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        Real.sinc (2 * Real.pi * ((n : ℝ) - k) *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) : ℝ) : ℂ) := by
  unfold localArc1622
  apply sum_congr rfl
  intro a ha
  exact prime_square_window552 N hN _ (by positivity) _ n

end LeanLab.Linnik1951
