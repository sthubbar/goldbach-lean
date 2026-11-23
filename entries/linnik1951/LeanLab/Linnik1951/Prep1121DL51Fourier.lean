module

public import LeanLab.Linnik1951.Decomp520a

/-!
P0093 page 159 before display 5.3 with equation 5.1. Split of the open leaf
principal_fourier_coeff_sq_prep1121 of Prep1121MixedRepair520: the Fourier
coefficients of the principal series in the Parseval step of the trivial estimate.
The principal series is written as one series over natural frequencies, its
coefficients are read off with negative_series_coefficient_proved357_up111, and
the squared weights are compared with the damped prime sum.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 159 equation 5.1. The weight of the principal series at the
natural frequency u is summable. -/
theorem principal_weight_summable_prep1121D (N q : ℕ) (hN : 1 ≤ N) :
    Summable (fun u : ℕ =>
      (((if u.Prime ∧ u ∉ q.primeFactors then Real.exp (-(u : ℝ) / N) else 0 : ℝ)) : ℂ)) := by
  apply Summable.of_norm_bounded (damping_summable111_up111 N hN)
  intro u
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_pos (Real.exp_pos _)]
  · simp [(Real.exp_pos _).le]

/-- LEAF: P0093 page 159 equation 5.1. The principal series is the prime
series minus the prime divisor terms of q, which is one series over natural
frequencies u with weight exp of minus u over N at the primes u not dividing q
and weight zero elsewhere. -/
theorem principal_as_nat_series_prep1121D (N q : ℕ) (hN : 1 ≤ N) :
    principalPrime520 N q = fun z => ∑' u : ℕ,
      (((if u.Prime ∧ u ∉ q.primeFactors then Real.exp (-(u : ℝ) / N) else 0 : ℝ)) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * u) : ℝ) * Complex.I) := by
  funext z
  set h : ℕ → ℂ := fun u => (Real.exp (-(u : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * u) : ℝ) * Complex.I) with hh
  have hP : primeFourier111_up111 N z = ∑' u : ℕ, {p : ℕ | p.Prime}.indicator h u := by
    rw [← _root_.tsum_subtype]
    rfl
  have hPs : Summable ({p : ℕ | p.Prime}.indicator h) := by
    rw [← summable_subtype_iff_indicator]
    exact prime_fourier_summable111_up111 N hN z
  have hF : (∑ p ∈ q.primeFactors, h p) =
      ∑' u : ℕ, (q.primeFactors : Set ℕ).indicator h u := by
    rw [tsum_eq_sum (s := q.primeFactors)]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [Set.indicator_of_mem (by exact_mod_cast hu)]
    · intro u hu
      rw [Set.indicator_of_notMem (by exact_mod_cast hu)]
  have hFs : Summable ((q.primeFactors : Set ℕ).indicator h) := by
    apply summable_of_ne_finset_zero (s := q.primeFactors)
    intro u hu
    rw [Set.indicator_of_notMem (by exact_mod_cast hu)]
  unfold principalPrime520
  change primeFourier111_up111 N z - (∑ p ∈ q.primeFactors, h p) = _
  rw [hP, hF, ← hPs.tsum_sub hFs]
  apply tsum_congr
  intro u
  by_cases hp : u.Prime
  · by_cases hq : u ∈ q.primeFactors
    · have hq' : u ∈ (q.primeFactors : Set ℕ) := by exact_mod_cast hq
      simp [Set.indicator_of_mem hq', hp, hq, hh]
    · have hq' : u ∉ (q.primeFactors : Set ℕ) := by exact_mod_cast hq
      simp [Set.indicator_of_notMem hq', hp, hq, hh]
  · have hq : u ∉ q.primeFactors := fun hm => hp (Nat.prime_of_mem_primeFactors hm)
    have hq' : u ∉ (q.primeFactors : Set ℕ) := by exact_mod_cast hq
    have hp' : u ∉ {p : ℕ | p.Prime} := hp
    simp [Set.indicator_of_notMem hq', Set.indicator_of_notMem hp', hp]

/-- P0093 page 159 before display 5.3. The Fourier coefficient of the
principal series at minus u is the weight at u, and zero at positive frequencies. -/
theorem principal_coeff_prep1121D (N q : ℕ) (hN : 1 ≤ N) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (principalPrime520 N q) i =
      if i ≤ 0 then
        (((if i.natAbs.Prime ∧ i.natAbs ∉ q.primeFactors then
          Real.exp (-(i.natAbs : ℝ) / N) else 0 : ℝ)) : ℂ)
      else 0 := by
  rw [principal_as_nat_series_prep1121D N q hN]
  exact negative_series_coefficient_proved357_up111 _ (principal_weight_summable_prep1121D N q hN) i

/-- LEAF: P0093 page 159 before display 5.3. The squared weights of the
principal series sum to at most the damped prime sum with doubled decay, since
each squared weight is exp of minus 2 u over N at a prime u, or zero. -/
theorem principal_weight_sq_le_prep1121D (N q : ℕ) (hN : 1 ≤ N) :
    ∑' u : ℕ, ‖(((if u.Prime ∧ u ∉ q.primeFactors then
        Real.exp (-(u : ℝ) / N) else 0 : ℝ)) : ℂ)‖ ^ 2 ≤
      ∑' p : Nat.Primes, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set g : ℕ → ℝ := fun u => {p : ℕ | p.Prime}.indicator
    (fun u : ℕ => Real.exp (-(2 * (u : ℝ)) / N)) u with hg
  have hsq : ∀ u : ℕ, ‖(((if u.Prime ∧ u ∉ q.primeFactors then
      Real.exp (-(u : ℝ) / N) else 0 : ℝ)) : ℂ)‖ ^ 2 ≤ g u := by
    intro u
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    by_cases hp : u.Prime
    · have hp' : u ∈ {p : ℕ | p.Prime} := hp
      simp only [hg, Set.indicator_of_mem hp']
      split_ifs
      · rw [sq, ← Real.exp_add]
        apply le_of_eq
        congr 1
        ring
      · rw [sq, mul_zero]
        exact (Real.exp_pos _).le
    · have hp' : u ∉ {p : ℕ | p.Prime} := hp
      simp only [hg, Set.indicator_of_notMem hp']
      rw [ite_eq_right_iff.mpr (fun h => absurd h.1 hp)]
      simp
  have hg0 : ∀ u, 0 ≤ g u := fun u =>
    Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u
  have hgs : Summable g := by
    apply Summable.of_nonneg_of_le hg0 _ (damping_summable111_up111 N hN)
    intro u
    simp only [hg]
    by_cases hp : u ∈ {p : ℕ | p.Prime}
    · rw [Set.indicator_of_mem hp]
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hNp.le
      have : (0 : ℝ) ≤ u := Nat.cast_nonneg u
      linarith
    · rw [Set.indicator_of_notMem hp]
      exact (Real.exp_pos _).le
  have hLs := Summable.of_nonneg_of_le (fun u => sq_nonneg _) hsq hgs
  refine (Summable.tsum_le_tsum hsq hLs hgs).trans (le_of_eq ?_)
  rw [hg]
  show ∑' u : ℕ, {p : ℕ | p.Prime}.indicator (fun u : ℕ => Real.exp (-(2 * (u : ℝ)) / N)) u = _
  rw [← _root_.tsum_subtype]
  rfl

/-- P0093 page 159 before display 5.3. Exact statement of the parent leaf
principal_fourier_coeff_sq_prep1121. -/
theorem principal_fourier_coeff_sq_prep1121D (N q : ℕ) (hN : 1 ≤ N) :
    ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (principalPrime520 N q) i‖ ^ 2 ≤
      ∑' p : Nat.Primes, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) := by
  rw [negative_modes_sum111_up111 (fun u : ℕ =>
      (((if u.Prime ∧ u ∉ q.primeFactors then Real.exp (-(u : ℝ) / N) else 0 : ℝ)) : ℂ))
    _ (principal_coeff_prep1121D N q hN)]
  exact principal_weight_sq_le_prep1121D N q hN

end LeanLab.Linnik1951
