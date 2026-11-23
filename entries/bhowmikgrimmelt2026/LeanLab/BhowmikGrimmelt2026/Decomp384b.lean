module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.BhowmikGrimmelt2026.Decomp384a
public import Mathlib.NumberTheory.Chebyshev

/-!
Removal of the higher prime powers omitted on P0029 page 4.
The quantitative bounds below are derived estimates, not printed paper constants.
The sealed logarithm only bound in DecompJ1034 is unchanged.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- The ordered prime representation count with logarithmic weights.
Source: P0029 page 4, before display 2.1. -/
noncomputable def primeR2_384 (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    if k.Prime ∧ (N - k).Prime then Real.log k * Real.log (N - k : ℕ) else 0

/-- The weighted prime count is the convolution of the prime part of von Mangoldt.
Source: P0029 page 4, the change from prime counts to r2. -/
theorem primeR2_eq_convolution384 (N : ℕ) :
    primeR2_384 N = ∑ k ∈ Finset.range (N + 1),
      (if k.Prime then vonMangoldt k else 0) *
        (if (N - k).Prime then vonMangoldt (N - k) else 0) := by
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : k.Prime <;> by_cases hq : (N - k).Prime <;>
    simp [hp, hq, vonMangoldt_apply_prime]

/-- No Goldbach representation implies zero logarithmically weighted prime count.
Source: P0029 page 4 and the representation interpretation on page 9. -/
theorem primeR2_zero_of_not_goldbach384 (N : ℕ) (hN : ¬ IsGoldbachSum N) :
    primeR2_384 N = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  apply ite_eq_right
  rintro ⟨hp, hq⟩
  exact hN ⟨k, N - k, hp, hq, Nat.add_sub_of_le (by simpa using hk)⟩

/-- The total nonprime mass of von Mangoldt is exactly psi minus theta.
Source: derived helper for the omitted contribution on P0029 page 4.
The arithmetic identity is Mathlib's Chebyshev.psi_sub_theta_eq_sum_not_prime. -/
theorem nonprime_mass_eq384 (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (vonMangoldt k - if k.Prime then vonMangoldt k else 0)) =
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  symm
  calc
    _ = ∑ k ∈ Finset.Ioc 0 N,
        (vonMangoldt k - if k.Prime then vonMangoldt k else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hp : k.Prime <;> simp [hp]
    _ = _ := by
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_Ioc, Finset.mem_range] at *
        omega
      · intro k hk hnot
        have hk0 : k = 0 := by
          simp only [Finset.mem_range, Finset.mem_Ioc, not_and_or, not_lt] at *
          omega
        subst k
        simp

/-- The whole prime power correction is bounded by twice log N times psi minus theta.
Source: derived estimate for P0029 page 4. No exceptional set hypothesis is needed. -/
theorem r2_sub_primeR2_le384 (N : ℕ) (hN : 1 ≤ N) :
    r2 N - primeR2_384 N ≤
      2 * Real.log N * (Chebyshev.psi N - Chebyshev.theta N) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hf (k : ℕ) (hk : k ≤ N) : vonMangoldt k ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hlog
    · exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hkpos)
        (by exact_mod_cast hk))
  have hbound (k : ℕ) (hk : k ≤ N) :
      0 ≤ (if k.Prime then vonMangoldt k else 0) ∧
      (if k.Prime then vonMangoldt k else 0) ≤ vonMangoldt k ∧
      vonMangoldt k ≤ Real.log N := by
    by_cases hp : k.Prime
    · rw [ite_eq_left hp]
      exact ⟨vonMangoldt_nonneg, le_rfl, hf k hk⟩
    · rw [ite_eq_right hp]
      exact ⟨le_rfl, vonMangoldt_nonneg, hf k hk⟩
  have h := convolution_defect_le384 N vonMangoldt
    (fun k => if k.Prime then vonMangoldt k else 0) (Real.log N) hbound
  rw [nonprime_mass_eq384] at h
  rw [primeR2_eq_convolution384]
  change (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
    vonMangoldt x.1 * vonMangoldt x.2) - _ ≤ _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => vonMangoldt a * vonMangoldt b)]
  exact h

/-- The prime part is nonnegative and is at most the full von Mangoldt convolution.
Source: P0029 page 4, the omitted contribution is nonnegative. -/
theorem primeR2_bounds384 (N : ℕ) : 0 ≤ primeR2_384 N ∧ primeR2_384 N ≤ r2 N := by
  rw [primeR2_eq_convolution384, r2,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => vonMangoldt a * vonMangoldt b)]
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    split_ifs <;> positivity
  · apply Finset.sum_le_sum
    intro k hk
    by_cases hp : k.Prime <;> by_cases hq : (N - k).Prime <;>
      simp only [hp, hq, ↓reduceIte, mul_zero, zero_mul] <;> first | exact le_rfl | positivity

/-- Positivity of the logarithmically weighted prime count is exactly Goldbach representability.
Source: P0029 page 4 and the representation interpretation on page 9. -/
theorem primeR2_pos_iff384 (N : ℕ) : 0 < primeR2_384 N ↔ IsGoldbachSum N := by
  constructor
  · intro hpos
    by_contra hnot
    rw [primeR2_zero_of_not_goldbach384 N hnot] at hpos
    exact (lt_irrefl 0) hpos
  · rintro ⟨p, q, hp, hq, rfl⟩
    unfold primeR2_384
    apply Finset.sum_pos'
    · intro k hk
      split_ifs with h
      · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast h.1.one_lt.le))
          (Real.log_nonneg (by exact_mod_cast h.2.one_lt.le))
      · exact le_rfl
    · refine ⟨p, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [Nat.add_sub_cancel_left, hp, hq, and_self, ↓reduceIte]
      exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
        (Real.log_pos (by exact_mod_cast hq.one_lt))

/-- An explicit square root times logarithm squared bound for the omitted prime powers.
Source: derived estimate for P0029 page 4, using Mathlib's Chebyshev bound.
The coefficient four is not a constant printed in the survey. -/
theorem r2_sub_primeR2_sqrt_log_sq384 (N : ℕ) (hN : 1 ≤ N) :
    r2 N - primeR2_384 N ≤ 4 * Real.sqrt N * (Real.log N) ^ 2 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ 2 * Real.log N * (Chebyshev.psi N - Chebyshev.theta N) :=
      r2_sub_primeR2_le384 N hN
    _ ≤ 2 * Real.log N * (2 * Real.sqrt N * Real.log N) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le (by exact_mod_cast hN))
        (by positivity)
    _ = _ := by ring

/-- A corrected square root bound at an actual Goldbach exception.
Source: derived estimate for P0029 pages 4 and 13.
This does not prove the sealed natural exponent zero bound. -/
theorem r2_exception_sqrt_log_sq384 (N : ℕ) (hN : 1 ≤ N)
    (hnot : ¬ IsGoldbachSum N) :
    r2 N ≤ 4 * Real.sqrt N * (Real.log N) ^ 2 := by
  simpa only [primeR2_zero_of_not_goldbach384 N hnot, sub_zero] using
    r2_sub_primeR2_sqrt_log_sq384 N hN


end LeanLab.BhowmikGrimmelt2026
