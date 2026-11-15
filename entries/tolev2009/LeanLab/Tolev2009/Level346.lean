module

public import LeanLab.Tolev2009.Progression346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Tolev 2009 page 3 cutoffs and Halupczok 2008 pages 6 and 9 to 11.
This comparison uses the exposed theta level at discrepancy exponent one hundred A.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Level346
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-- Halupczok pages 6 and 9, the 2009 lcm product range fits the explicit theta level. -/
theorem lcm_below_theta_level (A : ℝ) (N k q : ℕ)
    (hA : 10 ^ 4 ≤ A) (hL : 1 ≤ Real.log N)
    (hk : (k : ℝ) ≤ Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)))
    (hq : (q : ℝ) ≤ Qof A N) :
    Nat.lcm k q ≤ ⌊Real.sqrt N / Real.log N ^ (4 * (100 * A) + 15)⌋₊ := by
  have hL0 : 0 < Real.log N := by linarith
  apply Nat.le_floor
  calc
    (Nat.lcm k q : ℝ) ≤ (k : ℝ) * q := by
      by_cases hk0 : k = 0
      · simp [hk0]
      by_cases hq0 : q = 0
      · simp [hq0]
      exact_mod_cast Nat.le_of_dvd (by positivity : 0 < k * q) (Nat.lcm_dvd_mul k q)
    _ ≤ (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) * Qof A N :=
      mul_le_mul hk hq (Nat.cast_nonneg _) (by positivity)
    _ = Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A) + 20 * A) := by
      unfold Qof
      rw [mul_assoc, ← Real.rpow_add hL0]
    _ ≤ Real.sqrt N * Real.log N ^ (-(4 * (100 * A) + 15)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    _ = Real.sqrt N / Real.log N ^ (4 * (100 * A) + 15) := by
      rw [Real.rpow_neg hL0.le, div_eq_mul_inv]

/-- Tolev page 3, the third cutoff is at most the first cutoff under the printed large N regime. -/
theorem third_cutoff_le_first (B : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Dyadic.cutoff3 B N ≤ Dyadic.cutoff B N := by
  unfold Dyadic.cutoff3 Dyadic.cutoff
  apply Nat.floor_le_floor
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _)
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)

/-- Tolev page 3, every natural major arc denominator and first cutoff modulus lies in that theta range. -/
theorem first_cutoff_lcm (A : ℝ) (N k q : ℕ) (hA : 10 ^ 4 ≤ A)
    (hL : 1 ≤ Real.log N) (hk : k ≤ Dyadic.cutoff (10 ^ 4 * A) N)
    (hq : q ≤ ⌊Qof A N⌋₊) :
    Nat.lcm k q ≤ ⌊Real.sqrt N / Real.log N ^ (4 * (100 * A) + 15)⌋₊ := by
  apply lcm_below_theta_level A N k q hA hL
  · exact (Nat.cast_le.mpr hk).trans (Nat.floor_le (by positivity))
  · exact (Nat.cast_le.mpr hq).trans (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _))

/-- Tolev page 3, the same theta range contains the fixed third modulus lcm. -/
theorem third_cutoff_lcm (A : ℝ) (N k q : ℕ) (hA : 10 ^ 4 ≤ A)
    (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hk : k ≤ Dyadic.cutoff3 (10 ^ 4 * A) N)
    (hq : q ≤ ⌊Qof A N⌋₊) :
    Nat.lcm k q ≤ ⌊Real.sqrt N / Real.log N ^ (4 * (100 * A) + 15)⌋₊ := by
  exact first_cutoff_lcm A N k q hA hL (hk.trans (third_cutoff_le_first _ N hN)) hq

end LeanLab.Tolev2009.Level346
