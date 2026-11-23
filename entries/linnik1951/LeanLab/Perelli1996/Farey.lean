module

public import Mathlib

/-!
P0083, page 483, equation 13. Separation of rational arc centers.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Farey
open Real

/-- Distinct fractions with positive denominators have the standard spacing. -/
theorem rational_separation (a b : ℤ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hcross : a * (r : ℤ) - b * (q : ℤ) ≠ 0 := by
    intro hz
    apply hne
    apply (div_eq_div_iff hq0 hr0).2
    have : a * (r : ℤ) = b * (q : ℤ) := sub_eq_zero.mp hz
    exact_mod_cast this
  have hone : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hcross
  have hden : 0 < (q : ℝ) * r := by positivity
  have hid : (a : ℝ) / q - (b : ℝ) / r =
      ((a : ℝ) * r - (b : ℝ) * q) / ((q : ℝ) * r) := by field_simp
  rw [hid, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right hone hden.le

/-- Equation 13 with a common upper bound for both denominators. -/
theorem bounded_denominator_separation (a b : ℤ) (q r : ℕ) {Q : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hqQ : (q : ℝ) ≤ Q) (hrQ : (r : ℝ) ≤ Q)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) :
    1 / Q ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQ : 0 < Q := lt_of_lt_of_le hqR hqQ
  have hprod : (q : ℝ) * r ≤ Q ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hqQ) (sub_nonneg.mpr hrQ)]
  calc 1 / Q ^ 2 ≤ 1 / ((q : ℝ) * r) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        simpa using hprod
    _ ≤ _ := rational_separation a b q r hq hr hne

end LeanLab.Perelli1996.Farey
