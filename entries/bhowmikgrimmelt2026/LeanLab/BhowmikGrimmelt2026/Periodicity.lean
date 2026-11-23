module

public import LeanLab.BhowmikGrimmelt2026.WeightEstimates

/-!
Periodicity and distance to the nearest integer in equations 7.6 and 7.7, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The paper's distance to the nearest integer. -/
noncomputable def intDist (β : ℝ) : ℝ := |β - round β|

/-- Distance to the integers is nonnegative. -/
theorem intDist_nonneg (β : ℝ) : 0 ≤ intDist β := abs_nonneg _

/-- A nearest integer is at distance at most one half. -/
theorem intDist_le_half (β : ℝ) : intDist β ≤ 1 / 2 := abs_sub_round β

/-- Distance to the integers is at most distance to any chosen integer. -/
theorem intDist_le_abs_sub (β : ℝ) (k : ℤ) : intDist β ≤ |β - k| := round_le β k

/-- The additive exponential is one at integer arguments. -/
theorem ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) =
    (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- Adding an integer leaves the additive exponential unchanged. -/
theorem ee_add_int (x : ℝ) (k : ℤ) : ee (x + k) = ee x := by
  rw [← ee_mul, ee_int, mul_one]

/-- The discrete transform of the scaled weight is periodic under integer translations. -/
theorem GThat_add_int (G : ℝ → ℝ) (T β : ℝ) (k : ℤ) :
    GThat G T (β + k) = GThat G T β := by
  apply tsum_congr
  intro n
  have hp : (β + k) * (n : ℝ) = β * n + ((k * n : ℤ) : ℝ) := by push_cast; ring
  rw [hp, ee_add_int]

/-- Subtracting a nearest integer leaves the discrete transform unchanged. -/
theorem GThat_center (G : ℝ → ℝ) (T β : ℝ) :
    GThat G T (β - round β) = GThat G T β := by
  simpa only [sub_eq_add_neg, Int.cast_neg] using GThat_add_int G T β (-round β)

/-- Equation 7.6 using distance to the nearest integer, for every real frequency. -/
theorem GThat_bound {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T β : ℝ, 1 ≤ T →
      ‖GThat G T β‖ ≤ C * ((1 + T * intDist β) ^ (-A) + T ^ (-A)) := by
  obtain ⟨C, hC, hbound⟩ := GThat_bound_centered hsupp hsmooth A
  refine ⟨C, hC, fun T β hT => ?_⟩
  have h := hbound T (β - round β) hT (abs_sub_round β)
  rwa [GThat_center] at h

/-- Equation 7.7 using distance to the nearest integer, with an explicit quadratic constant. -/
theorem GThat_central {G : ℝ → ℝ} (hG : IsMajorWeight G) (A : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ T β : ℝ, 1 ≤ T →
      ‖GThat G T β - 1‖ ≤ 8 * Real.pi ^ 2 * (T * intDist β) ^ 2 + D * T ^ (-A) := by
  obtain ⟨D, hD, hbound⟩ := GThat_central_centered hG A
  refine ⟨D, hD, fun T β hT => ?_⟩
  have h := hbound T (β - round β) hT (abs_sub_round β)
  rw [GThat_center] at h
  simpa only [intDist, mul_pow, sq_abs] using h

end LeanLab.BhowmikGrimmelt2026
