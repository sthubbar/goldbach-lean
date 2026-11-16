module

public import LeanLab.Pintz2018.Curvature117

/-!
The Laplace kernel transformation in Pintz 2018, page 35, display 8.11.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Laplace117
open MeasureTheory

/-- The factorization behind the change to exponential coordinates in 8.11. -/
theorem laplace_factor (d0 d T v : ℝ) :
    Real.exp (-(d0 - d) * (v * T)) =
      Real.exp (-d0 * (v * T)) * (Real.exp (d * T)) ^ v := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _) v, Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- The scaled Laplace integral has exactly the weighted power cost used by the exchange proof.
Source: page 35, display 8.11, with the scaling on page 34. -/
theorem laplace_integral_identity (f : ℝ → ℝ) (d0 d T : ℝ) :
    T * (∫ v in Set.Icc (0 : ℝ) 1, f (v * T) * Real.exp (-(d0 - d) * (v * T))) =
      ∫ v in Set.Icc (0 : ℝ) 1,
        (T * f (v * T) * Real.exp (-d0 * (v * T))) * (Real.exp (d * T)) ^ v := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [laplace_factor d0 d T v]
  ring

/-- The actual continuous nonnegative Laplace weight in 8.11 supplies a concave cost.
Source: page 14, Condition 1, and page 35, display 8.11. -/
theorem laplace_cost_concave (f : ℝ → ℝ) (d0 T : ℝ) (hT : 0 < T)
    (hf : Continuous f) (hf0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t) :
    ConcaveOn ℝ (Set.Ici 1) (fun y : ℝ => ∫ v in Set.Icc (0 : ℝ) 1,
      (T * f (v * T) * Real.exp (-d0 * (v * T))) * y ^ v) := by
  apply Curvature117.integral_cost_concave
  · fun_prop
  · intro v hv
    have hv0 : 0 ≤ v * T := mul_nonneg hv.1 hT.le
    have hvT : v * T ≤ T := by nlinarith [hv.2]
    exact mul_nonneg (mul_nonneg hT.le (hf0 (v * T) ⟨hv0, hvT⟩)) (Real.exp_pos _).le

end LeanLab.Pintz2018.Laplace117
