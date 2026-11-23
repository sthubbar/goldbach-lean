module

public import Mathlib

/-!
P0093 page 158. Elementary real kernel integrals used after equation 4.6.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 158 symmetric frequency box. Integrating an even
continuous function on a symmetric interval doubles its positive half. -/
theorem symmetric_integral376 (f : ℝ → ℝ) (hf : Continuous f)
    (heven : ∀ x, f (-x) = f x) (A : ℝ) :
    (∫ x in -A..A, f x) = 2 * (∫ x in (0 : ℝ)..A, f x) := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-A) 0) (hf.intervalIntegrable 0 A)
  have hneg : (∫ x in -A..0, f x) = ∫ x in (0 : ℝ)..A, f x := by
    calc
      _ = ∫ x in (0 : ℝ)..A, f (-x) := by
        simpa using (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := A)).symm
      _ = _ := intervalIntegral.integral_congr (fun x _ => heven x)
  rw [← hadd, hneg]
  ring

/-- P0093 page 158 integration of a frequency kernel on a square box.
Each translated inner interval lies in the symmetric interval of twice
the radius. Nonnegativity permits that enlargement. -/
theorem kernel_box_bound376 (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 ≤ f x) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in -T..T, ∫ u in -T..T, f (t + u)) ≤
      2 * T * (∫ v in -(2 * T)..(2 * T), f v) := by
  have hcont : Continuous (fun t : ℝ => ∫ u in -T..T, f (t + u)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) (-T) T
  calc
    _ ≤ ∫ _t in -T..T, ∫ v in -(2 * T)..(2 * T), f v := by
      apply intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
        intervalIntegrable_const
      intro t ht
      rw [intervalIntegral.integral_comp_add_left]
      apply intervalIntegral.integral_mono_interval (by linarith [ht.1])
        (by linarith) (by linarith [ht.2]) (ae_of_all _ hpos) (hf.intervalIntegrable _ _)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- P0093 page 158 reciprocal difference kernel. The symmetric
one dimensional integral has the exact elementary logarithmic value. -/
theorem reciprocal_abs_integral376 (A : ℝ) (hA : 0 ≤ A) :
    (∫ x in -A..A, 1 / (1 + |x|)) = 2 * Real.log (A + 1) := by
  have hf : Continuous (fun x : ℝ => 1 / (1 + |x|)) :=
    continuous_const.div (continuous_const.add continuous_abs) (fun x => ne_of_gt (by positivity))
  rw [symmetric_integral376 _ hf (fun x => by rw [abs_neg]) A]
  congr 1
  calc
    _ = ∫ x in (0 : ℝ)..A, 1 / (1 + x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      dsimp only
      rw [abs_of_nonneg hx.1]
    _ = ∫ x in (1 : ℝ)..(A + 1), 1 / x := by
      simpa only [add_zero, zero_add, add_comm] using
        (intervalIntegral.integral_comp_add_left (f := fun x : ℝ => 1 / x) (a := 0) (b := A) 1)
    _ = _ := by rw [integral_one_div_of_pos (by norm_num) (by linarith)]; simp

/-- P0093 page 158 decaying sum kernel. Its symmetric one dimensional
integral is at most twice the inverse decay rate. -/
theorem exp_abs_integral_le376 (c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) :
    (∫ x in -A..A, Real.exp (-c * |x|)) ≤ 2 / c := by
  have hf : Continuous (fun x : ℝ => Real.exp (-c * |x|)) := by fun_prop
  rw [symmetric_integral376 _ hf (fun x => by rw [abs_neg]) A]
  have hhalf : (∫ x in (0 : ℝ)..A, Real.exp (-c * |x|)) =
      (1 - Real.exp (-c * A)) / c := by
    calc
      _ = ∫ x in (0 : ℝ)..A, Real.exp (-c * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hA] at hx
        dsimp only
        rw [abs_of_nonneg hx.1]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr hc.ne'), integral_exp]
        simp only [mul_zero, Real.exp_zero, smul_eq_mul]
        field_simp
        <;> ring
  rw [hhalf]
  have he := Real.exp_pos (-(c * A))
  apply (le_div_iff₀ hc).mpr
  field_simp
  nlinarith

end LeanLab.Linnik1951
