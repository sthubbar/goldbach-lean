module

public import LeanLab.Linnik1951.Decomp357a
public import LeanLab.Linnik1951.KernelBounds376

/-!
P0093 pages 157 and 158 equations 4.4 to 4.7. Separate the contour estimate from two real kernels.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 158 after equation 4.6. The reciprocal difference kernel
integrated over the square frequency box of radius T. -/
noncomputable def differenceKernel376 (T : ℝ) : ℝ :=
  ∫ t in -T..T, ∫ u in -T..T, 1 / (1 + |t - u|)

/-- P0093 page 158 negative frequency sum case before equation 4.7.
The exponentially decreasing sum kernel on the same square box. -/
noncomputable def sumKernel376 (T : ℝ) : ℝ :=
  ∫ t in -T..T, ∫ u in -T..T, Real.exp (-(Real.pi / 4) * |t + u|)

/-- LEAF. P0093 page 158 positive frequency sum case after equation
4.6. Integrating the reciprocal difference kernel costs a factor
T log of 2T plus 1. The constant eight enlarges the elementary bound. -/
theorem difference_kernel_le376 (T : ℝ) (hT : 1 ≤ T) :
    differenceKernel376 T ≤ 8 * T * Real.log (2 * T + 1) := by
  let f : ℝ → ℝ := fun x => 1 / (1 + |x|)
  have hf : Continuous f :=
    continuous_const.div (continuous_const.add continuous_abs) (fun x => ne_of_gt (by positivity))
  have hchange : differenceKernel376 T = ∫ t in -T..T, ∫ u in -T..T, f (t + u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hh := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => 1 / (1 + |t + u|)) (a := -T) (b := T)
    simpa only [neg_neg, sub_eq_add_neg] using hh
  have hbox := kernel_box_bound376 f hf (fun x => by dsimp [f]; positivity) T (by linarith)
  calc
    _ = ∫ t in -T..T, ∫ u in -T..T, f (t + u) := hchange
    _ ≤ 2 * T * (∫ v in -(2 * T)..(2 * T), f v) := hbox
    _ = 4 * T * Real.log (2 * T + 1) := by
      rw [show (∫ v in -(2 * T)..(2 * T), f v) = 2 * Real.log (2 * T + 1) from
        reciprocal_abs_integral376 (2 * T) (by linarith)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith))

/-- LEAF. P0093 page 158 negative frequency sum case before equation
4.7. Integrating the decaying sum kernel costs a factor T. The constant
sixteen enlarges the full line exponential integral estimate. -/
theorem sum_kernel_le376 (T : ℝ) (hT : 1 ≤ T) :
    sumKernel376 T ≤ 16 * T := by
  have hf : Continuous (fun x : ℝ => Real.exp (-(Real.pi / 4) * |x|)) := by fun_prop
  have hbox := kernel_box_bound376 _ hf (fun x => (Real.exp_pos _).le) T (by linarith)
  have he := exp_abs_integral_le376 (Real.pi / 4) (2 * T) (by positivity) (by linarith)
  have hp : 2 / (Real.pi / 4) ≤ 8 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi / 4)).mpr
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ 2 * T * (∫ v in -(2 * T)..(2 * T), Real.exp (-(Real.pi / 4) * |v|)) := hbox
    _ ≤ 2 * T * 8 := mul_le_mul_of_nonneg_left (he.trans hp) (by linarith)
    _ = _ := by ring


/-- P0093 page 158 substitution before equation 4.7. When the frequency
radius is at most N log cubed N, its logarithm is at most 5 log N. -/
theorem frequency_window_log376 (x R : ℝ) (hx : 3 ≤ x) (hR : 0 ≤ R) (hRx : R ≤ x) :
    Real.log (2 * (R * Real.log x ^ 3) + 1) ≤ 5 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x)]
  have hT : R * Real.log x ^ 3 ≤ x ^ 4 := by
    calc
      _ ≤ x * x ^ 3 := mul_le_mul hRx (pow_le_pow_left₀ hlog0 hlog 3) (by positivity) (by linarith)
      _ = _ := by ring
  have hp : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have hcut : 2 * (R * Real.log x ^ 3) + 1 ≤ x ^ 5 := by
    calc
      _ ≤ 2 * x ^ 4 + 1 := by linarith
      _ ≤ 3 * x ^ 4 := by linarith
      _ ≤ x * x ^ 4 := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = _ := by ring
  have hh := Real.log_le_log (by positivity : 0 < 2 * (R * Real.log x ^ 3) + 1) hcut
  rwa [Real.log_pow] at hh

end LeanLab.Linnik1951
