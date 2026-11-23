module

public import LeanLab.Linnik1951.Decomp521a
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
P0093 pages 155 and 161. Exact centred interval Fourier kernels.
The core and full period remain distinct. No asymptotic estimate is assumed.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open MeasureTheory
namespace LeanLab.Linnik1951

/-- P0093 page 161 equation 6.3. Exact auxiliary kernel for a symmetric
interval. This identity retains the radius rather than assuming orthogonality. -/
theorem symmetric_phase_integral552 (r w : ℝ) :
    (∫ z in -r..r, Complex.exp (((w * z : ℝ) : ℂ) * Complex.I)) =
      ((2 * r * Real.sinc (w * r) : ℝ) : ℂ) := by
  by_cases hw : w = 0
  · simp [hw, two_mul]
  calc
    _ = w⁻¹ • (∫ t in -(w * r)..(w * r), Complex.exp ((t : ℂ) * Complex.I)) := by
      simpa only [mul_neg] using
        (intervalIntegral.integral_comp_mul_left
          (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hw (a := -r) (b := r))
    _ = _ := by
      rw [integral_exp_mul_I_eq_sinc]
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
      push_cast
      field_simp [show (w : ℂ) ≠ 0 by exact_mod_cast hw]


/-- P0093 page 161 equation 6.3. Termwise integration on a centred
interval keeps the sinc factor of every frequency. -/
theorem series_symmetric_integral552 (a : ℕ → ℂ) (ha : Summable a)
    (r : ℝ) (hr : 0 ≤ r) (c w : ℝ) :
    (∫ z in -r..r, (∑' k : ℕ, a k *
      Complex.exp ((-(2 * Real.pi * (c + z) * k) : ℝ) * Complex.I)) *
        Complex.exp (((w * (c + z) : ℝ) : ℂ) * Complex.I)) =
    ∑' k : ℕ, a k * Complex.exp ((((w - 2 * Real.pi * k) * c : ℝ) : ℂ) * Complex.I) *
      ((2 * r * Real.sinc ((w - 2 * Real.pi * k) * r) : ℝ) : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun k z => a k *
    Complex.exp ((-(2 * Real.pi * (c + z) * k) : ℝ) * Complex.I) *
      Complex.exp (((w * (c + z) : ℝ) : ℂ) * Complex.I)
  have hF (k : ℕ) : Continuous (F k) := by dsimp [F]; fun_prop
  have hFnorm (k : ℕ) (z : ℝ) : ‖F k z‖ = ‖a k‖ := by
    dsimp [F]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hI (k : ℕ) : IntegrableOn (F k) (Set.Ioc (-r) r) :=
    (hF k).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnormI (k : ℕ) : (∫ z in Set.Ioc (-r) r, ‖F k z‖) = (2 * r) * ‖a k‖ := by
    simp only [hFnorm]
    simp [sub_neg_eq_add, hr, two_mul, add_mul]
  have hswap := integral_tsum_of_summable_integral_norm hI
    ((ha.norm.mul_left (2 * r)).congr (fun k => (hnormI k).symm))
  have hs (z : ℝ) : (∑' k : ℕ, a k *
      Complex.exp ((-(2 * Real.pi * (c + z) * k) : ℝ) * Complex.I)) *
        Complex.exp (((w * (c + z) : ℝ) : ℂ) * Complex.I) = ∑' k : ℕ, F k z :=
    tsum_mul_right.symm
  simp_rw [hs]
  rw [intervalIntegral.integral_of_le (by linarith), ← hswap]
  apply tsum_congr
  intro k
  rw [← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have heq (z : ℝ) : F k z =
      (a k * Complex.exp ((((w - 2 * Real.pi * k) * c : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((((w - 2 * Real.pi * k) * z : ℝ) : ℂ) * Complex.I) := by
    dsimp [F]
    simp only [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, symmetric_phase_integral552]


/-- P0093 page 161 equation 6.3. Exact auxiliary formula for a squared
summable series on a centred interval translated by c. Each convolution
frequency keeps its own sinc kernel. -/
theorem square_symmetric_integral552 (a : ℕ → ℂ) (ha : Summable a)
    (r : ℝ) (hr : 0 ≤ r) (c : ℝ) (n : ℤ) :
    (∫ z in -r..r, (∑' k : ℕ, a k *
      Complex.exp ((-(2 * Real.pi * (c + z) * k) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * (c + z) : ℝ) : ℂ) * Complex.I)) =
    ∑' k : ℕ, (∑ m ∈ Finset.range (k + 1), a m * a (k - m)) *
      Complex.exp (((2 * Real.pi * ((n : ℝ) - k) * c : ℝ) : ℂ) * Complex.I) *
      ((2 * r * Real.sinc (2 * Real.pi * ((n : ℝ) - k) * r) : ℝ) : ℂ) := by
  simp_rw [square_series521 a ha]
  have hconv : Summable (fun k => ∑ m ∈ Finset.range (k + 1), a m * a (k - m)) :=
    (summable_norm_sum_mul_range_of_summable_norm ha.norm ha.norm).of_norm
  rw [series_symmetric_integral552 _ hconv r hr c (2 * Real.pi * n)]
  congr 1
  ext k
  congr 2 <;> congr 1 <;> ring

/-- P0093 page 161 equation 6.3. Auxiliary small residual diagnostic.
The single negative mode at two has nonzero squared integral at residual
zero on radius one over sixteen. Its full period coefficient is zero. -/
theorem small_residual_offdiagonal552 :
    (∫ z in -(1 / (16 : ℝ))..(1 / (16 : ℝ)),
      Complex.exp ((-(4 * Real.pi * z) : ℝ) * Complex.I) ^ 2) =
        ((1 / (4 * Real.pi) : ℝ) : ℂ) := by
  have hp (z : ℝ) : Complex.exp ((-(4 * Real.pi * z) : ℝ) * Complex.I) ^ 2 =
      Complex.exp ((((-8 * Real.pi) * z : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [symmetric_phase_integral552]
  have he : (-8 * Real.pi) * (1 / (16 : ℝ)) = -(Real.pi / 2) := by ring
  rw [he, Real.sinc_neg, Real.sinc_of_ne_zero (by positivity : Real.pi / 2 ≠ 0),
    Real.sin_pi_div_two]
  push_cast
  field_simp
  <;> ring

end LeanLab.Linnik1951
