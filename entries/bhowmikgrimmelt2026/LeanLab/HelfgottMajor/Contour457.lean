module

public import LeanLab.HelfgottMajor.Decomp269a
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
The continued Mellin contour and Cauchy Schwarz step of P0014 pages 33 to 35.
These definitions keep the scale factor and the derivative in display 4.14.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Contour457
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a

/-- The continued Gaussian Mellin transform in displays 4.6 and 4.14, pages 33 and 35.
Integration by parts gives s times F as F at s plus two minus two pi i delta times F
at s plus one. Both Mellin integrals converge on the contour of real part minus one half.
-/
noncomputable def continuedGaussian (δ : ℝ) (s : ℂ) : ℂ :=
  (gaussianMellin δ (s + 2) -
    (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) / s

/-- The conductor one contour integral in display 4.7 on page 33.
The vertical parameterization absorbs the factor i from ds.
-/
noncomputable def principalContour (δ x : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
      continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)

/-- The logarithmic derivative weight in the first Cauchy Schwarz factor on page 35.
The factor s in the denominator is retained exactly as in display 4.13.
-/
noncomputable def principalLogWeight (t : ℝ) : ℂ :=
  logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) /
    ((-1 / 2 : ℂ) + t * Complex.I)

/-- The regular Gaussian numerator in display 4.14 on page 35.
This is minus the Mellin transform of t times the derivative of the shifted Gaussian.
-/
noncomputable def gaussianNumerator (δ t : ℝ) : ℂ :=
  gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 2) -
    (2 * π * Complex.I * δ) * gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 1)

/-- Cauchy Schwarz on the vertical line of real part minus one half.
Source P0014 pages 34 and 35, displays 4.13 to 4.15.
The square integrability hypotheses are explicit. No numerical analytic budget is assumed.
-/
theorem norm_integral_mul_cpow_le (f g : ℝ → ℂ) (hf : MemLp f 2) (hg : MemLp g 2)
    (x : ℝ) (hx : 0 < x) :
    ‖∫ t : ℝ, f t * g t * (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      sqrt (∫ t : ℝ, ‖f t‖ ^ 2) * sqrt (∫ t : ℝ, ‖g t‖ ^ 2) / sqrt x := by
  have hpow (t : ℝ) : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ = (sqrt x)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_zero, add_zero]
    rw [rpow_neg hx.le, sqrt_eq_rpow]
  have hi : Integrable (fun t : ℝ => ‖f t‖ * ‖g t‖ / sqrt x) :=
    (hf.norm.integrable_mul hg.norm).div_const _
  have hcs := integral_mul_norm_le_Lp_mul_Lq (f := f) (g := g) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2) (by simpa using hf) (by simpa using hg)
  simp only [rpow_two, ← sqrt_eq_rpow] at hcs
  calc
    _ ≤ ∫ t : ℝ, ‖f t‖ * ‖g t‖ / sqrt x := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with t
      rw [norm_mul, norm_mul, hpow, div_eq_mul_inv]
    _ = (∫ t : ℝ, ‖f t‖ * ‖g t‖) / sqrt x := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hcs (sqrt_nonneg x)

/-- The principal contour estimate from its two explicit square energy inputs.
CONDITIONAL ON hL, hG and hbudget. This is the Cauchy Schwarz step on pages 34 and 35.
-/
theorem principal_contour_bound_of_L2 (δ x : ℝ) (hx : 1 ≤ x)
    (hL : MemLp principalLogWeight 2) (hG : MemLp (gaussianNumerator δ) 2)
    (hbudget : sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) *
      sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) ≤
        2 * π * 6.01 * (1 + 6 * |δ|)) :
    ‖principalContour δ x‖ ≤ 6.01 * (1 + 6 * |δ|) / sqrt x := by
  have hx0 : 0 < x := by linarith
  have heq : principalContour δ x =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        principalLogWeight t * gaussianNumerator δ t *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := by
    unfold principalContour continuedGaussian principalLogWeight gaussianNumerator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg pi_pos.le]
  rw [heq, norm_mul, hc]
  calc
    _ ≤ (1 / (2 * π)) *
        (sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) *
          sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) / sqrt x) :=
      mul_le_mul_of_nonneg_left
        (norm_integral_mul_cpow_le _ _ hL hG x hx0) (by positivity)
    _ ≤ (1 / (2 * π)) * (2 * π * 6.01 * (1 + 6 * |δ|) / sqrt x) := by
      gcongr
    _ = _ := by field_simp

end LeanLab.HelfgottMajor.Contour457
