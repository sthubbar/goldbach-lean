module

public import LeanLab.BhowmikGrimmelt2026.PoissonTail

/-!
The quadratic central Fourier estimate in equation 7.7, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

/-- An even weight has an even continuous Fourier transform. -/
theorem fourier_weight_even {G : ℝ → ℝ} (heven : ∀ x, G (-x) = G x) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (G x : ℂ)) (-ξ) = 𝓕 (fun x : ℝ => (G x : ℂ)) ξ := by
  rw [fourier_eq_integral_ee, fourier_eq_integral_ee]
  conv_lhs => rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [heven, neg_neg, mul_neg, neg_mul]

/-- Pairing opposite exponentials gives twice the cosine. -/
theorem ee_add_neg (x : ℝ) :
    ee x + ee (-x) = ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  have h (y : ℝ) : ee y =
      (Real.cos (2 * Real.pi * y) : ℂ) + (Real.sin (2 * Real.pi * y) : ℂ) * Complex.I := by
    unfold ee
    rw [show 2 * (Real.pi : ℂ) * Complex.I * y =
      ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I _
  rw [h x, h (-x)]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

/-- Compact smooth weights remain integrable after modulation. -/
theorem integrable_weight_ee {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (hsmooth : ContDiff ℝ ∞ G) (ξ : ℝ) :
    Integrable (fun x : ℝ => (G x : ℂ) * ee (ξ * x)) := by
  have hc : HasCompactSupport (fun x : ℝ => (G x : ℂ) * ee (ξ * x)) :=
    ((HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).comp_left
      (g := Complex.ofReal) rfl).mul_right
  exact ((Complex.continuous_ofReal.comp hsmooth.continuous).mul
    (ee_contDiff.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hc

/-- For an even smooth weight, its continuous Fourier transform is the real cosine integral. -/
theorem fourier_eq_cos_integral {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G)
    (heven : ∀ x, G (-x) = G x) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (G x : ℂ)) ξ =
      ((∫ x : ℝ, G x * Real.cos (2 * Real.pi * ξ * x)) : ℂ) := by
  have hi1 := integrable_weight_ee hsupp hsmooth (-ξ)
  have hi2 := integrable_weight_ee hsupp hsmooth ξ
  apply (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0))
  calc
    2 * 𝓕 (fun x : ℝ => (G x : ℂ)) ξ =
        𝓕 (fun x : ℝ => (G x : ℂ)) ξ + 𝓕 (fun x : ℝ => (G x : ℂ)) (-ξ) := by
      rw [fourier_weight_even heven]; ring
    _ = ∫ x : ℝ, (G x : ℂ) * (ee (ξ * x) + ee (-(ξ * x))) := by
      rw [fourier_eq_integral_ee, fourier_eq_integral_ee, ← integral_add hi1]
      · apply integral_congr_ae
        filter_upwards [] with x
        simp only [neg_neg, neg_mul]
        ring
      · simpa using hi2
    _ = 2 * ((∫ x : ℝ, G x * Real.cos (2 * Real.pi * ξ * x)) : ℂ) := by
      simp_rw [ee_add_neg]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      push_cast
      simp only [mul_assoc]
      ring

/-- The support and nonnegativity give a pointwise quadratic cosine remainder. -/
theorem weight_cos_error {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (hnonneg : ∀ x, 0 ≤ G x) (ξ x : ℝ) :
    |G x * (Real.cos (2 * Real.pi * ξ * x) - 1)| ≤
      (8 * Real.pi ^ 2 * ξ ^ 2) * G x := by
  by_cases hx : G x = 0
  · simp [hx]
  have hxs := hsupp hx
  have hsq : x ^ 2 ≤ 4 := by nlinarith [hxs.1, hxs.2]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ξ * x)
  have hscale := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 2 * Real.pi ^ 2 * ξ ^ 2 by positivity)
  have herr : |Real.cos (2 * Real.pi * ξ * x) - 1| ≤ 8 * Real.pi ^ 2 * ξ ^ 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    nlinarith only [hcos, hscale]
  rw [abs_mul, abs_of_nonneg (hnonneg x)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left herr (hnonneg x)

/-- The normalized even major weight has a quadratic Fourier approximation at zero. -/
theorem fourier_weight_quadratic {G : ℝ → ℝ} (hG : IsMajorWeight G) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (G x : ℂ)) ξ - 1‖ ≤ 8 * Real.pi ^ 2 * ξ ^ 2 := by
  have hc : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hG.supp
  have hi : Integrable G := hG.smooth.continuous.integrable_of_hasCompactSupport hc
  have hicos : Integrable (fun x : ℝ => G x * Real.cos (2 * Real.pi * ξ * x)) :=
    (hG.smooth.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hid : Integrable (fun x : ℝ => G x * (Real.cos (2 * Real.pi * ξ * x) - 1)) := by
    convert hicos.sub hi using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have hidabs : Integrable (fun x : ℝ => |G x * (Real.cos (2 * Real.pi * ξ * x) - 1)|) := hid.abs
  have hib : Integrable (fun x : ℝ => (8 * Real.pi ^ 2 * ξ ^ 2) * G x) := hi.const_mul _
  rw [fourier_eq_cos_integral hG.supp hG.smooth hG.even]
  simp only [← Complex.ofReal_mul]
  rw [show (∫ x : ℝ, ((G x * Real.cos (2 * Real.pi * ξ * x) : ℝ) : ℂ)) =
    Complex.ofReal (∫ x : ℝ, G x * Real.cos (2 * Real.pi * ξ * x)) from integral_ofReal]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have heq : (∫ x : ℝ, G x * Real.cos (2 * Real.pi * ξ * x)) - 1 =
      ∫ x : ℝ, G x * (Real.cos (2 * Real.pi * ξ * x) - 1) := by
    simp only [mul_sub, mul_one]
    rw [integral_sub hicos hi, hG.integral_one]
  rw [heq]
  calc
    _ ≤ ∫ x : ℝ, |G x * (Real.cos (2 * Real.pi * ξ * x) - 1)| :=
      by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x : ℝ => G x * (Real.cos (2 * Real.pi * ξ * x) - 1))
    _ ≤ ∫ x : ℝ, (8 * Real.pi ^ 2 * ξ ^ 2) * G x :=
      integral_mono_ae hidabs hib (Filter.Eventually.of_forall (weight_cos_error hG.supp hG.nonneg ξ))
    _ = 8 * Real.pi ^ 2 * ξ ^ 2 := by rw [integral_const_mul, hG.integral_one, mul_one]

end LeanLab.BhowmikGrimmelt2026
