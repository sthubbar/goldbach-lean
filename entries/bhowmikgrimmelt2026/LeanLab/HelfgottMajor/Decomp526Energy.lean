module

public import Mathlib
public import LeanLab.HelfgottMajor.Decomp503a
public import LeanLab.HelfgottMajor.LogMoment431

/-!
Existing energy supplies moved verbatim to remove their target import cycle.
Source P0014 pages 39 and 40 and display 4.42 on page 43.
The energy statements and the old Gaussian definition keep their exact text.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Decomp269a
open Real LeanLab.HelfgottArcs
/-- The Mellin transform F_delta used on page 43 in the proof of display 4.43. -/
noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end LeanLab.HelfgottMajor.Decomp269a

namespace LeanLab.HelfgottMajor.Decomp389b
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a
open FourierTransform
open scoped SchwartzMap Topology ContDiff ENNReal

/-- The positive parameter half line energy on the critical line, book page 434.
The sign parameter is used only at 1 and minus 1 in the sampling proof.
-/
noncomputable def lineEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-- The derivative energy above height 1 on either sign of the line, book page 434. -/
noncomputable def derivativeEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ),
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-! ### Mellin Plancherel on the critical line, for the Gaussian integrand

The two energy leaves below are the sharp forms of
`∫ t, ‖mellin f (1/2 + t I)‖ ^ 2 = 2 * π * ∫ x in Ioi 0, ‖f x‖ ^ 2`
for `f x = exp (-x^2 / 2) * e (δ x)`, respectively for `log • f`. -/

lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [e, Complex.norm_exp]
  have h : (2 * (π : ℂ) * Complex.I * (t : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- Pointwise norm of the Gaussian-character integrand. -/
lemma gauss_norm (δ : ℝ) (x : ℝ) :
    ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ = exp (-x ^ 2 / 2) := by
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma gauss_norm_sq (δ : ℝ) (x : ℝ) :
    ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2 = exp (-x ^ 2) := by
  rw [gauss_norm, sq, ← Real.exp_add]
  congr 1
  ring

/-- Pointwise norm of the log-coordinate integrand `f (exp u) * exp (u / 2)`. -/
lemma log_norm (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = exp (u / 2) * exp (-(exp u) ^ 2 / 2) := by
  rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma log_norm_sq (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = exp u * exp (-(exp u) ^ 2) := by
  rw [log_norm, mul_pow]
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

lemma log_le_exp_abs (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤ exp (-|u| / 2) := by
  rw [log_norm]
  rcases le_total u 0 with hu | hu
  · have h1 : exp (-(exp u) ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by have := sq_nonneg (exp u); linarith)
    have h2 : exp (u / 2) = exp (-|u| / 2) := by rw [abs_of_nonpos hu]; ring_nf
    rw [h2]
    exact mul_le_of_le_one_right (exp_pos _).le h1
  · have h1 : exp (u / 2) * exp (-(exp u) ^ 2 / 2) = exp (u / 2 - (exp u) ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1, abs_of_nonneg hu]
    refine Real.exp_le_exp.mpr ?_
    have he : 1 + 2 * u ≤ (exp u) ^ 2 := by
      have h := add_one_le_exp u
      have hp := exp_pos u
      nlinarith [sq_nonneg (exp u)]
    linarith

lemma integrable_exp_neg_abs_mul {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => exp (-c * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => exp (-c * u)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := c)
      (by norm_num) (by norm_num) hc
    simpa using h
  have h2 : IntegrableOn (fun u : ℝ => exp (c * u)) (Set.Iic 0) := by
    have h := h1.comp_neg
    rw [Set.neg_Ioi, neg_zero] at h
    have h' : IntegrableOn (fun u : ℝ => exp (c * u)) (Set.Iio 0) := by
      refine h.congr_fun ?_ measurableSet_Iio
      intro u _
      show exp (-c * -u) = exp (c * u)
      rw [neg_mul_neg]
    exact (integrableOn_Iic_iff_integrableOn_Iio (f := fun u : ℝ => exp (c * u))).mpr h'
  have h3 : IntegrableOn (fun u : ℝ => exp (-c * |u|)) (Set.Ioi 0) := by
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro u hu
    show exp (-c * u) = exp (-c * |u|)
    rw [abs_of_pos (Set.mem_Ioi.mp hu)]
  have h4 : IntegrableOn (fun u : ℝ => exp (-c * |u|)) (Set.Iic 0) := by
    refine h2.congr_fun ?_ measurableSet_Iic
    intro u hu
    show exp (c * u) = exp (-c * |u|)
    rw [abs_of_nonpos (Set.mem_Iic.mp hu), neg_mul_neg]
  have hu : Set.Ioi (0:ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
    exact lt_or_ge 0 x
  rw [← integrableOn_univ, ← hu]
  exact h3.union h4

lemma log_continuous (δ : ℝ) :
    Continuous (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) := by
  unfold e
  fun_prop

lemma log_integrable (δ : ℝ) :
    Integrable (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) := by
  refine Integrable.mono' (integrable_exp_neg_abs_mul (c := 1 / 2) (by norm_num))
    (log_continuous δ).aestronglyMeasurable ?_
  filter_upwards with u
  rw [show -(1 / 2 : ℝ) * |u| = -|u| / 2 by ring]
  exact log_le_exp_abs δ u

lemma log_memLp (δ : ℝ) :
    MemLp (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) 2 := by
  have hg : MemLp (fun u : ℝ => exp (-|u| / 2)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm
      (by fun_prop : Continuous (fun u : ℝ => exp (-|u| / 2))).aestronglyMeasurable]
    refine (integrable_exp_neg_abs_mul (c := 1) (by norm_num)).congr ?_
    filter_upwards with u
    have hp : (0:ℝ) < exp (-|u| / 2) := exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hp, sq, ← Real.exp_add]
    congr 1
    rw [show -(1:ℝ) * |u| = -|u| by ring]
    ring
  refine MemLp.mono' hg (log_continuous δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact log_le_exp_abs δ u

/-- `exp u` is positive, so on the critical line the complex power times the
change-of-variables factor is a single exponential. -/
lemma cpow_exp_mul (u t : ℝ) :
    ((exp u : ℝ) : ℂ) * (((exp u : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I) - 1))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) := by
  have hne : Complex.exp (u : ℂ) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero hne,
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), ← Complex.exp_add]
  congr 1
  ring

/-- The Mellin transform of the Gaussian-character integrand on the critical line is the
Fourier integral of its log coordinate transform. -/
theorem mellin_eq_fourier_gauss (δ : ℝ) (t : ℝ) :
    gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      = 𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(t / (2 * π))) := by
  rw [show gaussianMellin δ = mellin (fun x : ℝ => (exp (-x ^ 2 / 2) : ℂ) * e (δ * x)) from rfl,
    mellin, fourier_eq']
  rw [← Real.range_exp, ← Set.image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy)]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul, RCLike.real_smul_eq_coe_mul, smul_eq_mul, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), Complex.ofReal_exp]
  simp only [inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    abs_of_pos (exp_pos u)]
  have hL : ((exp u : ℝ) : ℂ) *
      (Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I) - 1)) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)) := by
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hR : Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
      (((exp (u / 2) : ℝ) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)) := by
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp only [← Complex.ofReal_exp]
  exact hL.trans hR.symm


/-! ### Plancherel for the Fourier integral on `L1 ∩ L2`

Ported from the lab's `LeanLab.ExceptionalSet.WindowParseval264` (which uses Mathlib only). -/

theorem wip_fourier_pairing (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, g x * 𝓕 f x =
      ∫ x : ℝ, g x * (𝓕 (h₂.toLp f) : Lp ℂ 2) x := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
    (by fun_prop) g.integrable h₁
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    exact flip_innerₗ ℝ
  rw [hflip] at hswap
  have hd := congrArg (fun d : 𝓢'(ℝ, ℂ) => d g)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x : ℝ, (𝓕 g) x * f x := by
      simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
        VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul] using hswap.symm
    _ = ∫ x : ℝ, (𝓕 g) x * (h₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := by simpa only [smul_eq_mul] using hd

theorem wip_fourierIntegral_ae_eq (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  simpa using wip_fourier_pairing f h₁ h₂ (hc'.toSchwartzMap hg')

theorem wip_integral_norm_sq_coe (u : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖u x‖ ^ 2 = ‖u‖ ^ 2 := by
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) u u)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    using hi.symm

theorem wip_integral_norm_sq_fourier (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    ∫ t : ℝ, ‖𝓕 f t‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [wip_fourierIntegral_ae_eq f h₁ h₂] with t ht
      rw [ht]
    _ = ‖𝓕 (h₂.toLp f)‖ ^ 2 := wip_integral_norm_sq_coe _
    _ = ‖h₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      rw [← wip_integral_norm_sq_coe]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

/-! ### The `L2` mass in log coordinates -/

lemma log_sq_integral (δ : ℝ) :
    ∫ u : ℝ, ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = Sec45.nTwo := by
  have hIoi : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2 = Sec45.nTwo := by
    have h : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2
        = ∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact gauss_norm_sq δ x
    rw [h, show (fun x : ℝ => exp (-x ^ 2)) = (fun x : ℝ => exp (-1 * x ^ 2)) from by
      funext x; ring_nf, integral_gaussian_Ioi]
    simp [Sec45.nTwo]
  have himg : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2
      = ∫ u : ℝ, exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 := by
    rw [← Real.range_exp, ← Set.image_univ]
    rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => Real.exp_injective hxy)]
    simp only [abs_of_pos (exp_pos _), setIntegral_univ]
  have hpt : ∀ u : ℝ,
      ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
        = exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 := by
    intro u
    rw [log_norm_sq, gauss_norm_sq, smul_eq_mul]
  rw [show (∫ u : ℝ,
      ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2)
      = ∫ u : ℝ, exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with u
    exact hpt u]
  rw [← himg, hIoi]

lemma integrable_fourier_sq (δ : ℝ) :
    Integrable (fun ξ : ℝ =>
      ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) ξ‖ ^ 2) := by
  have h2 := log_memLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (log_integrable δ) (log_memLp δ)] with ξ hξ
  rw [hξ]


lemma integrable_mellin_sq (δ : ℝ) :
    Integrable (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) ξ‖ ^ 2) hR).mpr (integrable_fourier_sq δ)
  refine h.congr ?_
  filter_upwards with t
  rw [mellin_eq_fourier_gauss δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

lemma fourier_sq_integral (δ : ℝ) :
    ∫ y : ℝ, ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) y‖ ^ 2 = Sec45.nTwo := by
  rw [wip_integral_norm_sq_fourier (fun u : ℝ => (exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (log_integrable δ) (log_memLp δ)]
  exact log_sq_integral δ

theorem integral_mellin_sq_gauss (δ : ℝ) :
    ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nTwo := by
  have hpt : ∀ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
    intro t
    rw [mellin_eq_fourier_gauss δ t]
    have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
    rw [harg]
  rw [show ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ∫ t : ℝ, ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with t
    exact hpt t]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) y‖ ^ 2)]
  rw [fourier_sq_integral δ]
  have hcoef : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_div, div_one, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [hcoef, smul_eq_mul]

/-- The two sign-split Mellin energies add up to `2 π` times the `L2` mass. -/
theorem line_integral_sum (δ : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2)
      + (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
      = 2 * π * Sec45.nTwo := by
  set F : ℝ → ℝ := fun t => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 with hF
  have h1 : (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ), F t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [one_mul]
    rw [hF]
  have himg : Neg.neg '' (Set.Ioi (0:ℝ)) = Set.Iio (0:ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨y, hy, rfl⟩; linarith
    · intro hx; exact ⟨-x, by linarith, by ring⟩
  have hsub : ∫ t in Set.Ioi (0 : ℝ), F (-t) = ∫ t in Set.Iio (0 : ℝ), F t := by
    rw [← himg]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
      (fun x _ y _ hxy => neg_injective hxy)]
    simp
  have h2 : (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Iic (0 : ℝ), F t := by
    rw [show (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
        = ∫ t in Set.Ioi (0 : ℝ), F (-t) from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [neg_one_mul]
      rw [hF]]
    rw [hsub, integral_Iic_eq_integral_Iio]
  have hInt : Integrable F := integrable_mellin_sq δ
  rw [h1, h2]
  rw [← Set.compl_Ioi (a := (0:ℝ))]
  rw [integral_add_compl measurableSet_Ioi hInt]
  exact integral_mellin_sq_gauss δ

lemma nTwo_pos : 0 < Sec45.nTwo := by
  rw [Sec45.nTwo]; positivity

/-- The square-root splitting, with the total mass supplied as a hypothesis. -/
lemma sqrt_add_sqrt_le_of_sum {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B = 2 * π * Sec45.nTwo) :
    sqrt A + sqrt B ≤ 2 * sqrt π * sqrt Sec45.nTwo := by
  have hsA : sqrt A ^ 2 = A := sq_sqrt hA
  have hsB : sqrt B ^ 2 = B := sq_sqrt hB
  have hsπ : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  have hsN : sqrt Sec45.nTwo ^ 2 = Sec45.nTwo := sq_sqrt nTwo_pos.le
  have hsq : (sqrt A + sqrt B) ^ 2 = A + B + 2 * (sqrt A * sqrt B) := by
    rw [sq]; linarith
  have hprod : 2 * (sqrt A * sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (sqrt A - sqrt B)]
  have hR : (2 * sqrt π * sqrt Sec45.nTwo) ^ 2 = 4 * π * Sec45.nTwo := by
    nlinarith [hsπ, hsN]
  have hkey : (sqrt A + sqrt B) ^ 2 ≤ (2 * sqrt π * sqrt Sec45.nTwo) ^ 2 := by
    rw [hsq, hR]; linarith
  have h0 : 0 ≤ sqrt A + sqrt B := by positivity
  have h2 : 0 ≤ 2 * sqrt π * sqrt Sec45.nTwo := by positivity
  nlinarith [hkey, h0, h2, sq_nonneg (sqrt A + sqrt B - 2 * sqrt π * sqrt Sec45.nTwo),
    mul_nonneg h0 h2]


/-- LEAF. Book page 434, the first Plancherel estimate after display 16.26.
The Gaussian square moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_line_energy_bound (δ : ℝ) :
    sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo := by
  have hsum := line_integral_sum δ
  have h1 : lineEnergy δ 1 = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  have h2 : lineEnergy δ (-1) = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  rw [h1, h2]
  exact sqrt_add_sqrt_le_of_sum (by positivity) (by positivity) hsum

open Filter Asymptotics

/-- The Gaussian-character integrand of `gaussianMellin`, as a function of one variable. -/
private lemma gauss_cont (δ : ℝ) :
    Continuous (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) := by
  unfold e
  fun_prop

/-- Super-polynomial decay of the Gaussian at infinity. -/
private lemma gauss_isBigO_top (δ : ℝ) :
    (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) =O[Filter.atTop]
      (fun x : ℝ => x ^ (-(1 : ℝ))) := by
  have h1 : (fun x : ℝ => Real.exp (-x ^ 2 / 2)) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-x)) := by
    refine (exp_neg_mul_sq_isLittleO_exp_neg (b := 1 / 2) (by norm_num)).congr' ?_ ?_
    · filter_upwards with x
      congr 1
      ring
    · filter_upwards with x
      rfl
  have h2 : (fun x : ℝ => Real.exp (-x)) =o[Filter.atTop] (fun x : ℝ => x ^ (-(1 : ℝ))) := by
    simpa only [one_mul, neg_mul] using
      isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-1)
  have h3 := (h1.trans h2).isBigO
  rw [← isBigO_norm_left]
  refine h3.congr' (Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => rfl)
  exact (gauss_norm δ x).symm

/-- Boundedness of the Gaussian-character integrand at the origin. -/
private lemma gauss_isBigO_bot (δ : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hmem : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio 1))
  filter_upwards [hmem, self_mem_nhdsWithin] with x hx1 hx
  simp only [gauss_norm, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx (-b)),
    one_mul]
  refine le_trans (Real.exp_le_one_iff.mpr ?_)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx (le_of_lt hx1) (by linarith))
  have := sq_nonneg x
  nlinarith

/-- Differentiation under the Mellin integral for the Gaussian-character integrand. -/
private lemma gauss_mellin_hasDerivAt (δ : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasDerivAt (gaussianMellin δ)
      (mellin (fun x : ℝ => (Real.log x : ℂ) * ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) s) s := by
  have hfc : LocallyIntegrableOn (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
      (Set.Ioi 0) :=
    (gauss_cont δ).locallyIntegrable.locallyIntegrableOn _
  exact (mellin_hasDerivAt_of_isBigO_rpow hfc (gauss_isBigO_top δ) hs1
    (gauss_isBigO_bot δ (by linarith : (0:ℝ) < s.re / 2)) (by linarith)).2

/-- The log-coordinate profile of the derivative of the Gaussian Mellin transform. -/
private lemma weighted_cont (δ : ℝ) :
    Continuous (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  unfold e
  fun_prop

/-- The Mellin transform of the log-weighted Gaussian-character integrand on the critical line is
the Fourier integral of its log-coordinate transform. -/
private lemma mellin_log_eq_fourier (δ t : ℝ) :
    mellin (fun x : ℝ => (Real.log x : ℂ) * ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
        ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      = 𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(t / (2 * π))) := by
  rw [mellin, fourier_eq']
  rw [← Real.range_exp, ← Set.image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy)]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul, RCLike.real_smul_eq_coe_mul, smul_eq_mul, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), Complex.ofReal_exp, Real.log_exp]
  simp only [inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    abs_of_pos (exp_pos u)]
  set G : ℂ := (exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u) with hGdef
  set s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I with hsdef
  have hL : ((exp u : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * (s - 1)) * G)
      = Complex.exp ((u : ℂ) * s) * G := by
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hR : Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
      (((exp (u / 2) : ℝ) : ℂ) * G)
      = Complex.exp ((u : ℂ) * s) * G := by
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp only [← Complex.ofReal_exp]
  calc ((exp u : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * (s - 1)) * ((u : ℂ) * G))
      = (u : ℂ) * (((exp u : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * (s - 1)) * G)) := by ring
    _ = (u : ℂ) * (Complex.exp ((u : ℂ) * s) * G) := by rw [hL]
    _ = (u : ℂ) * (Complex.exp ((-2 : ℂ) * (π : ℂ) *
          ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) * (((exp (u / 2) : ℝ) : ℂ) * G)) := by
        rw [hR]
    _ = Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
          ((u : ℂ) * (((exp (u / 2) : ℝ) : ℂ) * G)) := by ring

/-- Pointwise norm of the log-coordinate derivative profile. -/
private lemma weighted_norm (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = |u| * (exp (u / 2) * exp (-(exp u) ^ 2 / 2)) := by
  rw [norm_mul, log_norm, Complex.norm_real, Real.norm_eq_abs]

/-- Pointwise square norm of the log-coordinate derivative profile. -/
private lemma weighted_norm_sq (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = u ^ 2 * (exp u * exp (-(exp u) ^ 2)) := by
  rw [weighted_norm, mul_pow, mul_pow, sq_abs]
  congr 1
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

/-- The log-coordinate derivative profile is dominated by a decaying exponential. -/
private lemma weighted_le (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤
      4 * exp (-(1 / 4 : ℝ) * |u|) := by
  rw [weighted_norm]
  have h1 : exp (u / 2) * exp (-(exp u) ^ 2 / 2) ≤ exp (-|u| / 2) := by
    rw [← log_norm]
    exact log_le_exp_abs δ u
  refine (mul_le_mul_of_nonneg_left h1 (abs_nonneg u)).trans ?_
  have hexp : 1 + |u| / 4 ≤ exp (|u| / 4) := by
    linarith [Real.add_one_le_exp (|u| / 4)]
  have hkey : |u| * exp (-|u| / 4) ≤ 4 := by
    have hp := exp_pos (-|u| / 4)
    have h4 : (1 + |u| / 4) * exp (-|u| / 4) ≤ 1 := by
      have h5 := mul_le_mul_of_nonneg_right hexp (le_of_lt hp)
      rw [← Real.exp_add, show |u| / 4 + -|u| / 4 = 0 by ring, Real.exp_zero] at h5
      exact h5
    nlinarith [h4, hp, abs_nonneg u]
  have hmul : exp (-|u| / 2) = exp (-|u| / 4) * exp (-|u| / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hp := exp_pos (-|u| / 4)
  rw [hmul, show -(1 / 4 : ℝ) * |u| = -|u| / 4 by ring]
  nlinarith [hkey, hp]

/-- The log-coordinate derivative profile is integrable. -/
private lemma weighted_integrable (δ : ℝ) :
    Integrable (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  refine Integrable.mono' ((integrable_exp_neg_abs_mul (c := 1 / 4) (by norm_num)).const_mul 4)
    (weighted_cont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact weighted_le δ u

/-- The log-coordinate derivative profile lies in `L2`. -/
private lemma weighted_memLp (δ : ℝ) :
    MemLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) 2 := by
  have hcont : Continuous (fun u : ℝ => 4 * exp (-(1 / 4 : ℝ) * |u|)) := by fun_prop
  have hg : MemLp (fun u : ℝ => 4 * exp (-(1 / 4 : ℝ) * |u|)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    have heq : (fun u : ℝ => ‖4 * exp (-(1 / 4 : ℝ) * |u|)‖ ^ 2)
        = fun u : ℝ => 16 * exp (-(1 / 2 : ℝ) * |u|) := by
      funext u
      have hp : (0:ℝ) < 4 * exp (-(1 / 4 : ℝ) * |u|) := by positivity
      rw [Real.norm_eq_abs, abs_of_pos hp, mul_pow, show (4:ℝ) ^ 2 = 16 by norm_num,
        show exp (-(1 / 4 : ℝ) * |u|) ^ 2 = exp (-(1 / 2 : ℝ) * |u|) by
          rw [sq, ← Real.exp_add]; congr 1; ring]
    rw [heq]
    exact (integrable_exp_neg_abs_mul (c := 1 / 2) (by norm_num)).const_mul 16
  refine MemLp.mono' hg (weighted_cont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact weighted_le δ u

/-- The `L2` mass of the log-coordinate derivative profile is the log squared Gaussian moment. -/
private lemma weighted_sq_integral (δ : ℝ) :
    ∫ u : ℝ, ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2 = Sec45.nLog := by
  have himg : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2) * Real.log x ^ 2
      = ∫ u : ℝ, exp u • (Real.exp (-(exp u) ^ 2) * Real.log (exp u) ^ 2) := by
    rw [← Real.range_exp, ← Set.image_univ]
    rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => Real.exp_injective hxy)]
    simp only [abs_of_pos (exp_pos _), setIntegral_univ]
  rw [show (∫ u : ℝ, ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2)
      = ∫ u : ℝ, exp u • (Real.exp (-(exp u) ^ 2) * Real.log (exp u) ^ 2) from by
    apply integral_congr_ae
    filter_upwards with u
    rw [weighted_norm_sq, Real.log_exp, smul_eq_mul]
    ring]
  rw [← himg]
  exact LeanLab.HelfgottMajor.LogMoment431.gaussian_log_square_integral

/-- The Fourier profile of the derivative has integrable square. -/
private lemma integrable_fourier_sq_weighted (δ : ℝ) :
    Integrable (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) := by
  have h2 := weighted_memLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (weighted_integrable δ)
    (weighted_memLp δ)] with ξ hξ
  rw [hξ]

/-- The Fourier side square integral of the derivative profile. -/
private lemma fourier_sq_integral_weighted (δ : ℝ) :
    ∫ y : ℝ, ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) y‖ ^ 2 = Sec45.nLog := by
  rw [wip_integral_norm_sq_fourier (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (weighted_integrable δ) (weighted_memLp δ)]
  exact weighted_sq_integral δ

/-- The pointwise critical-line identity for the derivative. -/
private lemma deriv_mellin_sq_pointwise (δ t : ℝ) :
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
  have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  rw [(gauss_mellin_hasDerivAt δ (s := (1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      (by rw [hre]; norm_num) (by rw [hre]; norm_num)).deriv, mellin_log_eq_fourier δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

/-- The derivative of the Gaussian Mellin transform has integrable square on the critical line. -/
private lemma integrable_deriv_mellin_sq (δ : ℝ) :
    Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) *
      ((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) hR).mpr
      (integrable_fourier_sq_weighted δ)
  refine h.congr ?_
  filter_upwards with t
  exact (deriv_mellin_sq_pointwise δ t).symm

/-- Differentiated Mellin Plancherel on the whole critical line. -/
private lemma integral_deriv_mellin_sq (δ : ℝ) :
    ∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nLog := by
  rw [show (∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with t
    exact deriv_mellin_sq_pointwise δ t]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) *
    ((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) y‖ ^ 2)]
  rw [fourier_sq_integral_weighted δ]
  have hcoef : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_div, div_one, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [hcoef, smul_eq_mul]

/-- The square-root splitting with an upper bound on the total mass. -/
private lemma sqrt_add_sqrt_le_of_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B ≤ 2 * π * Sec45.nLog) :
    sqrt A + sqrt B ≤ 2 * sqrt π * sqrt Sec45.nLog := by
  have hsA : sqrt A ^ 2 = A := sq_sqrt hA
  have hsB : sqrt B ^ 2 = B := sq_sqrt hB
  have hsπ : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  have hsN : sqrt Sec45.nLog ^ 2 = Sec45.nLog := sq_sqrt Sec45.nLog_nonneg
  have hsq : (sqrt A + sqrt B) ^ 2 = A + B + 2 * (sqrt A * sqrt B) := by
    rw [sq]; linarith
  have hprod : 2 * (sqrt A * sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (sqrt A - sqrt B)]
  have hR : (2 * sqrt π * sqrt Sec45.nLog) ^ 2 = 4 * π * Sec45.nLog := by
    nlinarith [hsπ, hsN]
  have hkey : (sqrt A + sqrt B) ^ 2 ≤ (2 * sqrt π * sqrt Sec45.nLog) ^ 2 := by
    rw [hsq, hR]; linarith
  have h0 : 0 ≤ sqrt A + sqrt B := by positivity
  have h2 : 0 ≤ 2 * sqrt π * sqrt Sec45.nLog := by positivity
  nlinarith [hkey, h0, h2, sq_nonneg (sqrt A + sqrt B - 2 * sqrt π * sqrt Sec45.nLog),
    mul_nonneg h0 h2]

/-- LEAF. Book page 434, the differentiated Mellin Plancherel estimate.
The Gaussian log squared moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_derivative_energy_bound (δ : ℝ) :
    sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog := by
  have hA : derivativeEnergy δ 1 = ∫ t in Set.Ioi (1 : ℝ),
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [one_mul]
  have himg : Neg.neg '' (Set.Ioi (1 : ℝ)) = Set.Iio (-1 : ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨y, hy, rfl⟩; linarith
    · intro hx; exact ⟨-x, by linarith, by ring⟩
  have hsub : ∫ t in Set.Ioi (1 : ℝ),
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t) : ℝ) * Complex.I)‖ ^ 2
      = ∫ t in Set.Iio (-1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [← himg]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
      (fun x _ y _ hxy => neg_injective hxy)]
    simp
  have hB : derivativeEnergy δ (-1) = ∫ t in Set.Iio (-1 : ℝ),
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [show derivativeEnergy δ (-1) = ∫ t in Set.Ioi (1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t) : ℝ) * Complex.I)‖ ^ 2 from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [neg_one_mul]]
    exact hsub
  have hInt : Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
    integrable_deriv_mellin_sq δ
  have hsplit : (∫ t in Set.Ioi (1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      + (∫ t in (Set.Ioi (1 : ℝ))ᶜ,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 :=
    integral_add_compl (μ := volume) measurableSet_Ioi hInt
  rw [Set.compl_Ioi] at hsplit
  have hmono : ∫ t in Set.Iio (-1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      ≤ ∫ t in Set.Iic (1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    refine setIntegral_mono_set hInt.integrableOn ?_ ?_
    · filter_upwards with t using (by positivity)
    · filter_upwards with t ht
      simp only [Set.mem_Iio, Set.mem_Iic] at ht ⊢
      linarith
  have hFint : ∫ t : ℝ,
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nLog := integral_deriv_mellin_sq δ
  have hsum : derivativeEnergy δ 1 + derivativeEnergy δ (-1) ≤ 2 * π * Sec45.nLog := by
    calc derivativeEnergy δ 1 + derivativeEnergy δ (-1)
        = (∫ t in Set.Ioi (1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
          + (∫ t in Set.Iio (-1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
          rw [hA, hB]
      _ ≤ (∫ t in Set.Ioi (1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
          + (∫ t in Set.Iic (1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
          add_le_add (le_refl _) hmono
      _ = ∫ t : ℝ,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := hsplit
      _ = 2 * π * Sec45.nLog := hFint
  have hAnn : 0 ≤ derivativeEnergy δ 1 := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Ioi (fun t _ => by positivity)
  have hBnn : 0 ≤ derivativeEnergy δ (-1) := by
    rw [hB]
    exact setIntegral_nonneg measurableSet_Iio (fun t _ => by positivity)
  exact sqrt_add_sqrt_le_of_le hAnn hBnn hsum

end LeanLab.HelfgottMajor.Decomp389b

namespace LeanLab.HelfgottMajor.Sampling431
open Real MeasureTheory Set Filter
open scoped Topology

/-- The scalar antiderivative used for both squared logarithmic weights on book page 434.
This checks only the elementary calculus in the sampling proof.
-/
theorem hasDerivAt_log_weight_primitive (a b q t : ℝ) (hq : 0 < q) (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => u * ((a * log (q * u) + b) ^ 2 -
        2 * a * (a * log (q * u) + b) + 2 * a ^ 2))
      ((a * log (q * t) + b) ^ 2) t := by
  have hl := (Real.hasDerivAt_log (mul_ne_zero hq.ne' ht.ne')).comp t
    ((hasDerivAt_id t).const_mul q)
  have hw := (hl.const_mul a).add_const b
  have hp := (hasDerivAt_id t).mul
    (((hw.pow 2).sub (hw.const_mul (2 * a))).add_const (2 * a ^ 2))
  convert hp using 1
  · rfl
  · simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ; ring

/-- Exact integral of the squared logarithmic weight from height 1 to T.
Source book page 434, the two elementary weight integrals in the sampling proof.
-/
theorem integral_log_weight_sq (a b q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, (a * log (q * t) + b) ^ 2) =
      T * ((a * log (q * T) + b) ^ 2 - 2 * a * (a * log (q * T) + b) + 2 * a ^ 2) -
      ((a * log q + b) ^ 2 - 2 * a * (a * log q + b) + 2 * a ^ 2) := by
  have hc : ContinuousOn (fun t : ℝ => (a * log (q * t) + b) ^ 2) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_log_weight_primitive a b q t hq
      (lt_of_lt_of_le zero_lt_one ((uIcc_of_le hT ▸ ht).1))) hc.intervalIntegrable
  simpa only [one_mul, mul_one] using hh

/-- Dropping the nonnegative lower endpoint gives the squared weight budget.
Source book page 434 before the square root estimates.
-/
theorem integral_log_weight_sq_le (a b q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, (a * log (q * t) + b) ^ 2) ≤
      T * ((a * log (q * T) + b - a) ^ 2 + a ^ 2) := by
  rw [integral_log_weight_sq a b q T hq hT]
  nlinarith [sq_nonneg (a * log q + b - a), sq_nonneg a]

/-- The finite error envelope root has the coefficient 3.242 printed on book page 434.
This is only the scalar weight bound. It uses no zero count or Mellin value.
-/
theorem error_weight_root_bound (q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ q * T) :
    sqrt (∫ t in (1 : ℝ)..T, (0.15 * log (q * t) + 3.389) ^ 2) ≤
      (0.15 * log (q * T) + 3.242) * sqrt T := by
  have hT0 : 0 ≤ T := by linarith
  have hl := log_le_log (by positivity : (0 : ℝ) < 2 * π * exp 2) hlarge
  rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 2), log_exp] at hl
  have hlog : (3.5 : ℝ) ≤ log (q * T) := by linarith [log_two_pi_gt]
  have hcoef : (0.15 * log (q * T) + 3.389 - 0.15) ^ 2 + 0.15 ^ 2 ≤
      (0.15 * log (q * T) + 3.242) ^ 2 := by nlinarith
  have hbudget := (integral_log_weight_sq_le 0.15 3.389 q T hq hT).trans
    (mul_le_mul_of_nonneg_left hcoef hT0)
  apply (sqrt_le_iff).mpr
  refine ⟨mul_nonneg (by linarith) (sqrt_nonneg T), ?_⟩
  simpa only [mul_pow, sq_sqrt hT0, mul_comm] using hbudget

/-- The main logarithmic weight has the shifted logarithm budget on book page 434.
This is the scalar square root estimate before display 16.26.
-/
theorem main_weight_root_bound (q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ q * T) :
    sqrt (∫ t in (1 : ℝ)..T, log (q * t / (2 * π)) ^ 2) ≤
      sqrt T * log (q * T / (2 * π * sqrt (exp 1))) := by
  have hT0 : 0 ≤ T := by linarith
  have hqT0 : 0 < q * T := mul_pos hq (by linarith)
  have hl := log_le_log (by positivity : (0 : ℝ) < 2 * π * exp 2) hlarge
  rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 2), log_exp] at hl
  have hL : (2 : ℝ) ≤ log (q * T) - log (2 * π) := by linarith
  have hshift : log (q * T / (2 * π * sqrt (exp 1))) =
      log (q * T) - log (2 * π) - 1 / 2 := by
    rw [log_div hqT0.ne' (by positivity),
      log_mul (by positivity : (2 * π : ℝ) ≠ 0) (by positivity : sqrt (exp 1) ≠ 0),
      log_sqrt (exp_pos 1).le, log_exp]
    ring
  have heq : (∫ t in (1 : ℝ)..T, log (q * t / (2 * π)) ^ 2) =
      ∫ t in (1 : ℝ)..T, (1 * log (q * t) + -log (2 * π)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    dsimp only
    rw [log_div (mul_ne_zero hq.ne' (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
      (by positivity)]
    ring
  have hcoef : (1 * log (q * T) + -log (2 * π) - 1) ^ 2 + 1 ^ 2 ≤
      (log (q * T) - log (2 * π) - 1 / 2) ^ 2 := by nlinarith
  have hbudget := (integral_log_weight_sq_le 1 (-log (2 * π)) q T hq hT).trans
    (mul_le_mul_of_nonneg_left hcoef hT0)
  rw [heq, hshift]
  apply (sqrt_le_iff).mpr
  refine ⟨mul_nonneg (sqrt_nonneg T) (by linarith), ?_⟩
  simpa only [mul_pow, sq_sqrt hT0] using hbudget

end LeanLab.HelfgottMajor.Sampling431
namespace LeanLab.HelfgottMajor.Decomp389b
open Real LeanLab.HelfgottArcs Decomp269a

/-- Analytic regularity on the open unit strip for the sampling integrals.
P0014 page 39 display 4.31, obtained from the existing Mellin differentiation proof. -/
theorem gaussian_mellin_analyticAt (δ : ℝ) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    AnalyticAt ℂ (gaussianMellin δ) s := by
  have hd : DifferentiableOn ℂ (gaussianMellin δ) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    exact (gauss_mellin_hasDerivAt δ hz.1 hz.2).differentiableAt.differentiableWithinAt
  exact (hd.analyticOnNhd ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const))) s ⟨h0, h1⟩

end LeanLab.HelfgottMajor.Decomp389b

namespace LeanLab.HelfgottMajor.Decomp389b
open Real MeasureTheory Decomp269a

/-- Full line derivative integrability from the existing differentiated Plancherel proof.
P0014 page 40 and display 4.42 on page 43. -/
theorem gaussian_derivative_sq_integrable (δ : ℝ) :
    Integrable (fun t : ℝ => ‖deriv (gaussianMellin δ)
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  exact integrable_deriv_mellin_sq δ

end LeanLab.HelfgottMajor.Decomp389b
