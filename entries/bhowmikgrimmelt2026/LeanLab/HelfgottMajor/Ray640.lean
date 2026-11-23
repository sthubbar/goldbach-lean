module

public import LeanLab.HelfgottMajor.Gamma503
public import Mathlib

/-!
P0014 page 26 before display 3.66.
Logarithmic coordinates for rotation of a Gaussian Mellin ray.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Ray640
open Real MeasureTheory Filter Set
open scoped Topology

/-- The Mellin differential after the holomorphic substitution u equal to exp z.
P0014 page 26 before display 3.66. -/
noncomputable def logKernel (δ : ℝ) (s z : ℂ) : ℂ :=
  Complex.exp (s * z - Complex.exp (2 * z) / 2 +
    (2 * (π : ℂ) * Complex.I * δ) * Complex.exp z)

/-- LEAF: The logarithmic Mellin differential is entire.
P0014 page 26 before display 3.66. This removes the power branch from Cauchy theory. -/
theorem logKernel_differentiable (δ : ℝ) (s : ℂ) :
    Differentiable ℂ (logKernel δ s) := by
  unfold logKernel
  fun_prop

/-- LEAF: Finite ray rotation with the two circular boundary terms retained.
P0014 page 26 before display 3.66. The real coordinates are logarithmic radii. -/
theorem logarithmic_rectangle (δ θ a b : ℝ) (s : ℂ) :
    (∫ x : ℝ in a..b, logKernel δ s x) -
      (∫ x : ℝ in a..b, logKernel δ s (x + (θ : ℂ) * Complex.I)) =
      Complex.I * (∫ y : ℝ in 0..θ, logKernel δ s (a + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in 0..θ, logKernel δ s (b + (y : ℂ) * Complex.I)) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (logKernel δ s) (a : ℂ) ((b : ℂ) + (θ : ℂ) * Complex.I)
    (logKernel_differentiable δ s).differentiableOn
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_zero, mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_mul, smul_eq_mul] at h
  linear_combination h

/-- LEAF: Exact modulus on every intermediate ray.
P0014 page 26 before display 3.66. The radial Jacobian is included. -/
theorem logKernel_norm (δ x φ : ℝ) (s : ℂ) :
    ‖logKernel δ s (x + (φ : ℂ) * Complex.I)‖ =
      exp (s.re * x - s.im * φ - exp (2 * x) * cos (2 * φ) / 2 -
        2 * π * δ * exp x * sin φ) := by
  simp [logKernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im]
  congr 1
  ring

/-- LEAF: Uniform Gaussian domination on the closed angular sector.
P0014 page 26 before display 3.66. Both the height and twist give damping. -/
theorem logKernel_sector_majorant (δ θ x φ : ℝ) (s : ℂ)
    (hδ : 0 ≤ δ) (ht : 0 ≤ s.im) (hθ0 : 0 ≤ θ) (hθ1 : θ < π / 4)
    (hφ : φ ∈ Icc 0 θ) :
    ‖logKernel δ s (x + (φ : ℂ) * Complex.I)‖ ≤
      exp (s.re * x) * exp (-((cos (2 * θ) / 2) * (exp x) ^ 2)) := by
  rw [logKernel_norm, ← exp_add]
  apply exp_le_exp.mpr
  have hc : cos (2 * θ) ≤ cos (2 * φ) :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith [hφ.1])
      (by linarith [pi_pos]) (by linarith [hφ.2])
  have hp : 0 ≤ s.im * φ := mul_nonneg ht hφ.1
  have hd : 0 ≤ 2 * π * δ * exp x * sin φ := by
    apply mul_nonneg (by positivity)
    exact sin_nonneg_of_nonneg_of_le_pi hφ.1 (by linarith [hφ.2, pi_pos])
  have he : exp (2 * x) = (exp x) ^ 2 := by rw [two_mul, exp_add, pow_two]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (exp x))]

/-- LEAF: The outer circular arc tends to zero.
P0014 page 26 before display 3.66. Its radius is exp x as x tends to infinity. -/
theorem outer_arc_decay (δ θ : ℝ) (s : ℂ)
    (hδ : 0 ≤ δ) (ht : 0 ≤ s.im) (hθ0 : 0 ≤ θ) (hθ1 : θ < π / 4) :
    Tendsto (fun x : ℝ => ∫ φ : ℝ in 0..θ,
      logKernel δ s (x + (φ : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hc : 0 < cos (2 * θ) / 2 := by
    have := cos_pos_of_mem_Ioo (x := 2 * θ) ⟨by linarith [pi_pos], by linarith⟩
    positivity
  have he : Tendsto (fun t : ℝ => exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
  have hg := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hc s.re).tendsto_zero_of_tendsto he
  have hg' : Tendsto (fun x : ℝ =>
      exp (s.re * x) * exp (-((cos (2 * θ) / 2) * (exp x) ^ 2))) atTop (𝓝 0) := by
    convert hg.comp Real.tendsto_exp_atTop using 1
    funext x
    dsimp only [Function.comp_def]
    rw [← Real.exp_mul]
    congr 2 <;> ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun x => norm_nonneg _) _
    (by simpa using hg'.const_mul θ)
  intro x
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := θ) (C := exp (s.re * x) *
      exp (-((cos (2 * θ) / 2) * (exp x) ^ 2)))
    (fun φ hφ => logKernel_sector_majorant δ θ x φ s hδ ht hθ0 hθ1
      ⟨(uIoc_of_le hθ0 ▸ hφ).1.le, (uIoc_of_le hθ0 ▸ hφ).2⟩)
  simpa [abs_of_nonneg hθ0, mul_comm] using hh

/-- LEAF: The inner circular arc tends to zero for positive real part.
P0014 page 26 before display 3.66. Its radius is exp x as x tends to minus infinity. -/
theorem inner_arc_decay (δ θ : ℝ) (s : ℂ) (hσ : 0 < s.re)
    (hδ : 0 ≤ δ) (ht : 0 ≤ s.im) (hθ0 : 0 ≤ θ) (hθ1 : θ < π / 4) :
    Tendsto (fun x : ℝ => ∫ φ : ℝ in 0..θ,
      logKernel δ s (x + (φ : ℂ) * Complex.I)) atBot (𝓝 0) := by
  have hc : 0 ≤ cos (2 * θ) / 2 := by
    have := cos_pos_of_mem_Ioo (x := 2 * θ) ⟨by linarith [pi_pos], by linarith⟩
    positivity
  have he : Tendsto (fun x : ℝ => exp (s.re * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atBot hσ tendsto_id)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun x => norm_nonneg _) _ (by simpa using he.const_mul θ)
  intro x
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := θ) (C := exp (s.re * x)) (fun φ hφ => by
      calc
        ‖logKernel δ s (x + (φ : ℂ) * Complex.I)‖ ≤
          exp (s.re * x) * exp (-((cos (2 * θ) / 2) * (exp x) ^ 2)) :=
            logKernel_sector_majorant δ θ x φ s hδ ht hθ0 hθ1
              ⟨(uIoc_of_le hθ0 ▸ hφ).1.le, (uIoc_of_le hθ0 ▸ hφ).2⟩
        _ ≤ exp (s.re * x) := mul_le_of_le_one_right (exp_nonneg _)
          (exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc (sq_nonneg _)))))
  simpa [abs_of_nonneg hθ0, mul_comm] using hh

/-- LEAF: Passing to the two infinite rays in the finite rectangle identity.
P0014 page 26 before display 3.66. Both horizontal integrals are absolutely convergent. -/
theorem logarithmic_rotation (δ θ : ℝ) (s : ℂ) (hσ : 0 < s.re)
    (hδ : 0 ≤ δ) (ht : 0 ≤ s.im) (hθ0 : 0 ≤ θ) (hθ1 : θ < π / 4)
    (hreal : Integrable (fun x : ℝ => logKernel δ s x))
    (hrotated : Integrable (fun x : ℝ => logKernel δ s (x + (θ : ℂ) * Complex.I))) :
    (∫ x : ℝ, logKernel δ s x) =
      ∫ x : ℝ, logKernel δ s (x + (θ : ℂ) * Complex.I) := by
  have hl := (intervalIntegral_tendsto_integral hreal tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral hrotated tendsto_neg_atTop_atBot tendsto_id)
  have hr := (((inner_arc_decay δ θ s hσ hδ ht hθ0 hθ1).comp
    tendsto_neg_atTop_atBot).const_mul Complex.I).sub
    ((outer_arc_decay δ θ s hδ ht hθ0 hθ1).const_mul Complex.I)
  have heq : (fun R : ℝ =>
      (∫ x : ℝ in -R..R, logKernel δ s x) -
        (∫ x : ℝ in -R..R, logKernel δ s (x + (θ : ℂ) * Complex.I))) =
      (fun R : ℝ => Complex.I *
        (∫ y : ℝ in 0..θ, logKernel δ s (-R + (y : ℂ) * Complex.I)) -
          Complex.I * (∫ y : ℝ in 0..θ, logKernel δ s (R + (y : ℂ) * Complex.I))) := by
    funext R
    simpa only [Complex.ofReal_neg] using logarithmic_rectangle δ θ (-R) R s
  simp only [Function.comp_def, Complex.ofReal_neg] at hr
  rw [← heq] at hr
  have hh := tendsto_nhds_unique hl hr
  simpa only [mul_zero, sub_zero, sub_eq_zero] using hh

/-- LEAF: The exponential substitution including the Mellin power and the ray Jacobian.
P0014 page 26 before display 3.66. Only the positive real power is used. -/
theorem logarithmic_ray_pullback (δ θ x : ℝ) (s : ℂ) :
    logKernel δ s (x + (θ : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I * s) *
        ((exp x : ℝ) : ℂ) *
          ((((exp x : ℝ) : ℂ) ^ (s - 1)) * Complex.exp
            (((-(exp x) ^ 2 / 2 : ℝ) : ℂ) *
                Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) +
              ((2 * π * δ * exp x : ℝ) : ℂ) * Complex.I *
                Complex.exp ((θ : ℂ) * Complex.I))) := by
  have hp : ((exp x : ℝ) : ℂ) ^ (s - 1) = Complex.exp ((x : ℂ) * (s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (exp_pos x).ne'),
      ← Complex.ofReal_log (exp_pos x).le, log_exp]
  rw [hp]
  unfold logKernel
  push_cast
  rw [Complex.exp_add, show (2 : ℂ) * ((x : ℂ) + (θ : ℂ) * Complex.I) =
    2 * (x : ℂ) + ((2 : ℂ) * θ) * Complex.I by ring, Complex.exp_add]
  rw [show Complex.exp (2 * (x : ℂ)) = (Complex.exp (x : ℂ)) ^ 2 by
    rw [two_mul, Complex.exp_add, pow_two]]
  simp only [← Complex.ofReal_exp]
  rw [Complex.ofReal_exp x]
  repeat rw [← Complex.exp_add]
  congr 1
  rw [Complex.exp_add]
  ring

/-- LEAF: The real logarithmic ray is the original Mellin integrand with its Jacobian.
P0014 page 26 before display 3.66, using the Gaussian transform of Section 2.3. -/
theorem logarithmic_real_pullback (δ x : ℝ) (s : ℂ) :
    logKernel δ s x = exp x •
      ((((exp x : ℝ) : ℂ) ^ (s - 1)) •
        ((exp (-(exp x) ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * exp x))) := by
  have h := logarithmic_ray_pullback δ 0 x s
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one, one_mul, add_zero] at h
  rw [h]
  simp only [Complex.real_smul, smul_eq_mul, mul_assoc]
  congr 2
  unfold LeanLab.HelfgottArcs.e
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end LeanLab.HelfgottMajor.Ray640
