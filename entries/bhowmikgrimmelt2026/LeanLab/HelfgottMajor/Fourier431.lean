module

public import Mathlib.Analysis.Fourier.LpSpace

/-!
The integral Fourier transform and the L2 isometry used on book Part IV page 434.
This helper supplies the compatibility step after the logarithmic substitution.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Fourier431
open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff

/-- The integral Fourier transform agrees almost everywhere with the L2 transform.
This is the Plancherel compatibility step used on book page 434.
-/
theorem fourierIntegral_ae_eq_L2 {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp (α := ℝ) ℂ 2 volume) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num))
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (by simp : Complex.ofReal (0 : ℝ) = 0)).toSchwartzMap
    (by fun_prop : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g))
  have hdist := congrArg (fun d : 𝓢'(ℝ, ℂ) => d φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  have htest : (∫ x : ℝ, φ x * 𝓕 f x) = ∫ x : ℝ, 𝓕 (φ : ℝ → ℂ) x * f x := by
    have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) Real.continuous_fourierChar (innerSL ℝ).continuous₂ (φ.integrable (μ := volume)) h1
    rw [flip_innerₗ] at hh
    simpa only [smul_eq_mul] using! hh.symm
  have hcoe : (∫ x : ℝ, 𝓕 (φ : ℝ → ℂ) x * f x) =
      ∫ x : ℝ, (𝓕 φ) x • (h2.toLp f) x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    simp [hx, SchwartzMap.fourier_coe]
  calc
    _ = ∫ x : ℝ, φ x * 𝓕 f x := by rfl
    _ = _ := htest
    _ = _ := hcoe
    _ = _ := hdist
    _ = _ := by rfl

/-- Integral Plancherel for an integrable square integrable profile.
This supplies the full line energy identity on book page 434.
-/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hh : (∫ x : ℝ, ‖(𝓕 (h2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x‖ ^ 2) =
      ∫ x : ℝ, ‖(h2.toLp f) x‖ ^ 2 := by
    apply Complex.ofRealLI.injective
    have H := Lp.inner_fourier_eq (h2.toLp f) (h2.toLp f)
    change (∫ x : ℝ, inner ℂ ((𝓕 (h2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x)
      ((𝓕 (h2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x)) =
      ∫ x : ℝ, inner ℂ ((h2.toLp f) x) ((h2.toLp f) x) at H
    simp only [inner_self_eq_norm_sq_to_K] at H
    simpa only [← LinearIsometry.integral_comp_comm, Complex.ofRealLI_apply,
      Complex.ofReal_pow] using! H
  calc
    _ = ∫ x : ℝ, ‖(𝓕 (h2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourierIntegral_ae_eq_L2 h1 h2] with x hx
      rw [hx]
    _ = _ := hh
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]

/-- The integral Fourier transform of an L1 and L2 profile is square integrable.
This is the convergence part of Plancherel on book page 434.
-/
theorem fourier_memLp_two {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourierIntegral_ae_eq_L2 h1 h2)).2
    (Lp.memLp (𝓕 (h2.toLp f) : Lp (α := ℝ) ℂ 2 volume))

end LeanLab.HelfgottMajor.Fourier431
