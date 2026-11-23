module

public import LeanLab.HelfgottMajor.Gaussian309
public import LeanLab.HelfgottMajor.Continuation457
public import LeanLab.HelfgottMajor.Contour457
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
The conductor one residue in P0014 page 33 after display 4.9 and page 34.
This regular logarithmic derivative has no double pole at zero.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Principal457
open Complex Filter
open scoped Topology

/-- The conductor one logarithmic derivative at zero, page 33 after display 4.9. -/
theorem zeta_logDeriv_zero :
    logDeriv riemannZeta 0 = (Real.log (2 * Real.pi) : ℂ) := by
  simp only [logDeriv, Pi.div_apply, deriv_riemannZeta_zero, riemannZeta_zero]
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  ring

/-- The unshifted principal residue limit retains the scale factor from display 4.7.
Source P0014 pages 33 and 34. The limit is along positive real s and equals log of two pi
for every positive x. No explicit formula or finite critical line check is used.
-/
theorem principal_unshifted_residue (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => (t : ℂ) * logDeriv riemannZeta (t : ℂ) *
      Decomp269a.gaussianMellin 0 (t : ℂ) * (x : ℂ) ^ (t : ℂ))
      (𝓝[>] 0) (𝓝 (Real.log (2 * Real.pi) : ℂ)) := by
  have hz : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by simp)
  have hl : ContinuousAt (logDeriv riemannZeta) 0 :=
    (hz.deriv.div hz (by rw [riemannZeta_zero]; norm_num)).continuousAt
  have hG := Gaussian309.regularized_derivative.continuousAt
  have hp : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) 0 :=
    continuousAt_const_cpow (by exact_mod_cast hx.ne')
  have hlim : Tendsto (fun s : ℂ => logDeriv riemannZeta s *
      ((2 : ℂ) ^ (s / 2) * Gamma (s / 2 + 1)) * (x : ℂ) ^ s)
      (𝓝 0) (𝓝 (Real.log (2 * Real.pi) : ℂ)) := by
    simpa only [Pi.mul_apply, zero_div, cpow_zero, zero_add, Gamma_one, mul_one,
      zeta_logDeriv_zero] using! ((hl.mul hG).mul hp).tendsto
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply (hlim.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  change 0 < t at htpos
  change logDeriv riemannZeta (t : ℂ) *
    ((2 : ℂ) ^ ((t : ℂ) / 2) * Gamma ((t : ℂ) / 2 + 1)) * (x : ℂ) ^ (t : ℂ) = _
  rw [← Gaussian309.regularized_mellin (t : ℂ) (by simpa using htpos)]
  ring

/-- The principal residue of the continued shifted transform is independent of x and delta.
Source P0014 page 33 display 4.7 and the conductor one case on page 34.
The continued transform is the explicit integration by parts expression from display 4.14.
-/
theorem principal_shifted_residue (δ x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => (t : ℂ) * logDeriv riemannZeta (t : ℂ) *
      Contour457.continuedGaussian δ (t : ℂ) * (x : ℂ) ^ (t : ℂ))
      (𝓝[>] 0) (𝓝 (Real.log (2 * Real.pi) : ℂ)) := by
  have hz : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by simp)
  have hl : ContinuousAt (logDeriv riemannZeta) 0 :=
    (hz.deriv.div hz (by rw [riemannZeta_zero]; norm_num)).continuousAt
  have hG := Continuation457.regular_numerator_continuous δ
  have hp : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) 0 :=
    continuousAt_const_cpow (by exact_mod_cast hx.ne')
  have hlim : Tendsto (fun s : ℂ => logDeriv riemannZeta s *
      (Decomp269a.gaussianMellin δ (s + 2) -
        (2 * Real.pi * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1)) *
        (x : ℂ) ^ s) (𝓝 0) (𝓝 (Real.log (2 * Real.pi) : ℂ)) := by
    simpa only [Pi.mul_apply, zero_add, cpow_zero, mul_one,
      Continuation457.shifted_first_moment, zeta_logDeriv_zero] using!
        ((hl.mul hG).mul hp).tendsto
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply (hlim.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  change 0 < t at htpos
  dsimp only [Function.comp_apply, Contour457.continuedGaussian]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  field_simp

/-- The same principal residue limit for the original shifted Gaussian Mellin integral.
Source P0014 pages 33 and 34, display 4.7. Integration by parts identifies the continuation
with the defining integral on the positive real approach to zero.
-/
theorem principal_gaussian_residue (δ x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => (t : ℂ) * logDeriv riemannZeta (t : ℂ) *
      Decomp269a.gaussianMellin δ (t : ℂ) * (x : ℂ) ^ (t : ℂ))
      (𝓝[>] 0) (𝓝 (Real.log (2 * Real.pi) : ℂ)) := by
  apply (principal_shifted_residue δ x hx).congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  change 0 < t at htpos
  rw [Continuation457.continuedGaussian_eq δ (t : ℂ) (by simpa using htpos)]

end LeanLab.HelfgottMajor.Principal457
