module

public import LeanLab.HelfgottMajor.Lemma41Kernel669
public import LeanLab.HelfgottMajor.Continuation457

/-!
P0014 pages 32 and 35, displays 4.6 and 4.14.
Identify the integral continuation used by the new route with the existing shifted moments.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Route669
open Real Complex MeasureTheory Set Filter
open LeanLab.HelfgottArcs Decomp269a MainLemma41Split123
open scoped Topology

/-- P0014 page 35, display 4.14. The Mellin numerator is the difference of two shifted
Gaussian moments throughout the half plane of real part above minus one. -/
theorem mellin_tDerivWeight (δ : ℝ) (s : ℂ) (hs : -1 < s.re) :
    mellin (tDerivWeight δ) s = gaussianMellin δ (s + 2) -
      (2 * π * I * δ) * gaussianMellin δ (s + 1) := by
  let A : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) *
    ((Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t))
  have hA (z : ℂ) (hz : 0 < z.re) : IntegrableOn (A z) (Ioi 0) := by
    simpa only [A, smul_eq_mul] using Gaussian269.mellin_integrable δ z hz
  have h1 := hA (s + 1) (by simp; linarith)
  have h2 := hA (s + 2) (by simp; linarith)
  have hp : mellin (tDerivWeight δ) s = ∫ t in Ioi (0 : ℝ),
      A (s + 2) t - (2 * π * I * δ) * A (s + 1) t := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp1 : (t : ℂ) ^ ((s + 1) - 1) = (t : ℂ) ^ (s - 1) * t := by
      rw [show (s + 1) - 1 = (s - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]
    have hp2 : (t : ℂ) ^ ((s + 2) - 1) = (t : ℂ) ^ (s - 1) * t ^ 2 := by
      rw [show (s + 2) - 1 = (s - 1) + 2 by ring, cpow_add _ _ ht0, cpow_ofNat]
    simp only [A, hp1, hp2, smul_eq_mul, tDerivWeight]
    ring
  rw [hp, integral_sub h2 (h1.const_mul _), integral_const_mul]
  rfl

/-- P0014 pages 32 and 35. The integral continuation equals the shifted moment continuation. -/
theorem contMellin_eq (δ : ℝ) (s : ℂ) (hs : -1 < s.re) :
    contMellin δ s = Contour457.continuedGaussian δ s := by
  rw [contMellin, mellin_tDerivWeight δ s hs, Contour457.continuedGaussian]

/-- P0014 page 32. In the original convergence half plane the continuation equals G delta. -/
theorem contMellin_eq_gaussianMellin (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    contMellin δ s = gaussianMellin δ s := by
  rw [contMellin_eq δ s (by linarith), Continuation457.continuedGaussian_eq δ s hs]

/-- P0014 page 32 before display 4.6. The regular Mellin numerator has value one at zero. -/
theorem mellin_tDerivWeight_zero (δ : ℝ) : mellin (tDerivWeight δ) 0 = 1 := by
  simpa using (mellin_tDerivWeight δ 0 (by norm_num)).trans
    (by simpa using Continuation457.shifted_first_moment δ)

/-- P0014 page 32 before display 4.6. The residue of the continued Mellin transform at zero
is one, expressed as the limit of its regularized product. -/
theorem contMellin_residue_one (δ : ℝ) :
    Tendsto (fun s : ℂ => s * contMellin δ s) (𝓝[≠] 0) (𝓝 1) := by
  have hc : Tendsto (fun s : ℂ => gaussianMellin δ (s + 2) -
      (2 * π * I * δ) * gaussianMellin δ (s + 1)) (𝓝 0) (𝓝 1) := by
    have hv := Continuation457.shifted_first_moment δ
    simpa only [zero_add, hv] using
      (Continuation457.regular_numerator_continuous δ).tendsto
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  have hsmall : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -1 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hs hsr
  change s ≠ 0 at hs
  rw [contMellin_eq δ s hsr, Contour457.continuedGaussian]
  field_simp

/-- P0014 page 32. The continuation is holomorphic in real part above minus one away from zero. -/
theorem contMellin_differentiableAt (δ : ℝ) (s : ℂ) (hs : -1 < s.re) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (contMellin δ) s := by
  have h2 := (Continuation457.gaussian_mellin_differentiable δ (s + 2)
    (by simp; linarith)).comp s (differentiableAt_id.add_const 2)
  have h1 := (Continuation457.gaussian_mellin_differentiable δ (s + 1)
    (by simp; linarith)).comp s (differentiableAt_id.add_const 1)
  have hd : DifferentiableAt ℂ (Contour457.continuedGaussian δ) s :=
    (h2.sub (h1.const_mul _)).div differentiableAt_id hs0
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact contMellin_eq δ z hz

end LeanLab.HelfgottMajor.Route669
