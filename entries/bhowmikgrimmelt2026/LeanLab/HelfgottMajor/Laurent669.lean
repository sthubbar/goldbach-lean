module

public import LeanLab.HelfgottMajor.Route669

/-!
The constant Laurent coefficient of the continued Gaussian Mellin transform.
Source P0014 page 32 and page 33, display 4.6.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Laurent669
open Real MeasureTheory Filter Asymptotics Set
open LeanLab.HelfgottArcs Decomp269a MainLemma41Split123
open scoped Topology

/-- P0014 page 32, differentiation of the Mellin integral. The Gaussian derivative formula
holds throughout the positive half plane, including both shifted moments at zero. -/
theorem gaussian_mellin_hasDerivAt_pos (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => log t • ((Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) s ∧
      HasDerivAt (gaussianMellin δ)
        (mellin (fun t : ℝ => log t • ((Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) s) s := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  have hn (t : ℝ) : ‖f t‖ = Real.exp (-t ^ 2 / 2) := by
    have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    have he := he0 (δ * t)
    dsimp only [f]
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have hc : Continuous f := by unfold f e; fun_prop
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
    rw [← isBigO_norm_left]
    simp_rw [hn]
    have hexp : (fun t : ℝ => Real.exp (-t)) =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
      simpa only [one_mul, neg_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-(s.re + 1))).isBigO
    have hh := (exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)).isBigO.trans hexp
    simpa only [one_mul, neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using hh
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    simp only [hn, neg_zero, rpow_zero, norm_one, mul_one]
    exact exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  exact mellin_hasDerivAt_of_isBigO_rpow
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop (by linarith) hbot hs


/-- P0014 page 32 and display 4.6 on page 33. The derivative at zero of the regular
Mellin numerator equals the integral defining its constant Laurent coefficient. -/
theorem mellin_tDerivWeight_hasDerivAt_zero (δ : ℝ) :
    HasDerivAt (mellin (tDerivWeight δ)) (laurentC0 δ) 0 := by
  let g : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  let A : ℂ → ℝ → ℂ := fun z t =>
    (t : ℂ) ^ (z - 1) * ((log t : ℂ) * g t)
  let c : ℂ := 2 * π * Complex.I * δ
  have h1 := gaussian_mellin_hasDerivAt_pos δ ((0 : ℂ) + 1) (by norm_num)
  have h2 := gaussian_mellin_hasDerivAt_pos δ ((0 : ℂ) + 2) (by norm_num)
  have hD := (h2.2.comp 0 ((hasDerivAt_id (0 : ℂ)).add_const 2)).sub
    ((h1.2.comp 0 ((hasDerivAt_id (0 : ℂ)).add_const 1)).const_mul c)
  simp only [zero_add, mul_one] at hD h1 h2
  have hi1 : IntegrableOn (A 1) (Ioi 0) := by
    simpa [MellinConvergent, A, g, smul_eq_mul, RCLike.real_smul_eq_coe_mul] using! h1.1
  have hi2 : IntegrableOn (A 2) (Ioi 0) := by
    simpa [MellinConvergent, A, g, smul_eq_mul, RCLike.real_smul_eq_coe_mul] using! h2.1
  have hval : mellin (fun t : ℝ => log t • g t) 2 -
      c * mellin (fun t : ℝ => log t • g t) 1 = laurentC0 δ := by
    simp only [mellin, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
    change (∫ t in Ioi (0 : ℝ), A 2 t) - c * (∫ t in Ioi (0 : ℝ), A 1 t) = _
    rw [← integral_const_mul, ← integral_sub hi2 (hi1.const_mul c),
      laurentC0, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    norm_num only [A, g, c, show (2 : ℂ) - 1 = 1 by norm_num,
      sub_self, Complex.cpow_one, Complex.cpow_zero, one_mul]
    ring
  have hn : HasDerivAt (fun z : ℂ => gaussianMellin δ (z + 2) -
      c * gaussianMellin δ (z + 1)) (laurentC0 δ) 0 := by
    convert hD using 1
    · funext z; rfl
    · exact hval.symm
  apply hn.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num : (-1 : ℝ) < (0 : ℂ).re)] with z hz
  exact Route669.mellin_tDerivWeight δ z hz

/-- P0014 page 32 and display 4.6 on page 33. Subtracting the principal part one over s
from the continued Mellin transform has limit laurentC0 delta at zero. -/
theorem contMellin_sub_pole_tendsto (δ : ℝ) :
    Tendsto (fun s : ℂ => contMellin δ s - 1 / s) (𝓝[≠] 0) (𝓝 (laurentC0 δ)) := by
  have h := (mellin_tDerivWeight_hasDerivAt_zero δ).tendsto_slope_zero
  simp only [zero_add, Route669.mellin_tDerivWeight_zero, smul_eq_mul] at h
  apply h.congr'
  filter_upwards [] with s
  simp only [contMellin, div_eq_mul_inv]
  ring

end LeanLab.HelfgottMajor.Laurent669
