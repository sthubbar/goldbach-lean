module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
Scalar Gamma derivative tools for P0014 page 43 display 4.42.
The trigamma value at one half follows from differentiating reflection.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Gamma431
open Complex Filter
open scoped Topology

/-- Gamma is analytic on the positive real half plane.
This is a prerequisite for the symbolic moment calculation in display 4.42.
-/
theorem analyticAt_Gamma_of_re_pos (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    apply (differentiableAt_Gamma z ?_).differentiableWithinAt
    intro n heq
    have hh := congrArg Complex.re heq
    simp only [neg_re, natCast_re] at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    change 0 < z.re at hz
    linarith
  exact (hd.analyticOnNhd (isOpen_lt continuous_const continuous_re)) s hs

/-- Digamma is differentiable on the positive real half plane.
This supplies the derivative used to evaluate the scalar log squared moment in display 4.42.
-/
theorem differentiableAt_digamma_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ digamma s := by
  have ha := analyticAt_Gamma_of_re_pos s hs
  exact ha.deriv.differentiableAt.div ha.differentiableAt (Gamma_ne_zero_of_re_pos hs)

/-- The digamma derivative at one half is pi squared over two.
Source P0014 page 43 display 4.42, symbolic scalar moment calculation.
This follows from Mathlib digamma reflection and Gamma analyticity.
-/
theorem deriv_digamma_one_half : deriv digamma (1 / 2 : ℂ) = (Real.pi : ℂ) ^ 2 / 2 := by
  have hp := (differentiableAt_digamma_of_re_pos (1 / 2) (by norm_num)).hasDerivAt
  have hp' : HasDerivAt digamma (deriv digamma (1 / 2 : ℂ)) (1 - (1 / 2 : ℂ)) := by
    convert hp using 1 <;> norm_num
  have hleft := hp'.comp (1 / 2) ((hasDerivAt_const (1 / 2 : ℂ) 1).sub (hasDerivAt_id _))
  have harg : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) (1 / 2) := by
    convert (hasDerivAt_id (1 / 2 : ℂ)).const_mul (Real.pi : ℂ) using 1 <;> simp
  have hs := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * (1 / 2))).comp (1 / 2) harg
  have hc := (Complex.hasDerivAt_cos ((Real.pi : ℂ) * (1 / 2))).comp (1 / 2) harg
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 / 2)) = 1 := by
    rw [mul_one_div, Complex.sin_pi_div_two]
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 / 2)) = 0 := by
    rw [mul_one_div, Complex.cos_pi_div_two]
  have hquot := (hc.div hs (by simpa only [Function.comp_apply, hsin] using (one_ne_zero : (1 : ℂ) ≠ 0))).const_mul (Real.pi : ℂ)
  have hright := hp.add hquot
  have heq : (fun z : ℂ => digamma (1 - z)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      (fun z : ℂ => digamma z + (Real.pi : ℂ) *
        (Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z))) := by
    filter_upwards [(isOpen_Ioo.preimage continuous_re).mem_nhds
      (show (1 / 2 : ℂ) ∈ Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1 by norm_num)] with z hz
    change 0 < z.re ∧ z.re < 1 at hz
    rw [digamma_one_sub]
    · rfl
    · intro n hn
      have hh := congrArg Complex.re hn
      simp only [intCast_re] at hh
      have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast (le_of_lt (hz.1.trans_eq hh))
      have hn1 : n < (1 : ℤ) := by exact_mod_cast (hh ▸ hz.2)
      have hnz : n = 0 := by omega
      simp [hnz] at hh
      linarith [hz.1]
  have he := hleft.unique (hright.congr_of_eventuallyEq heq)
  simp only [Function.comp_apply, hcos, hsin, zero_mul, one_mul, mul_one, mul_zero, sub_zero, one_pow,
    div_one, zero_sub, neg_mul] at he
  linear_combination (-1 / 2 : ℂ) * he

/-- The second Gamma derivative at one half gives the closed form in display 4.42.
This is the symbolic special function value before identifying its moment integral.
-/
theorem deriv2_Gamma_one_half :
    deriv (deriv Gamma) (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) *
      (((Real.eulerMascheroniConstant : ℂ) + 2 * log 2) ^ 2 + (Real.pi : ℂ) ^ 2 / 2) := by
  have hG := Complex.hasDerivAt_Gamma_one_half
  have hψ := (differentiableAt_digamma_of_re_pos (1 / 2) (by norm_num)).hasDerivAt
  rw [deriv_digamma_one_half] at hψ
  have hd := hG.mul hψ
  have heq : deriv Gamma =ᶠ[𝓝 (1 / 2 : ℂ)] (fun z => Gamma z * digamma z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (0 : ℝ) < (1 / 2 : ℂ).re by norm_num)] with z hz
    rw [digamma, logDeriv_apply, mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hz)]
  have hh := (hd.congr_of_eventuallyEq heq).deriv
  rw [Gamma_one_half_eq, digamma_one_half] at hh
  have hsqrt := (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm
  rw [← Real.sqrt_eq_rpow] at hsqrt
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hsqrt
  rw [hsqrt] at hh
  convert hh using 1 <;> ring

end LeanLab.HelfgottMajor.Gamma431
