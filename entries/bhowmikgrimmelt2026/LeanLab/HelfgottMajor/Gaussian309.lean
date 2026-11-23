module

public import LeanLab.HelfgottMajor.Gaussian269
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
The unshifted Gaussian Mellin transform near zero.
Source P0014 page 33 display 4.6 and page 43 display 4.42.
These identities supply the Gaussian factor in the local residue audit.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Gaussian309
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a

/-- The unshifted Gaussian Mellin transform in Gamma form.
This is the Gaussian specialization of the Mellin integral used on pages 31 to 33.
-/
theorem mellin_zero_shift (s : ℂ) (hs : 0 < s.re) :
    gaussianMellin 0 s = (1 / 2 : ℂ) * (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2) := by
  have hcomp := mellin_comp_rpow
    (fun t : ℝ => (exp (-(t / 2)) : ℂ)) s 2
  have hbase : mellin (fun t : ℝ => (exp (-(t / 2)) : ℂ)) (s / 2) =
      (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2) := by
    have hg := Complex.integral_cpow_mul_exp_neg_mul_Ioi
      (a := s / 2) (r := (1 / 2 : ℝ)) (by simpa using half_pos hs) (by norm_num)
    simpa [mellin, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_mul, div_eq_mul_inv, mul_comm] using hg
  norm_num only [Complex.ofReal_ofNat] at hcomp
  rw [hbase] at hcomp
  have heq : gaussianMellin 0 s =
      mellin (fun t : ℝ => (exp (-(t ^ (2 : ℝ) / 2)) : ℂ)) s := by
    simp [gaussianMellin, e]
    congr 1
    funext t
    congr 1
    ring
  rw [heq, hcomp]
  norm_num [smul_eq_mul, mul_assoc]

/-- Multiplication by s removes the Gaussian Mellin pole at zero, display 4.6 on page 33.
The right side gives the regular extension of that numerator.
-/
theorem regularized_mellin (s : ℂ) (hs : 0 < s.re) :
    s * gaussianMellin 0 s = (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 1) := by
  rw [mellin_zero_shift s hs, Complex.Gamma_add_one _ (by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith)]
  ring

/-- The regularized Gaussian numerator has value one at zero, display 4.6 on page 33. -/
theorem regularized_value :
    (2 : ℂ) ^ ((0 : ℂ) / 2) * Complex.Gamma ((0 : ℂ) / 2 + 1) = 1 := by simp

/-- The constant Laurent coefficient of the unshifted Gaussian Mellin transform.
This evaluates c0 in display 4.6 on page 33 by differentiating the regular numerator.
-/
theorem regularized_derivative :
    HasDerivAt (fun s : ℂ => (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 1))
      (((log 2 : ℝ) : ℂ) / 2 - (eulerMascheroniConstant : ℂ) / 2) 0 := by
  have hlin : HasDerivAt (fun s : ℂ => s / 2 + 1) (1 / 2) 0 := by
    convert (((hasDerivAt_id (0 : ℂ)).div_const 2).add_const 1) using 1 <;> simp
  have hg1 : HasDerivAt Complex.Gamma (-(eulerMascheroniConstant : ℂ))
      ((fun s : ℂ => s / 2 + 1) 0) := by
    simpa using Complex.hasDerivAt_Gamma_one
  have hg := hg1.comp (0 : ℂ) hlin
  have hp := ((hasDerivAt_id (0 : ℂ)).div_const 2).const_cpow
    (c := (2 : ℂ)) (Or.inl (by norm_num))
  have hprod := hp.mul hg
  simp only [Pi.mul_apply, Function.comp_apply, id_eq, zero_div, Complex.cpow_zero,
    Complex.Gamma_one, zero_add, mul_one, one_mul] at hprod
  have hl : ((log 2 : ℝ) : ℂ) = Complex.log (2 : ℂ) := by
    simpa using Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)
  convert hprod using 1
  · funext s
    rfl
  · rw [hl]
    ring

end LeanLab.HelfgottMajor.Gaussian309
