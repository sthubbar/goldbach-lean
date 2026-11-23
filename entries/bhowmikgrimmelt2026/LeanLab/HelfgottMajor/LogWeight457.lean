module

public import LeanLab.HelfgottMajor.Contour457
public import LeanLab.PNTPort.ZetaZeros.LeftLine
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
Convergence of the logarithmic derivative square energy on the left contour.
Source P0014 pages 34 and 35, displays 4.12 and 4.13.
The numerical square energy budget remains a separate OPEN input.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.LogWeight457
open Real Complex MeasureTheory Filter Set Contour457
open scoped Topology

/-- A coarse integrable majorant for logarithmic growth on the left contour.
Derived convergence estimate for P0014 page 35 after display 4.13.
-/
theorem logarithmic_line_majorant (t : ℝ) :
    Real.log (|t| + 3) / ‖(-1 / 2 : ℂ) + t * Complex.I‖ ≤
      36 * (1 + |t|) ^ (-(3 / 4 : ℝ)) := by
  let a := |t|
  let d := ‖(-1 / 2 : ℂ) + t * Complex.I‖
  have ha : 0 ≤ a := abs_nonneg t
  have hpos : 0 < 1 + a := by positivity
  have hd0 : 0 ≤ d := norm_nonneg _
  have hsq : d ^ 2 = 1 / 4 + a ^ 2 := by
    dsimp only [d, a]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hd : (1 + a) / 3 ≤ d := by
    nlinarith [sq_nonneg (2 * a - 1 / 4)]
  have hdpos : 0 < d := by linarith
  have hl : Real.log (a + 3) ≤ 12 * (1 + a) ^ (1 / 4 : ℝ) := by
    have hh := Real.log_le_rpow_div (by positivity : 0 ≤ a + 3) (by norm_num : (0 : ℝ) < 1 / 4)
    have hr : (a + 3) ^ (1 / 4 : ℝ) ≤ ((1 + a) * 3) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow hpos.le (by norm_num)] at hr
    have h3 : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hm := mul_le_mul_of_nonneg_left h3
      (Real.rpow_nonneg hpos.le (1 / 4 : ℝ))
    nlinarith
  change Real.log (a + 3) / d ≤ 36 * (1 + a) ^ (-(3 / 4 : ℝ))
  calc
    _ ≤ (12 * (1 + a) ^ (1 / 4 : ℝ)) / d :=
      div_le_div_of_nonneg_right hl hd0
    _ ≤ (12 * (1 + a) ^ (1 / 4 : ℝ)) / ((1 + a) / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by
      rw [show (-(3 / 4 : ℝ)) = 1 / 4 - 1 by ring, Real.rpow_sub hpos, Real.rpow_one]
      field_simp
      ring

/-- The logarithmic derivative weight is continuous on the left contour.
Source P0014 pages 34 and 35. The zeta function has no zero on this line.
-/
theorem principalLogWeight_continuous : Continuous principalLogWeight := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let s : ℂ := (-1 / 2 : ℂ) + t * Complex.I
  have hs1 : s ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [s] at hh
  have hs0 : s ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [s] at hh
  have hz : riemannZeta s ≠ 0 := by
    simpa [s] using
      LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
  have ha := analyticAt_riemannZeta hs1
  have hc : ContinuousAt (logDeriv riemannZeta) s := (ha.deriv.div ha hz).continuousAt
  have hline : ContinuousAt (fun t : ℝ => (-1 / 2 : ℂ) + t * Complex.I) t := by fun_prop
  exact (ContinuousAt.comp (f := fun t : ℝ => (-1 / 2 : ℂ) + t * Complex.I)
    hc hline).div hline hs0

/-- The principal logarithmic derivative weight is square integrable.
Source P0014 page 35 after display 4.13. This proves convergence without the 6.01 budget.
-/
theorem principal_log_weight_memLp_two : MemLp principalLogWeight 2 := by
  obtain ⟨C, hC, hbound⟩ := LeanLab.PNTPort.ZetaZeros.logDeriv_left_line
  have hmajor (t : ℝ) : ‖principalLogWeight t‖ ≤
      (36 * C) * (1 + |t|) ^ (-(3 / 4 : ℝ)) := by
    have hh : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * Real.log (|t| + 3) := by
      simpa [logDeriv_apply] using (hbound t).2
    rw [principalLogWeight, norm_div]
    calc
      _ ≤ (C * Real.log (|t| + 3)) / ‖(-1 / 2 : ℂ) + t * Complex.I‖ :=
        div_le_div_of_nonneg_right hh (norm_nonneg _)
      _ = C * (Real.log (|t| + 3) / ‖(-1 / 2 : ℂ) + t * Complex.I‖) := by ring
      _ ≤ C * (36 * (1 + |t|) ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (logarithmic_line_majorant t) hC.le
      _ = _ := by ring
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))
  apply (memLp_two_iff_integrable_sq_norm
    principalLogWeight_continuous.aestronglyMeasurable).mpr
  apply (hbase.const_mul ((36 * C) ^ 2)).mono'
    (principalLogWeight_continuous.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hh := (sq_le_sq₀ (norm_nonneg (principalLogWeight t))
    (by positivity : 0 ≤ (36 * C) * (1 + |t|) ^ (-(3 / 4 : ℝ)))).mpr (hmajor t)
  convert hh using 1
  simp only [mul_pow]
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + |t|)]
  norm_num

end LeanLab.HelfgottMajor.LogWeight457
