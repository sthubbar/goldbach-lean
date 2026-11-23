module

public import LeanLab.Linnik1951.SPLIT1622_mellin
public import LeanLab.Linnik1951.Decomp376f

/-!
P0093 pages 157 and 158. Abstract outer Mellin kernel estimate and transfer.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory


/-- LEAF. P0093 page 158 reciprocal difference kernel after equation
4.6. Its integral on the square box is at least T when T is at least
one. This lower bound absorbs the prime power transfer error only. -/
theorem difference_kernel_lower442 (T : ℝ) (hT : 1 ≤ T) :
    T ≤ differenceKernel376 T := by
  have hTp : 0 < T := by linarith
  have hc : Continuous (fun t : ℝ => ∫ u in -T..T, 1 / (1 + |t - u|)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_const.div
        (continuous_const.add ((continuous_fst.sub continuous_snd).abs))
        (fun x : ℝ × ℝ => ne_of_gt (show (0 : ℝ) < 1 + |x.1 - x.2| by positivity))) (-T) T
  have hinner (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      (2 * T) / (1 + 2 * T) ≤ ∫ u in -T..T, 1 / (1 + |t - u|) := by
    have hh : (∫ _u in -T..T, (1 : ℝ) / (1 + 2 * T)) ≤
        ∫ u in -T..T, 1 / (1 + |t - u|) := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        ((show Continuous (fun u : ℝ => 1 / (1 + |t - u|)) by
          exact continuous_const.div
            (continuous_const.add ((continuous_const.sub continuous_id).abs))
            (fun u => ne_of_gt (by positivity))).intervalIntegrable _ _)
      intro u hu
      have hab : |t - u| ≤ 2 * T := abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have he : (∫ _u in -T..T, (1 : ℝ) / (1 + 2 * T)) =
        (2 * T) / (1 + 2 * T) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rwa [he] at hh
  have hout : (∫ _t in -T..T, (2 * T) / (1 + 2 * T)) ≤ differenceKernel376 T := by
    exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hc.intervalIntegrable _ _) hinner
  have hcalc : (∫ _t in -T..T, (2 * T) / (1 + 2 * T)) =
      4 * T ^ 2 / (1 + 2 * T) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hcalc] at hout
  apply le_trans _ hout
  apply (le_div_iff₀ (by positivity : 0 < 1 + 2 * T)).mpr
  nlinarith

end LeanLab.Linnik1951
