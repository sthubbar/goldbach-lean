module

public import LeanLab.KadiriLumley2014.TrivialSeries259
public import LeanLab.KadiriLumley2014.WeightDerivative

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equation 2.15.
Transfer the integrated trivial-zero series to the logarithmic remainder.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Real Set MeasureTheory
open Task64
open LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- The logarithmic derivative term is continuous along every affine interval above two. -/
theorem trivial_log_continuousOn {c d : ℝ} (hc : 2 < c) (hd : 0 ≤ d) :
    ContinuousOn (fun t : ℝ => Real.log (1 - 1 / (c + d * t) ^ 2)) (Icc 0 1) := by
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 2 < c + d * t := by
    intro t ht
    nlinarith [mul_nonneg hd ht.1]
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, (c + d * t) ^ 2 ≠ 0 := by
    intro t ht
    have h := hp t ht
    nlinarith
  apply (continuousOn_const.sub (continuousOn_const.div
    (by fun_prop : ContinuousOn (fun t : ℝ => (c + d * t) ^ 2) (Icc 0 1)) hsq)).log
  intro t ht
  have h := hp t ht
  have hpos : 0 < (c + d * t) ^ 2 := by nlinarith
  apply ne_of_gt
  apply sub_pos.mpr
  exact (div_lt_one hpos).mpr (by nlinarith)

/-- The integrated trivial-zero series transfers to the logarithmic integral by parts. -/
theorem integral_trivial_weightD {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 2 < c) (hd : 0 ≤ d) :
    (∫ t in (0 : ℝ)..1,
      ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t) =
      -(d / 2) * (∫ t in (0 : ℝ)..1,
        Real.log (1 - 1 / (c + d * t) ^ 2) * weight m t) := by
  let F : ℝ → ℝ := fun t => (c + d * t) * ∑' n : ℕ, tb (c + d * t) n
  have hp : ∀ t ∈ uIcc (0 : ℝ) 1, 2 < c + d * t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    nlinarith [mul_nonneg hd ht.1]
  have hFd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt F ((d / 2) * Real.log (1 - 1 / (c + d * t) ^ 2)) t := by
    intro t ht
    have hlin : HasDerivAt (fun t : ℝ => c + d * t) d t := by
      simpa using ((hasDerivAt_id t).const_mul d).const_add c
    convert (hasDerivAt_trivial_series (hp t ht)).comp t hlin using 1
    · rfl
    · ring
  have hFc : ContinuousOn F (uIcc (0 : ℝ) 1) :=
    fun t ht => (hFd t ht).continuousAt.continuousWithinAt
  have hlog := trivial_log_continuousOn hc hd
  rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hlog
  have hdi : IntervalIntegrable (fun t : ℝ => (d / 2) * Real.log (1 - 1 / (c + d * t) ^ 2)) volume 0 1 :=
    (hlog.const_mul (d / 2)).intervalIntegrable
  have hwd := (weightD_continuous m).intervalIntegrable (μ := volume) 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFc (weight_continuous m).continuousOn
    (fun t ht => hFd t (by simpa using mem_Icc_of_Ioo ht))
    (fun t _ => weight_hasDerivAt m t) hdi hwd
  rw [(weight_endpoints hm).1, (weight_endpoints hm).2] at h
  simp only [mul_zero, sub_self, zero_sub] at h
  change (∫ t in (0 : ℝ)..1, F t * weightD m t) = _
  rw [h]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

end LeanLab.KadiriLumley2014.Task259
