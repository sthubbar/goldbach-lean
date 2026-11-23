module

public import LeanLab.KadiriLumley2014.PsiPrimitive301

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4, transfer of the integrated explicit formula.
Integration by parts from psi one to the polynomial-weighted psi integral.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64
open LeanLab.Dudek2014.Section22 (psi1)

/-- Positive affine scaling transfers psi one to the actual weighted psi integral. -/
theorem integral_psi_affine_weight {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    d * (∫ t in (0 : ℝ)..1, Chebyshev.psi (c + d * t) * weight m t) =
      -(∫ t in (0 : ℝ)..1, psi1 (c + d * t) * weightD m t) := by
  let F : ℝ → ℝ := fun t => psi1 (c + d * t)
  have hFc : ContinuousOn F (uIcc (0 : ℝ) 1) := by
    apply (psi1_continuousOn_Icc hc.le (by linarith : c ≤ c + d)).comp
      (by fun_prop : ContinuousOn (fun t : ℝ => c + d * t) (uIcc 0 1))
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hFd : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivWithinAt F (d * Chebyshev.psi (c + d * t)) (Ioi t) t := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    have harg : 0 < c + d * t := by nlinarith [ht'.1]
    have hlin : HasDerivAt (fun t : ℝ => c + d * t) d t := by
      simpa using ((hasDerivAt_id t).const_mul d).const_add c
    have h := (psi1_hasDerivWithinAt_right harg).comp t (hlin.hasDerivWithinAt (s := Ioi t)) (by
      intro s hs
      change t < s at hs
      change c + d * t < c + d * s
      nlinarith)
    simpa only [F, Function.comp_def, mul_comm] using h
  have hmono : Monotone (fun t : ℝ => Chebyshev.psi (c + d * t)) :=
    Chebyshev.psi_mono.comp (by intro s t hst; dsimp; nlinarith)
  have hFi : IntervalIntegrable (fun t : ℝ => d * Chebyshev.psi (c + d * t)) volume 0 1 :=
    (hmono.intervalIntegrable (a := 0) (b := 1)).const_mul d
  have hwd := (weightD_continuous m).intervalIntegrable (μ := volume) 0 1
  have hp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right hFc
    (weight_continuous m).continuousOn hFd
    (fun t _ => (weight_hasDerivAt m t).hasDerivWithinAt) hFi hwd
  have hboundary : F 1 * weight m 1 - F 0 * weight m 0 = 0 := by
    rw [(weight_endpoints hm).1, (weight_endpoints hm).2]
    ring
  rw [hboundary, intervalIntegral.integral_add
    (hFi.mul_continuousOn (weight_continuous m).continuousOn)
    (hFc.intervalIntegrable.mul_continuousOn (weightD_continuous m).continuousOn)] at hp
  have hscale : (∫ t in (0 : ℝ)..1, (d * Chebyshev.psi (c + d * t)) * weight m t) =
      d * (∫ t in (0 : ℝ)..1, Chebyshev.psi (c + d * t) * weight m t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [hscale] at hp
  exact eq_neg_of_add_eq_zero_left hp

end LeanLab.KadiriLumley2014.Task301
