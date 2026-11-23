module

public import LeanLab.KadiriLumley2014.ZeroParts259
public import LeanLab.KadiriLumley2014.TrivialParts259
public import LeanLab.KadiriLumley2014.PsiParts301

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equation 2.15.
The integrated explicit formula against the polynomial derivative weight.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Real Set MeasureTheory
open Task64 Task301
open LeanLab.PNTPort.ExplicitPsi1
open LeanLab.PNTPort.ExplicitPsi1.Trivial
open LeanLab.Dudek2014.Section22 (psi1)

/-- Every polynomial derivative weight has zero integral when m is positive. -/
theorem integral_weightD_zero {m : ℕ} (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, weightD m t) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => weight_hasDerivAt m t)
    ((weightD_continuous m).intervalIntegrable (μ := volume) 0 1),
    (weight_endpoints hm).1, (weight_endpoints hm).2]
  ring

/-- Integration by parts for the elementary main term of psi one. -/
theorem integral_main_weightD {m : ℕ} (hm : 0 < m) (c d : ℝ) :
    (∫ t in (0 : ℝ)..1,
      ((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t) =
      -d * (∫ t in (0 : ℝ)..1, ((c + d * t) - Real.log (2 * π)) * weight m t) := by
  let F : ℝ → ℝ := fun t => (c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)
  have hFd : ∀ t : ℝ, HasDerivAt F (d * ((c + d * t) - Real.log (2 * π))) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => c + d * t) d t := by
      simpa using ((hasDerivAt_id t).const_mul d).const_add c
    convert ((hlin.pow 2).div_const 2).sub (hlin.mul_const (Real.log (2 * π))) using 1 <;> ring
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (by fun_prop : ContinuousOn F (uIcc (0 : ℝ) 1)) (weight_continuous m).continuousOn
    (fun t _ => hFd t) (fun t _ => weight_hasDerivAt m t)
    ((by fun_prop : Continuous (fun t : ℝ => d * ((c + d * t) - Real.log (2 * π)))).intervalIntegrable _ _)
    ((weightD_continuous m).intervalIntegrable (μ := volume) 0 1)
  rw [(weight_endpoints hm).1, (weight_endpoints hm).2] at h
  simp only [mul_zero, sub_self, zero_sub] at h
  change (∫ t in (0 : ℝ)..1, F t * weightD m t) = _
  rw [h]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The actual psi integral equals the main term minus the convergent zero kernel
and one half of the logarithmic integral. The standard constant comes from the imported psi-one formula. -/
theorem integral_psi_explicit {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 2 < c) (hd : 0 < d) :
    (∫ t in (0 : ℝ)..1, Chebyshev.psi (c + d * t) * weight m t) =
      (∫ t in (0 : ℝ)..1, ((c + d * t) - Real.log (2 * π)) * weight m t) -
      (∑' ρ : Zall,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
          (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ) *
            (weight m t : ℂ))).re -
      (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (c + d * t) ^ 2) * weight m t) / 2 := by
  have hc0 : 0 < c := by linarith
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 2 < c + d * t := by
    intro t ht
    nlinarith [mul_nonneg hd.le ht.1]
  have hZc : ContinuousOn (fun t : ℝ => Zreal (c + d * t)) (Icc 0 1) := by
    unfold Zreal
    exact Complex.continuous_re.comp_continuousOn
      ((by fun_prop : ContinuousOn (fun t : ℝ => ((c + d * t : ℝ) : ℂ)) (Icc 0 1)).mul
        (continuousOn_zterm_sum hc0 hd.le))
  have hTc : ContinuousOn (fun t : ℝ => (c + d * t) * ∑' n : ℕ, tb (c + d * t) n) (Icc 0 1) := by
    intro t ht
    exact (ContinuousAt.comp (f := fun s : ℝ => c + d * s) (x := t)
      (hasDerivAt_trivial_series (hp t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => c + d * t) t)).continuousWithinAt
  have hwd : ContinuousOn (weightD m) (Icc (0 : ℝ) 1) := (weightD_continuous m).continuousOn
  have hZi : IntervalIntegrable (fun t : ℝ => Zreal (c + d * t) * weightD m t) volume 0 1 :=
    (hZc.mul hwd).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hTi : IntervalIntegrable (fun t : ℝ => ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t) volume 0 1 :=
    (hTc.mul hwd).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hMi := (by unfold weightD; fun_prop : Continuous (fun t : ℝ =>
    ((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t)).intervalIntegrable (μ := volume) 0 1
  have hCi := ((weightD_continuous m).const_mul
    ((deriv riemannZeta (-1) / riemannZeta (-1)).re)).intervalIntegrable (μ := volume) 0 1
  have hform : (∫ t in (0 : ℝ)..1, psi1 (c + d * t) * weightD m t) =
      (∫ t in (0 : ℝ)..1,
        ((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t) -
      (∫ t in (0 : ℝ)..1, Zreal (c + d * t) * weightD m t) -
      (∫ t in (0 : ℝ)..1, ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
        ((((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t -
          Zreal (c + d * t) * weightD m t) +
          (deriv riemannZeta (-1) / riemannZeta (-1)).re * weightD m t) -
          ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        dsimp only
        rw [psi1_formula (by linarith [hp t ht])]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hMi.sub hZi).add hCi) hTi,
          intervalIntegral.integral_add (hMi.sub hZi) hCi,
          intervalIntegral.integral_sub hMi hZi,
          intervalIntegral.integral_const_mul, integral_weightD_zero hm]
        ring
  have htransfer := integral_psi_affine_weight hm hc0 hd
  rw [hform, integral_main_weightD hm c d,
    integral_Zreal_weightD hm hc0 hd.le, integral_trivial_weightD hm hc hd.le] at htransfer
  apply (mul_left_cancel₀ hd.ne')
  nlinarith [htransfer]

end LeanLab.KadiriLumley2014.Task259
