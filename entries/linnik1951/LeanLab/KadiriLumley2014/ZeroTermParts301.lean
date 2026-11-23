module

public import LeanLab.KadiriLumley2014.ZeroInterchange301
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equations 2.15 to 2.17.
The termwise integration by parts needed to recover the smoothing kernel.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64
open LeanLab.PNTPort.ExplicitPsi1

/-- Integrating a single psi-one zero term against the first weight derivative
recovers the corresponding psi zero kernel. -/
theorem integral_zterm_weightD {m : ℕ} (hm : 0 < m) (c d : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (ρ : Zall) :
    (∫ t in (0 : ℝ)..1,
      ((c + d * t : ℝ) : ℂ) * zterm (c + d * t) ρ * (weightD m t : ℂ)) =
      -((d : ℂ) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ)) *
        (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ) * (weight m t : ℂ)) := by
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have hz := ρ.property.1
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  have hρ1 : (ρ : ℂ) + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith [ρ.property.2]
  have hρneg : (ρ : ℂ) ≠ -1 := by
    intro h
    apply hρ1
    rw [h]
    ring
  have hRe : 0 < ((ρ : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [ρ.property.2]
  let H : ℝ → ℂ := fun t =>
    (((c + d * t : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) + 1)) *
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ)
  let C : ℂ := (d : ℂ) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ)
  have hy : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < c + d * t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    nlinarith [ht.1]
  have hHc : Continuous H := by
    exact ((((Complex.continuous_ofReal_cpow_const hRe).comp
      (by fun_prop : Continuous (fun t : ℝ => c + d * t))).div_const _).mul_const _).div_const _
  have hPc : ContinuousOn (fun t : ℝ => ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ)) (uIcc 0 1) := by
    intro t ht
    have hc' : ContinuousAt (fun z : ℂ => z ^ (ρ : ℂ)) ((c + d * t : ℝ) : ℂ) :=
      continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (hy t ht))
    exact (ContinuousAt.comp (f := fun s : ℝ => ((c + d * s : ℝ) : ℂ)) (x := t) hc'
      (by fun_prop : ContinuousAt (fun s : ℝ => ((c + d * s : ℝ) : ℂ)) t)).continuousWithinAt
  have hHd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt H (C * ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ)) t := by
    intro t ht
    have hlin : HasDerivAt (fun t : ℝ => c + d * t) d t := by
      simpa using ((hasDerivAt_id t).const_mul d).const_add c
    have hanti := (hasDerivAt_ofReal_cpow_const' (hy t ht).ne' hρneg).scomp t hlin
    simpa only [H, C, Function.comp_def, Complex.real_smul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (hanti.mul_const (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ)).div_const (ρ : ℂ)
  have hwc : Continuous (fun t : ℝ => (weight m t : ℂ)) :=
    Complex.continuous_ofReal.comp (weight_continuous m)
  have hwdc : Continuous (fun t : ℝ => (weightD m t : ℂ)) :=
    Complex.continuous_ofReal.comp (weightD_continuous m)
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hHc.continuousOn hwc.continuousOn
    (fun t ht => hHd t (by simpa using mem_Icc_of_Ioo ht))
    (fun t _ => (weight_hasDerivAt m t).ofReal_comp)
    ((hPc.const_mul C).intervalIntegrable) (hwdc.intervalIntegrable (μ := volume) 0 1)
  have hboundary : H 1 * (weight m 1 : ℂ) - H 0 * (weight m 0 : ℂ) = 0 := by
    rw [(weight_endpoints hm).1, (weight_endpoints hm).2]
    simp
  rw [hboundary, zero_sub] at hp
  calc
    _ = ∫ t in (0 : ℝ)..1, H t * (weightD m t : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hbase : ((c + d * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hy t ht).ne'
      dsimp only [H, zterm]
      rw [Complex.cpow_add _ _ hbase, Complex.cpow_one]
      field_simp
    _ = -(∫ t in (0 : ℝ)..1, (C * ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ)) * (weight m t : ℂ)) := hp
    _ = _ := by
      simp_rw [mul_assoc]
      rw [intervalIntegral.integral_const_mul]
      dsimp [C]
      ring

end LeanLab.KadiriLumley2014.Task301
