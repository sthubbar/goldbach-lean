module

public import LeanLab.KadiriLumley2014.ZeroTermParts301
public import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equation 2.15.
Continuity and integration by parts for the actual nontrivial-zero series.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Real Set MeasureTheory
open Task64 Task301
open LeanLab.PNTPort.ExplicitPsi1
open LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- The actual integrated zero sum is continuous on each positive affine interval. -/
theorem continuousOn_zterm_sum {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    ContinuousOn (fun t : ℝ => ∑' ρ : Zall, zterm (c + d * t) ρ) (Icc 0 1) := by
  refine continuousOn_tsum (fun ρ => ?_)
    (summable_hw.mul_left ((c + d) ^ 2 + c ^ (-1 / 2 : ℝ)))
    (fun ρ t ht => norm_zterm_on_affine c d hc hd ρ ht)
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 0 < c + d * t := by
    intro t ht
    nlinarith [mul_nonneg hd ht.1]
  apply ContinuousOn.const_mul
  apply ContinuousOn.div_const
  intro t ht
  have h : ContinuousAt (fun z : ℂ => z ^ (ρ : ℂ)) ((c + d * t : ℝ) : ℂ) :=
    continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (hp t ht))
  exact (ContinuousAt.comp (f := fun s : ℝ => ((c + d * s : ℝ) : ℂ)) (x := t) h
    (by fun_prop : ContinuousAt (fun t : ℝ => ((c + d * t : ℝ) : ℂ)) t)).continuousWithinAt

/-- Every continuous weight gives an absolutely convergent family of integrated zero terms. -/
theorem summable_integral_zterm {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d)
    (q : ℝ → ℂ) (hq : Continuous q) :
    Summable (fun ρ : Zall => ∫ t in (0 : ℝ)..1, zterm (c + d * t) ρ * q t) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hq.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (q 0)).trans (hM 0 ⟨le_rfl, by norm_num⟩)
  let C : ℝ := ((c + d) ^ 2 + c ^ (-1 / 2 : ℝ)) * M
  have hB : 0 ≤ (c + d) ^ 2 + c ^ (-1 / 2 : ℝ) := by positivity
  apply Summable.of_norm_bounded (summable_hw.mul_left C)
  intro ρ
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖zterm (c + d * t) ρ * q t‖ ≤ C * hw ρ := by
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [norm_mul]
    have hb := mul_le_mul (norm_zterm_on_affine c d hc hd ρ ht') (hM t ht')
      (norm_nonneg _) (mul_nonneg hB (hw_nonneg ρ))
    convert hb using 1
    dsimp [C]
    ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- The psi zero kernels are summable after one polynomial integration by parts. -/
theorem summable_psi_zero_kernel {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    Summable (fun ρ : Zall =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
        (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ) *
          (weight m t : ℂ))) := by
  have hs := summable_integral_zterm hc hd.le
    (fun t : ℝ => ((c + d * t : ℝ) : ℂ) * (weightD m t : ℂ)) (by unfold weightD; fun_prop)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs' := hs.mul_left (-(d : ℂ))⁻¹
  apply hs'.congr
  intro ρ
  have hp := integral_zterm_weightD hm c d hc hd.le ρ
  have heq : (∫ t in (0 : ℝ)..1,
      zterm (c + d * t) ρ * (((c + d * t : ℝ) : ℂ) * (weightD m t : ℂ))) =
      (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) * zterm (c + d * t) ρ * (weightD m t : ℂ)) := by
    congr 1
    funext t
    ring
  rw [heq, hp]
  field_simp

/-- Weighted integration by parts for the actual integrated nontrivial-zero sum. -/
theorem integral_Zreal_weightD {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) :
    (∫ t in (0 : ℝ)..1, Zreal (c + d * t) * weightD m t) =
      -(d * (∑' ρ : Zall,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
          (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ) *
            (weight m t : ℂ))).re) := by
  let q : ℝ → ℂ := fun t => ((c + d * t : ℝ) : ℂ) * (weightD m t : ℂ)
  have hq : Continuous q := by dsimp [q]; unfold weightD; fun_prop
  have hcont := ((continuousOn_zterm_sum hc hd).mul
    (by fun_prop : ContinuousOn q (Icc (0 : ℝ) 1)))
  have hi := hcont.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  have hex := integral_zterm_tsum_continuous c d hc hd q hq
  have hparts : (∑' ρ : Zall, ∫ t in (0 : ℝ)..1, zterm (c + d * t) ρ * q t) =
      -(d : ℂ) * (∑' ρ : Zall,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
          (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ) *
            (weight m t : ℂ))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro ρ
    have hp := integral_zterm_weightD hm c d hc hd ρ
    convert hp using 1
    · congr 1
      funext t
      dsimp [q]
      ring
    · ring
  calc
    _ = (∫ t in (0 : ℝ)..1, ((∑' ρ : Zall, zterm (c + d * t) ρ) * q t).re) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [Zreal, q]
      simp [Complex.mul_re]
      ring
    _ = ((∫ t in (0 : ℝ)..1, (∑' ρ : Zall, zterm (c + d * t) ρ) * q t)).re := hre
    _ = _ := by rw [hex, hparts]; simp

end LeanLab.KadiriLumley2014.Task259
