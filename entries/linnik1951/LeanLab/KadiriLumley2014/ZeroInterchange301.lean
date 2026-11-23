module

public import LeanLab.PNTPort.ExplicitPsi1.Final
public import LeanLab.KadiriLumley2014.WeightDerivative
public import Mathlib.Topology.Compactness.Lindelof

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equation 2.15 and the display before equation 2.16.
Uniform domination for transferring the lab's integrated explicit formula.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1

/-- The actual nontrivial-zero index of the integrated formula is countable. -/
theorem formula_zeros_countable : Zall.Countable := by
  have hz : riemannZetaZeros.Countable :=
    isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete isDiscrete_riemannZetaZeros
  exact hz.mono (fun z hz => hz.1)

/-- A single psi-one zero term has a uniform summable majorant on a positive bounded interval. -/
theorem norm_zterm_on_affine (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d)
    (ρ : Zall) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖zterm (c + d * t) ρ‖ ≤ ((c + d) ^ 2 + c ^ (-1 / 2 : ℝ)) * hw ρ := by
  have hy0 : 0 < c + d * t := by nlinarith [ht.1]
  have hyc : c ≤ c + d * t := by nlinarith [ht.1]
  have hycd : c + d * t ≤ c + d := by nlinarith [ht.2]
  have hsq : (c + d * t) ^ (2 : ℝ) ≤ (c + d) ^ 2 := by
    rw [Real.rpow_two]
    nlinarith
  have hneg : (c + d * t) ^ (-1 / 2 : ℝ) ≤ c ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hc hyc (by norm_num)
  apply (norm_zterm_le hy0 ρ.property).trans
  apply mul_le_mul_of_nonneg_right _ (hw_nonneg ρ)
  exact add_le_add hsq hneg

/-- A continuous weight with a unit-interval norm bound permits termwise integration
of the actual integrated-formula zero sum. No explicit formula identity is assumed. -/
theorem integral_zterm_tsum (c d M : ℝ) (hc : 0 < c) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (q : ℝ → ℂ) (hq : Continuous q) (hqM : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ M) :
    (∫ t in (0 : ℝ)..1, (∑' ρ : Zall, zterm (c + d * t) ρ) * q t) =
      ∑' ρ : Zall, ∫ t in (0 : ℝ)..1, zterm (c + d * t) ρ * q t := by
  classical
  haveI : Countable Zall := formula_zeros_countable.to_subtype
  let base : ℝ → ℝ := fun t => max c (c + d * t)
  have hbasepos : ∀ t, 0 < base t := fun t => hc.trans_le (le_max_left _ _)
  have hbaseeq : ∀ t ∈ Icc (0 : ℝ) 1, base t = c + d * t := by
    intro t ht
    apply max_eq_right
    nlinarith [ht.1]
  have hbasecont : Continuous base := by fun_prop
  let F : Zall → ℝ → ℂ := fun ρ t => zterm (base t) ρ * q t
  let B : ℝ := ((c + d) ^ 2 + c ^ (-1 / 2 : ℝ)) * M
  let bound : Zall → ℝ := fun ρ => B * hw ρ
  have hB : 0 ≤ (c + d) ^ 2 + c ^ (-1 / 2 : ℝ) := by positivity
  have hsum : Summable bound := summable_hw.mul_left B
  have hFcont : ∀ ρ, Continuous (F ρ) := by
    intro ρ
    have hp : Continuous (fun t : ℝ => ((base t : ℝ) : ℂ) ^ (ρ : ℂ)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hp' : ContinuousAt (fun z : ℂ => z ^ (ρ : ℂ)) ((base t : ℝ) : ℂ) :=
        continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (hbasepos t))
      have hb' : ContinuousAt (fun s : ℝ => ((base s : ℝ) : ℂ)) t :=
        Complex.continuous_ofReal.continuousAt.comp hbasecont.continuousAt
      simpa only [Function.comp_def] using
        (ContinuousAt.comp (f := fun s : ℝ => ((base s : ℝ) : ℂ)) (x := t) hp' hb')
    exact (((hp.div_const _).const_mul _).mul hq)
  have hbound : ∀ ρ t, t ∈ Icc (0 : ℝ) 1 → ‖F ρ t‖ ≤ bound ρ := by
    intro ρ t ht
    dsimp [F, bound, B]
    rw [norm_mul, hbaseeq t ht]
    have hn := norm_zterm_on_affine c d hc hd ρ ht
    have hh := mul_le_mul hn (hqM t ht) (norm_nonneg _) (mul_nonneg hB (hw_nonneg ρ))
    convert hh using 1 <;> ring
  have hlim : ∀ t : ℝ, HasSum (fun ρ : Zall => F ρ t)
      ((∑' ρ : Zall, zterm (base t) ρ) * q t) := by
    intro t
    exact (summable_zterm (hbasepos t)).hasSum.mul_right (q t)
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume) (fun ρ _t => bound ρ)
    (fun ρ => (hFcont ρ).aestronglyMeasurable)
    (fun ρ => ae_of_all _ (fun t ht => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact hbound ρ t ⟨ht.1.le, ht.2⟩))
    (ae_of_all _ (fun _t _ht => hsum)) intervalIntegrable_const
    (ae_of_all _ (fun t _ht => hlim t))
  calc
    _ = ∫ t in (0 : ℝ)..1, (∑' ρ : Zall, zterm (base t) ρ) * q t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      dsimp only
      rw [hbaseeq t ht]
    _ = ∑' ρ : Zall, ∫ t in (0 : ℝ)..1, F ρ t := hi.tsum_eq.symm
    _ = _ := tsum_congr (fun ρ => by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      dsimp [F]
      rw [hbaseeq t ht])

/-- Compactness supplies the norm bound for every continuous weight. -/
theorem integral_zterm_tsum_continuous (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d)
    (q : ℝ → ℂ) (hq : Continuous q) :
    (∫ t in (0 : ℝ)..1, (∑' ρ : Zall, zterm (c + d * t) ρ) * q t) =
      ∑' ρ : Zall, ∫ t in (0 : ℝ)..1, zterm (c + d * t) ρ * q t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hq.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (q 0)).trans (hM 0 ⟨le_rfl, by norm_num⟩)
  exact integral_zterm_tsum c d M hc hd hM0 q hq hM

/-- In particular the actual first derivative of the paper's weight permits the interchange. -/
theorem integral_zterm_tsum_weightD (m : ℕ) (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d) :
    (∫ t in (0 : ℝ)..1,
      (∑' ρ : Zall, zterm (c + d * t) ρ) * (Task64.weightD m t : ℂ)) =
      ∑' ρ : Zall, ∫ t in (0 : ℝ)..1, zterm (c + d * t) ρ * (Task64.weightD m t : ℂ) :=
  integral_zterm_tsum_continuous c d hc hd (fun t => (Task64.weightD m t : ℂ))
    (Complex.continuous_ofReal.comp (Task64.weightD_continuous m))

end LeanLab.KadiriLumley2014.Task301
