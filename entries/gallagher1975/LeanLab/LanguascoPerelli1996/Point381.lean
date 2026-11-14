module

public import Mathlib

/-!
P0071 page 358 display 20, the elementary point control step.
Reference 9, Heath Brown 1982, pages 90 and 91, writes out the
Sobolev and Cauchy Schwarz mechanism used here.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Point381
open Real MeasureTheory intervalIntegral
open scoped ContDiff

/-- Page 358 display 20, the real Sobolev step on a symmetric interval.
A nonnegative smooth function at any point of the interval is at most
its mass divided by the radius plus its total variation. -/
theorem point_le_mass_div_add_variation {g g' : ℝ → ℝ}
    (hg : Continuous g) (hg' : Continuous g')
    (hd : ∀ t, HasDerivAt g (g' t) t) (hg0 : ∀ t, 0 ≤ g t)
    {ξ η : ℝ} (hξ : 0 < ξ) (hη : |η| ≤ ξ) :
    g η ≤ (∫ t in (-ξ)..ξ, g t) / ξ + (∫ t in (-ξ)..ξ, |g' t|) := by
  have hη' := abs_le.mp hη
  have hab : -ξ ≤ ξ := by linarith
  let V := ∫ t in (-ξ)..ξ, |g' t|
  have hp : ∀ t ∈ Set.Icc (-ξ) ξ, g η ≤ g t + V := by
    intro t ht
    by_cases hle : η ≤ t
    · have heq : (∫ u in η..t, g' u) = g t - g η :=
        integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hg'.intervalIntegrable _ _)
      have ha := abs_integral_le_integral_abs (f := g') (μ := volume) hle
      rw [heq] at ha
      have hm : (∫ u in η..t, |g' u|) ≤ V :=
        integral_mono_interval hη'.1 hle ht.2 (Filter.Eventually.of_forall fun u => abs_nonneg _)
          (hg'.abs.intervalIntegrable _ _)
      linarith [neg_le_abs (g t - g η)]
    · have hle' : t ≤ η := le_of_not_ge hle
      have heq : (∫ u in t..η, g' u) = g η - g t :=
        integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hg'.intervalIntegrable _ _)
      have ha := abs_integral_le_integral_abs (f := g') (μ := volume) hle'
      rw [heq] at ha
      have hm : (∫ u in t..η, |g' u|) ≤ V :=
        integral_mono_interval ht.1 hle' hη'.2 (Filter.Eventually.of_forall fun u => abs_nonneg _)
          (hg'.abs.intervalIntegrable _ _)
      linarith [le_abs_self (g η - g t)]
  have hint := integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable (-ξ) ξ)
    ((hg.add continuous_const).intervalIntegrable (-ξ) ξ) hp
  simp only [Pi.add_apply, integral_add (hg.intervalIntegrable (-ξ) ξ)
    (continuous_const.intervalIntegrable (-ξ) ξ), intervalIntegral.integral_const, smul_eq_mul] at hint
  have hmass : 0 ≤ ∫ t in (-ξ)..ξ, g t := integral_nonneg_of_forall hab hg0
  have hcalc : (g η - V) * ξ ≤ ∫ t in (-ξ)..ξ, g t := by nlinarith
  have hdiv := (le_div_iff₀ hξ).2 hcalc
  linarith

/-- Page 358 display 20, Cauchy Schwarz in L2 on a finite interval.
This exposes the standard Mathlib Holder inequality without a new analytic input. -/
theorem integral_mul_le_sqrt {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t) :
    (∫ t in a..b, f t * g t) ≤
      Real.sqrt (∫ t in a..b, f t ^ 2) * Real.sqrt (∫ t in a..b, g t ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hfmem : MemLp f (2 : ENNReal) (volume.restrict (Set.Ioc a b)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
      ((hf.pow 2).intervalIntegrable a b).1
  have hgmem : MemLp g (2 : ENNReal) (volume.restrict (Set.Ioc a b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
      ((hg.pow 2).intervalIntegrable a b).1
  have hh := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc a b)) hpq (ae_of_all _ hf0) (ae_of_all _ hg0)
    (by simpa using hfmem) (by simpa using hgmem)
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] at hh
  rw [integral_of_le hab, integral_of_le hab, integral_of_le hab,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hh

/-- Page 358 display 20 for any smooth complex function.
No arithmetic or correlation hypothesis is used in this point control step. -/
theorem point_control {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {ξ η : ℝ} (hξ : 0 < ξ) (hη : |η| ≤ ξ) :
    ‖f η‖ ^ 2 ≤ 2 * ((∫ t in (-ξ)..ξ, ‖f t‖ ^ 2) / ξ +
      Real.sqrt ((∫ t in (-ξ)..ξ, ‖f t‖ ^ 2) * (∫ t in (-ξ)..ξ, ‖deriv f t‖ ^ 2))) := by
  let g := fun t => ‖f t‖ ^ 2
  have hgc : ContDiff ℝ ∞ g := hf.norm_sq ℂ
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hgg : Continuous (deriv g) := hgc.continuous_deriv (by simp)
  have hb := point_le_mass_div_add_variation hgc.continuous hgg
    (fun t => (hgc.differentiable (by simp) t).hasDerivAt) (fun _ => sq_nonneg _) hξ hη
  have hderiv (t : ℝ) : |deriv g t| ≤ 2 * (‖f t‖ * ‖deriv f t‖) := by
    have hd := (hf.differentiable (by simp) t).hasDerivAt.norm_sq.deriv
    change deriv g t = 2 * inner (𝕜 := ℝ) (f t) (deriv f t) at hd
    rw [hd, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) _ _) (by norm_num)
  have hv := integral_mono_on (μ := volume) (show -ξ ≤ ξ by linarith)
    (hgg.abs.intervalIntegrable (-ξ) ξ)
    ((continuous_const.mul (hf.continuous.norm.mul hdc.norm)).intervalIntegrable (-ξ) ξ)
    (fun t _ => hderiv t)
  simp only [Pi.mul_apply] at hv
  rw [intervalIntegral.integral_const_mul] at hv
  have hcs := integral_mul_le_sqrt (show -ξ ≤ ξ by linarith)
    hf.continuous.norm hdc.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hm0 : 0 ≤ (∫ t in (-ξ)..ξ, ‖f t‖ ^ 2) :=
    integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  have hs : Real.sqrt ((∫ t in (-ξ)..ξ, ‖f t‖ ^ 2) *
      (∫ t in (-ξ)..ξ, ‖deriv f t‖ ^ 2)) =
      Real.sqrt (∫ t in (-ξ)..ξ, ‖f t‖ ^ 2) * Real.sqrt (∫ t in (-ξ)..ξ, ‖deriv f t‖ ^ 2) :=
    Real.sqrt_mul hm0 _
  dsimp only [g] at hb
  rw [hs]
  have hmdiv : 0 ≤ (∫ t in (-ξ)..ξ, ‖f t‖ ^ 2) / ξ := div_nonneg hm0 hξ.le
  linarith

end LeanLab.LanguascoPerelli1996.Point381

