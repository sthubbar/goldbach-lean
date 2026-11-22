module

public import LeanLab.KadiriLumley2014.CostaTransfer
public import LeanLab.KadiriLumley2014.Weight

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 pages 2 and 3, equations 2.4, 2.12 and 2.13.
Journal INTEGERS 14 A61 pages 3 and 4, equations 4, 12 and 13.
This uses the paper's polynomial weight and remains conditional on CostaEstimate.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The weighted theta difference from equation 2.4. -/
noncomputable def thetaAverage (m : ℕ) (δ u X : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1,
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t) /
    (∫ t in (0 : ℝ)..1, weight m t)

/-- The weighted psi difference from equation 2.12. -/
noncomputable def psiAverage (m : ℕ) (δ u X : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1,
    (Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.psi (X * (1 + δ * t))) * weight m t) /
    (∫ t in (0 : ℝ)..1, weight m t)

/-- Monotonicity gives the required interval integrability of a weighted
Chebyshev difference without assuming continuity at its prime power jumps. -/
theorem weighted_difference_integrable {F : ℝ → ℝ} (hF : Monotone F)
    (m : ℕ) {δ c X : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hX : 0 ≤ X) :
    IntervalIntegrable (fun t => (F (c * (X * (1 + δ * t))) -
      F (X * (1 + δ * t))) * weight m t) volume 0 1 := by
  have hsmall : Monotone (fun t : ℝ => X * (1 + δ * t)) := by
    intro s t hst
    apply mul_le_mul_of_nonneg_left _ hX
    nlinarith
  have hbig : Monotone (fun t : ℝ => c * (X * (1 + δ * t))) := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left (hsmall hst) hc
  exact ((hF.comp hbig).intervalIntegrable (a := 0) (b := 1)).sub
    ((hF.comp hsmall).intervalIntegrable (a := 0) (b := 1)) |>.mul_continuousOn (weight_continuous m).continuousOn

/-- Equation 2.13 for the polynomial weight.
This theorem is conditional on the cited CostaEstimate only. -/
theorem thetaAverage_ge_psiAverage_sub_omega (hCosta : CostaEstimate)
    (m : ℕ) {δ u X : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001)
    (hu : 0 ≤ u) (hu1 : u ≤ 0.0001) (hX : Real.exp 38 ≤ X) :
    psiAverage m δ u X - (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X ≤
      thetaAverage m δ u X := by
  have hX0 : 0 ≤ X := (Real.exp_pos 38).le.trans hX
  have hi := weighted_difference_integrable Chebyshev.theta_mono m hδ (Real.exp_nonneg u) hX0
  have hj := weighted_difference_integrable Chebyshev.psi_mono m hδ (Real.exp_nonneg u) hX0
  let C : ℝ := (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X
  have hk : IntervalIntegrable (fun t => C * weight m t) volume 0 1 :=
    ((weight_continuous m).intervalIntegrable 0 1).const_mul C
  have hdiff :
      (∫ t in (0 : ℝ)..1,
        ((Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) - Chebyshev.psi (X * (1 + δ * t))) -
          (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) - Chebyshev.theta (X * (1 + δ * t)))) * weight m t) ≤
        ∫ t in (0 : ℝ)..1, C * weight m t := by
    have hin := hj.sub hi
    simp_rw [← sub_mul] at hin
    apply intervalIntegral.integral_mono_on (by norm_num) hin hk
    intro t ht
    have hp := (costa_gap_lt_omega hCosta hu hu1 hδ hδ1 hX ht.1 ht.2).le
    have hp' :
        (Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) - Chebyshev.psi (X * (1 + δ * t))) -
          (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) - Chebyshev.theta (X * (1 + δ * t))) ≤ C := by
      dsimp [C]
      linarith
    exact mul_le_mul_of_nonneg_right hp' (weight_nonneg m ht)
  have heq : (fun t : ℝ =>
        ((Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) - Chebyshev.psi (X * (1 + δ * t))) -
          (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) - Chebyshev.theta (X * (1 + δ * t)))) * weight m t) =
      (fun t : ℝ =>
        (Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) - Chebyshev.psi (X * (1 + δ * t))) * weight m t -
          (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) - Chebyshev.theta (X * (1 + δ * t))) * weight m t) := by
    funext t
    ring
  rw [heq] at hdiff
  rw [intervalIntegral.integral_sub hj hi, intervalIntegral.integral_const_mul] at hdiff
  have hm := weight_mass_pos m
  unfold thetaAverage psiAverage
  dsimp [C] at hdiff
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hm).mpr
  rw [add_mul, div_mul_cancel₀ _ hm.ne']
  linarith

end LeanLab.KadiriLumley2014.Task64
