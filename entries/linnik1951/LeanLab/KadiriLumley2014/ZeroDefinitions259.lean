module

public import LeanLab.KadiriLumley2014.G92

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equations 2.18 and 2.19.
Sealed declarations moved unchanged from Decomp92 to break the proof import cycle.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The enlarged Brun Titchmarsh coefficient used in page 3 equation 2.7. -/
noncomputable def tailCoefficient (δ u X : ℝ) : ℝ :=
  2 * (1 + δ) * (Real.exp u - 1) *
    (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) * X

/-- The absolute zero summand from page 4 equation 2.19, with multiplicity.
The index contains exactly the nontrivial zeros in the open critical strip. -/
noncomputable def zeroSummand (m : ℕ) (δ u X : ℝ)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖ *
    X ^ ((ρ : ℂ).re - 1)

/-- The nonnegative absolute zero sum Sigma in page 4 equation 2.19.
Summability is stated explicitly in the following analytic leaf. -/
noncomputable def zeroError (m : ℕ) (δ u X : ℝ) : ℝ :=
  ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}, zeroSummand m δ u X ρ

/-- Every absolute zero summand is nonnegative for nonnegative X. -/
theorem zeroSummand_nonneg (m : ℕ) (δ u : ℝ) {X : ℝ} (hX : 0 ≤ X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    0 ≤ zeroSummand m δ u X ρ := by
  unfold zeroSummand
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (Real.rpow_nonneg hX _)

/-- The absolute zero term decreases with X because every real part is below one. -/
theorem zeroSummand_antitone (m : ℕ) (δ u : ℝ) {X0 X : ℝ}
    (hX0 : 0 < X0) (hX : X0 ≤ X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    zeroSummand m δ u X ρ ≤ zeroSummand m δ u X0 ρ := by
  unfold zeroSummand
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hX0 hX (by linarith [ρ.property.2.2]))
  positivity

/-- Page 4 after equation 2.18. Replacing X by X0 is valid for the actual
absolute zero sum. This implication is conditional on summability at X0. -/
theorem zeroError_antitone (m : ℕ) (δ u : ℝ) {X0 X : ℝ}
    (hX0 : 0 < X0) (hX : X0 ≤ X) (hs : Summable (zeroSummand m δ u X0)) :
    Summable (zeroSummand m δ u X) ∧ zeroError m δ u X ≤ zeroError m δ u X0 := by
  have hsX : Summable (zeroSummand m δ u X) :=
    Summable.of_nonneg_of_le (zeroSummand_nonneg m δ u (hX0.le.trans hX))
      (zeroSummand_antitone m δ u hX0 hX) hs
  exact ⟨hsX, hsX.tsum_le_tsum (zeroSummand_antitone m δ u hX0 hX) hs⟩

end LeanLab.KadiriLumley2014.Task92
