module

public import LeanLab.KadiriLumley2014.ExplicitBase259
public import LeanLab.KadiriLumley2014.ZeroParts259
public import LeanLab.PNTPort.ExplicitPsi1.Nontrivial

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equations 2.16 to 2.19.
Normalization of the actual convergent psi zero kernels.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Real Set MeasureTheory
open Task64 Task92 Task301
open LeanLab.PNTPort.ExplicitPsi1

/-- A positive real exponential raised to a complex power is the complex exponential. -/
theorem cpow_real_exp (u : ℝ) (s : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ s = Complex.exp (s * u) := by
  have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero u
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_nonneg u), Real.log_exp]
  congr 1
  ring

/-- The difference of one upper and lower raw zero kernel is the normalized G contribution. -/
theorem psi_kernel_difference (m : ℕ) {δ u X : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hX : 0 < X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
      (∫ t in (0 : ℝ)..1,
        ((Real.exp u * X * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ) * (weight m t : ℂ)) -
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
      (∫ t in (0 : ℝ)..1, ((X * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ) * (weight m t : ℂ)) =
    (((Real.exp u - 1) * X * (∫ t in (0 : ℝ)..1, weight m t) : ℝ) : ℂ) *
      complexZeroSummand m δ u X ρ := by
  rw [integral_cpow_scale m hδ (mul_pos (Real.exp_pos u) hX), integral_cpow_scale m hδ hX,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_nonneg u) hX.le,
    cpow_real_exp]
  have hs := complexZeroSummand_scaled m δ hu hX ρ
  have hmC : ((∫ t in (0 : ℝ)..1, weight m t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (weight_mass_pos m).ne'
  unfold weightTransform at hs
  have hh := congrArg (fun z : ℂ => z * ((∫ t in (0 : ℝ)..1, weight m t : ℝ) : ℂ)) hs
  push_cast at hh ⊢
  field_simp at hh
  linear_combination -hh

/-- The raw scaled psi zero family is summable for every positive smoothing width. -/
theorem summable_scaled_psi_kernel {m : ℕ} (hm : 0 < m) {δ X : ℝ}
    (hδ : 0 < δ) (hX : 0 < X) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
        (∫ t in (0 : ℝ)..1, ((X * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ) *
          (weight m t : ℂ))) := by
  have h := summable_psi_zero_kernel hm hX (mul_pos hX hδ)
  have hlin : ∀ t : ℝ, X + X * δ * t = X * (1 + δ * t) := by intro t; ring
  simp_rw [hlin] at h
  rw [Zall_eq] at h
  exact h

/-- The normalized complex zero family is summable without any cited numerical zero input. -/
theorem complex_zero_summable {m : ℕ} (hm : 0 < m) {δ u X : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hX : 0 < X) :
    Summable (complexZeroSummand m δ u X) := by
  have hU := summable_scaled_psi_kernel hm hδ (mul_pos (Real.exp_pos u) hX)
  have hL := summable_scaled_psi_kernel hm hδ hX
  let C : ℂ := (((Real.exp u - 1) * X * (∫ t in (0 : ℝ)..1, weight m t) : ℝ) : ℂ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (mul_pos (mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)) hX)
      (weight_mass_pos m)).ne'
  have h := (hU.sub hL).mul_left C⁻¹
  apply h.congr
  intro ρ
  rw [psi_kernel_difference m hδ.le hu hX ρ]
  change C⁻¹ * (C * complexZeroSummand m δ u X ρ) = _
  rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]

/-- The absolute zero family is summable from the existing integrated-formula majorant. -/
theorem absolute_zero_summable {m : ℕ} (hm : 0 < m) {δ u X : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hX : 0 < X) :
    Summable (zeroSummand m δ u X) := by
  simpa only [norm_complexZeroSummand m δ u hX] using
    (complex_zero_summable hm hδ hu hX).norm

end LeanLab.KadiriLumley2014.Task259
