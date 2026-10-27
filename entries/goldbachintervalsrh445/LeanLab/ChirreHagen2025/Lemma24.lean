module

public import Mathlib
public import LeanLab.ChirreHagen2025.SmoothTheorem2

/-!
P0075, unit U-6357, track T1 for the paper and T2 for I-5170, CLOUD 20261020T1125Z-cloud41,
2026-10-20. Chirre-Hagen Lemma 2.5, the TeX label 4_24pm; the file name says 2.4 by an early slip: for `0 < δ ≤ 1` and real `γ ≠ 0`, with `ρ = 1/2 + iγ`,
`|((1+δ)^ρ - 1)/ρ| ≤ min(δ, ℓ/|γ|)`, `ℓ = √(1+δ) + 1`. First bound: the quotient is
`∫_1^{1+δ} t^{ρ-1} dt` and `|t^{ρ-1}| = t^{-1/2} ≤ 1`. Second: `|(1+δ)^ρ| = √(1+δ)` and
`|ρ| ≥ |γ|`. So `CoefBound` of SmoothTheorem2.lean holds, and `theorem2_smooth_of` drops it.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.SmoothT2
open Complex

variable {ι : Type*}

theorem coef_le_delta {δ : ℝ} (hδ : 0 < δ) (γ' : ι → ℝ) (i : ι) :
    ‖cδ γ' δ i‖ ≤ δ := by
  have hρ : rho γ' i - 1 + 1 = rho γ' i := by ring
  have hre : -1 < (rho γ' i - 1).re := by simp [rho]
  have hint := integral_cpow (a := 1) (b := 1 + δ) (Or.inl hre)
  rw [hρ] at hint
  have hρ0 : rho γ' i ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [rho] at this
  have e : cδ γ' δ i = ∫ x : ℝ in (1 : ℝ)..1 + δ, (x : ℂ) ^ (rho γ' i - 1) := by
    rw [hint]; unfold cδ; push_cast; simp
  rw [e]
  have hb : ∀ x ∈ Set.uIoc (1 : ℝ) (1 + δ), ‖(x : ℂ) ^ (rho γ' i - 1)‖ ≤ 1 := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1])
    simp [rho]; norm_num
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (by linarith)] at this
  simpa using this

theorem coef_le_ell {δ : ℝ} (hδ : 0 < δ) (γ : ι → ℝ) (i : ι) (hγ : γ i ≠ 0) :
    ‖cδ γ δ i‖ ≤ Local36.ell δ / |γ i| := by
  have hρ0 : rho γ i ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [rho] at this
  unfold cδ
  rw [norm_div]
  have hpos : (0 : ℝ) < 1 + δ := by linarith
  have hnum : ‖((1 + δ : ℝ) : ℂ) ^ rho γ i - 1‖ ≤ Local36.ell δ := by
    calc ‖((1 + δ : ℝ) : ℂ) ^ rho γ i - 1‖ ≤ ‖((1 + δ : ℝ) : ℂ) ^ rho γ i‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = √(1 + δ) + 1 := by
          rw [norm_cpow_eq_rpow_re_of_pos hpos, Real.sqrt_eq_rpow]
          simp [rho]
      _ = Local36.ell δ := rfl
  have hden : |γ i| ≤ ‖rho γ i‖ := by
    have := Complex.abs_im_le_norm (rho γ i)
    simpa [rho] using this
  have hg : 0 < |γ i| := abs_pos.mpr hγ
  have hl0 : 0 ≤ Local36.ell δ := by unfold Local36.ell; positivity
  calc ‖((1 + δ : ℝ) : ℂ) ^ rho γ i - 1‖ / ‖rho γ i‖ ≤ Local36.ell δ / ‖rho γ i‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ Local36.ell δ / |γ i| := div_le_div_of_nonneg_left hl0 hg hden

/-- The paper's Lemma 2.5. -/
theorem coefBound_of {γ : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (h14 : Ordinates14 γ) :
    CoefBound γ δ := by
  intro i
  have hγ : γ i ≠ 0 := by
    intro h; have := h14 i; rw [h, abs_zero] at this; norm_num at this
  exact le_min (coef_le_delta hδ γ i) (coef_le_ell hδ γ i hγ)

/-- Theorem 2 with 1.2913, CONDITIONAL ON ExplicitA, HadamardK, Lemma26 and Ordinates14. -/
theorem theorem2_smooth_of {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardK γ)
    (h14 : Ordinates14 γ) (hL : Lemma26 γ) :
    ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.2913 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 :=
  theorem2_smooth hE hH h14 (fun _ hδ _ => coefBound_of hδ h14) hL

end LeanLab.ChirreHagen2025.SmoothT2

