module

public import Mathlib

/-!
# Bounds for `Γ` on the strip `1/2 ≤ Re s ≤ 3/2`

Lab proof, unit U-5269, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics, no
cited input. A step toward a digamma bound `|ψ(σ + it)| ≪ log |t|`, which the left half of an
explicit formula with all zeros needs; Mathlib v4.35 has no growth bound for complex `Γ`.

* `norm_Gamma_strip_le`: `‖Γ(s)‖ ≤ Γ(1/2) + Γ(3/2)` for `1/2 ≤ Re s ≤ 3/2`.
* `normSq_Gamma_half`: `|Γ(1/2 + it)|² = π / cosh(πt)`, from the reflection formula.
* `norm_Gamma_half_mul_exp_le`: `|Γ(1/2 + it)| e^{πt/2} ≤ √(2π)`.
* `norm_Gamma_le_PL`: by Phragmén-Lindelöf, `‖Γ(s) e^{-iπs/2} / (s + 1)‖ ≤ √(2π)` on the strip,
  so `|Γ(σ + it)| ≤ √(2π) |s + 1| e^{-πt/2}`, the Stirling decay up to a polynomial factor.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter MeasureTheory
open scoped Real ComplexConjugate

/-- `‖Γ(s)‖ ≤ Γ(1/2) + Γ(3/2)` for `1/2 ≤ Re s ≤ 3/2`. -/
theorem norm_Gamma_strip_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖Gamma s‖ ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := by
  rw [Gamma_eq_integral (by linarith), GammaIntegral]
  have hI1 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
  have hI3 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 2)
  have hint := hI1.add hI3
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [Real.Gamma_eq_integral (by norm_num), Real.Gamma_eq_integral (by norm_num),
    ← integral_add hI1 hI3]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have he : 0 < Real.exp (-x) := Real.exp_pos _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
    Real.norm_of_nonneg he.le, ← mul_add]
  simp only [sub_re, one_re]
  gcongr
  rcases le_or_gt x 1 with hx1 | hx1
  · have : x ^ (s.re - 1) ≤ x ^ (1 / 2 - 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
    have : 0 ≤ x ^ (3 / 2 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith
  · have : x ^ (s.re - 1) ≤ x ^ (3 / 2 - 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have : 0 ≤ x ^ (1 / 2 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith

/-- `|Γ(1/2 + it)|² = π / cosh(πt)`. -/
theorem normSq_Gamma_half (t : ℝ) :
    ‖Gamma (1 / 2 + t * I)‖ ^ 2 = π / Real.cosh (π * t) := by
  have hrefl := Gamma_mul_Gamma_one_sub (1 / 2 + t * I)
  have hconj : (1 : ℂ) - (1 / 2 + t * I) = conj (1 / 2 + t * I) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [hconj, Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hrefl
  have hsin : Complex.sin (π * (1 / 2 + t * I)) = Real.cosh (π * t) := by
    rw [show (π : ℂ) * (1 / 2 + t * I) = π / 2 + (π * t : ℝ) * I by push_cast; ring,
      Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      Complex.ofReal_cosh]
    ring
  rw [hsin] at hrefl
  have : ((‖Gamma (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) = ((π / Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [hrefl]; push_cast; ring
  exact_mod_cast this

/-- `|Γ(1/2 + it)| e^{πt/2} ≤ √(2π)`. -/
theorem norm_Gamma_half_mul_exp_le (t : ℝ) :
    ‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2) ≤ √(2 * π) := by
  have h := normSq_Gamma_half t
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hsq : (‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2)) ^ 2 ≤ 2 * π := by
    rw [mul_pow, h, ← Real.exp_nat_mul]
    have e2 : ((2 : ℕ) : ℝ) * (π * t / 2) = π * t := by push_cast; ring
    rw [e2, div_mul_eq_mul_div, div_le_iff₀ hc, Real.cosh_eq]
    have := Real.exp_pos (-(π * t))
    have hp := Real.pi_pos
    nlinarith
  calc _ ≤ √((‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2)) ^ 2) := by
        rw [Real.sqrt_sq (by positivity)]
    _ ≤ √(2 * π) := Real.sqrt_le_sqrt hsq

/-- The function `g(s) = Γ(s) e^{-iπs/2} / (s + 1)`. -/
noncomputable def gPL (s : ℂ) : ℂ := Gamma s * Complex.exp (-(π * I * s / 2)) / (s + 1)

lemma norm_exp_PL (s : ℂ) : ‖Complex.exp (-(π * I * s / 2))‖ = Real.exp (π * s.im / 2) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

lemma norm_gPL_half (t : ℝ) : ‖gPL (1 / 2 + t * I)‖ ≤ √(2 * π) := by
  unfold gPL
  rw [norm_div, norm_mul, norm_exp_PL]
  have him : ((1 / 2 : ℂ) + t * I).im = t := by simp
  rw [him]
  have hden : 1 ≤ ‖(1 / 2 + t * I : ℂ) + 1‖ := by
    have := Complex.abs_re_le_norm ((1 / 2 + t * I : ℂ) + 1)
    have e : ((1 / 2 + t * I : ℂ) + 1).re = 3 / 2 := by simp; norm_num
    rw [e] at this; norm_num at this; linarith
  rw [div_le_iff₀ (by linarith)]
  have := norm_Gamma_half_mul_exp_le t
  have h0 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  nlinarith

lemma norm_gPL_three_half (t : ℝ) : ‖gPL (3 / 2 + t * I)‖ ≤ √(2 * π) := by
  unfold gPL
  have hG : Gamma (3 / 2 + t * I) = (1 / 2 + t * I) * Gamma (1 / 2 + t * I) := by
    rw [show (3 / 2 + t * I : ℂ) = (1 / 2 + t * I) + 1 by ring]
    exact Gamma_add_one _ (by intro h; have := congr_arg Complex.re h; simp at this)
  rw [hG, norm_div, norm_mul, norm_mul, norm_exp_PL]
  have him : ((3 / 2 : ℂ) + t * I).im = t := by simp
  rw [him]
  have hnum : ‖(1 / 2 + t * I : ℂ)‖ ≤ ‖(3 / 2 + t * I : ℂ) + 1‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp [Complex.normSq_apply]; nlinarith
  have hpos : 0 < ‖(3 / 2 + t * I : ℂ) + 1‖ := by
    apply norm_pos_iff.mpr; intro h; have := congr_arg Complex.re h; simp at this; norm_num at this
  rw [div_le_iff₀ hpos]
  have := norm_Gamma_half_mul_exp_le t
  have h0 : 0 ≤ ‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2) := by positivity
  calc ‖(1 / 2 + t * I : ℂ)‖ * ‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2)
      = ‖(1 / 2 + t * I : ℂ)‖ * (‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2)) := by ring
    _ ≤ ‖(3 / 2 + t * I : ℂ) + 1‖ * √(2 * π) := mul_le_mul hnum this h0 (norm_nonneg _)
    _ = √(2 * π) * ‖(3 / 2 + t * I : ℂ) + 1‖ := by ring

lemma gPL_differentiableAt {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ gPL z := by
  have hne : ∀ m : ℕ, z ≠ -m := by
    intro m h; rw [h] at hz; simp at hz; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : z + 1 ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  unfold gPL
  exact ((Complex.differentiableAt_Gamma z hne).mul
    (Complex.differentiableAt_exp.comp z (by fun_prop))).div (by fun_prop) h1

/-- **Phragmén-Lindelöf**: `‖Γ(s) e^{-iπs/2} / (s + 1)‖ ≤ √(2π)` for `1/2 ≤ Re s ≤ 3/2`. -/
theorem norm_gPL_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) : ‖gPL s‖ ≤ √(2 * π) := by
  have hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) ⊆ {z : ℂ | 0 < z.re} := by
    have hsub : re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (3 / 2) :=
      preimage_mono Ioo_subset_Icc_self
    have hcl' := closure_minimal hsub (isClosed_Icc.preimage continuous_re)
    intro z hz
    have := hcl' hz
    simp only [mem_preimage, mem_Icc] at this
    simp only [mem_setOf_eq]; linarith [this.1]
  have hfd : DiffContOnCl ℂ gPL (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) :=
    DifferentiableOn.diffContOnCl (fun z hz => (gPL_differentiableAt (hcl hz)).differentiableWithinAt)
  set K : ℝ := Real.Gamma (1 / 2) + Real.Gamma (3 / 2)
  have hB : ∃ c < π / ((3 / 2 : ℝ) - 1 / 2), ∃ B, gPL =O[comap (_root_.abs ∘ im) atTop ⊓
      𝓟 (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2))] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, by have := Real.pi_gt_three; norm_num; linarith, π / 2, ?_⟩
    refine Asymptotics.IsBigO.of_bound K ?_
    refine Filter.eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
    simp only [mem_preimage, mem_Ioo] at hz
    unfold gPL
    rw [norm_div, norm_mul, norm_exp_PL, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hG := norm_Gamma_strip_le (s := z) hz.1.le hz.2.le
    have hden : 1 ≤ ‖z + 1‖ := by
      have := Complex.abs_re_le_norm (z + 1); simp at this
      rw [abs_of_pos (by linarith)] at this; linarith
    have hK : 0 ≤ K := by
      have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      positivity
    have hexp : Real.exp (π * z.im / 2) ≤ Real.exp (π / 2 * Real.exp (1 * |z.im|)) := by
      apply Real.exp_le_exp.mpr
      have h1 : z.im ≤ |z.im| := le_abs_self _
      have h2 : |z.im| ≤ Real.exp (1 * |z.im|) := by
        rw [one_mul]; linarith [Real.add_one_le_exp |z.im|]
      have hp := Real.pi_pos
      nlinarith
    rw [div_le_iff₀ (by linarith)]
    calc ‖Gamma z‖ * Real.exp (π * z.im / 2) ≤ K * Real.exp (π / 2 * Real.exp (1 * |z.im|)) :=
          mul_le_mul hG hexp (Real.exp_pos _).le hK
      _ ≤ K * Real.exp (π / 2 * Real.exp (1 * |z.im|)) * ‖z + 1‖ := by
          have : 0 ≤ K * Real.exp (π / 2 * Real.exp (1 * |z.im|)) := by positivity
          nlinarith
  refine PhragmenLindelof.vertical_strip hfd hB (fun z hz => ?_) (fun z hz => ?_) h1 h2
  · have e : z = 1 / 2 + z.im * I := by apply Complex.ext <;> simp [hz]
    rw [e]; exact norm_gPL_half z.im
  · have e : z = 3 / 2 + z.im * I := by apply Complex.ext <;> simp [hz]
    rw [e]; exact norm_gPL_three_half z.im

/-- **`|Γ(s)| ≤ √(2π) |s + 1| e^{-π Im s / 2}`** for `1/2 ≤ Re s ≤ 3/2`. -/
theorem norm_Gamma_le_PL {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖Gamma s‖ ≤ √(2 * π) * ‖s + 1‖ * Real.exp (-(π * s.im / 2)) := by
  have h := norm_gPL_le h1 h2
  have hpos : 0 < ‖s + 1‖ := by
    apply norm_pos_iff.mpr; intro h0; have := congr_arg Complex.re h0; simp at this; linarith
  unfold gPL at h
  rw [norm_div, norm_mul, norm_exp_PL, div_le_iff₀ hpos] at h
  have he := Real.exp_pos (π * s.im / 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ he]
  linarith

end LeanLab.PNTPort.ZetaZeros

