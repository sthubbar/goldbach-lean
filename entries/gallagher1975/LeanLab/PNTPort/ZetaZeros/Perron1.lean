module

public import Mathlib

/-!
# The Riesz kernel of `ψ₁`: `𝓜[max(0, 1 - x)](s) = 1/(s(s + 1))`

Lab proof, unit U-5274, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
no cited input. The Mellin pair behind the explicit formula for
`ψ₁(x) = Σ_{n ≤ x} Λ(n)(x - n)`: with `w₁(x) = max(0, 1 - x)`, `𝓜 w₁ (s) = 1/(s(s + 1))` for
`Re s > 0`, so by Mathlib's `mellinInv_mellin_eq`,
`w₁(y) = (1/2π) ∫ y^{-(σ + it)} / ((σ + it)(σ + it + 1)) dt` for `y > 0`, `σ > 0`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter MeasureTheory
open scoped Real

/-- `w₁(x) = max(0, 1 - x)`. -/
noncomputable def w1 (x : ℝ) : ℝ := max 0 (1 - x)

lemma w1_continuous : Continuous w1 := by unfold w1; fun_prop

lemma w1_eq_zero {x : ℝ} (hx : 1 ≤ x) : w1 x = 0 := by unfold w1; simp; linarith

lemma w1_eq {x : ℝ} (hx : x ≤ 1) : w1 x = 1 - x := by unfold w1; simp; linarith

/-- `∫_{Ioi 0} t^{s-1} w₁(t) = ∫_0^1 t^{s-1}(1 - t)`. -/
lemma mellin_w1_eq_interval (s : ℂ) :
    mellin (fun x ↦ (w1 x : ℂ)) s = ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * (1 - t) := by
  unfold mellin
  rw [intervalIntegral.integral_of_le zero_le_one]
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    (f := fun t : ℝ => (t : ℂ) ^ (s - 1) • (w1 t : ℂ)) measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0) (fun t ht => by
      have : 1 < t := by
        simp only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le] at ht; exact ht.2 ht.1
      simp [w1_eq_zero this.le])
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only [smul_eq_mul]
  rw [w1_eq ht.2]; push_cast; ring

/-- **`𝓜 w₁ (s) = 1/(s(s + 1))`** for `Re s > 0`. -/
theorem mellin_w1 {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x ↦ (w1 x : ℂ)) s = 1 / (s * (s + 1)) := by
  rw [mellin_w1_eq_interval]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp at this; linarith
  have e : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * (1 - t) =
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1)) - ∫ t in (0 : ℝ)..1, (t : ℂ) ^ s := by
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht _
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      rw [mul_sub, mul_one]
      congr 1
      rw [show (t : ℂ) ^ s = (t : ℂ) ^ (s - 1 + 1) by ring_nf, cpow_add _ _ ht', cpow_one]
    · exact intervalIntegral.intervalIntegrable_cpow' (by rw [sub_re, one_re]; linarith)
    · exact intervalIntegral.intervalIntegrable_cpow' (by linarith)
  rw [e, integral_cpow (Or.inl (by rw [sub_re, one_re]; linarith)),
    integral_cpow (Or.inl (by linarith))]
  simp only [ofReal_one, one_cpow, ofReal_zero, sub_add_cancel]
  rw [zero_cpow hs0, zero_cpow hs1]
  field_simp
  ring

lemma w1_mellinConvergent {σ : ℝ} (hσ : 0 < σ) : MellinConvergent (fun x ↦ (w1 x : ℂ)) σ := by
  unfold MellinConvergent
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hii : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) * (w1 t : ℂ)) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)).mul_continuousOn
        (Complex.continuous_ofReal.comp w1_continuous).continuousOn
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hii
    simpa [smul_eq_mul] using hii
  · refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [w1_eq_zero (le_of_lt ht)]

lemma norm_inv_kernel_le {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    ‖1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))‖ ≤ (1 + t ^ 2)⁻¹ := by
  have h1 : 1 + t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]; nlinarith
  have h2 : ‖(σ : ℂ) + t * I‖ ≤ ‖(σ : ℂ) + t * I + 1‖ := by
    rw [show (σ : ℂ) + t * I + 1 = ((σ + 1 : ℝ) : ℂ) + t * I by push_cast; ring]
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]; nlinarith
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [norm_div, norm_one, norm_mul, one_div]
  apply inv_anti₀ hpos
  calc 1 + t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := h1
    _ = ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I‖ := by ring
    _ ≤ ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖ := by gcongr

lemma kernel_continuous {σ : ℝ} (hσ : 1 ≤ σ) :
    Continuous fun t : ℝ => 1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
  apply Continuous.div continuous_const (by fun_prop)
  intro t h
  rcases mul_eq_zero.mp h with h | h
  · have := congr_arg Complex.re h; simp at this; linarith
  · have := congr_arg Complex.re h; simp at this; linarith

lemma kernel_integrable {σ : ℝ} (hσ : 1 ≤ σ) :
    Integrable fun t : ℝ => 1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) :=
  Integrable.mono' integrable_inv_one_add_sq (kernel_continuous hσ).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_inv_kernel_le hσ t)

/-- **Inversion**: `w₁(y) = (1/2π) ∫ y^{-(σ + it)} / ((σ + it)(σ + it + 1)) dt`, `y > 0`, `σ ≥ 1`. -/
theorem w1_inversion {σ : ℝ} (hσ : 1 ≤ σ) {y : ℝ} (hy : 0 < y) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * I)) *
      (1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))) = w1 y := by
  have hre : ∀ t : ℝ, 0 < ((σ : ℂ) + t * I).re := fun t => by simp; linarith
  have hF : (fun t : ℝ => mellin (fun x ↦ (w1 x : ℂ)) ((σ : ℂ) + t * I)) =
      fun t : ℝ => 1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
    funext t; exact mellin_w1 (hre t)
  have hinv := mellinInv_mellin_eq σ (fun x ↦ (w1 x : ℂ)) hy
    (w1_mellinConvergent (by linarith))
    (by unfold VerticalIntegrable; rw [hF]; exact kernel_integrable hσ)
    ((Complex.continuous_ofReal.comp w1_continuous).continuousAt)
  unfold mellinInv at hinv
  rw [← hinv]
  simp only [smul_eq_mul]
  congr 1
  · simp only [one_div, mul_inv_rev]
    exact (by push_cast; ring : (π : ℂ)⁻¹ * 2⁻¹ = ((π⁻¹ * 2⁻¹ : ℝ) : ℂ))
  · congr 1; funext t; rw [mellin_w1 (hre t)]

open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- The kernel `K(t) = 1/((σ + it)(σ + it + 1))`. -/
noncomputable def Kσ (σ t : ℝ) : ℂ := 1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))

lemma cpow_div_eq {n x : ℝ} (hn : 0 < n) (hx : 0 < x) (s : ℂ) :
    ((n / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, mul_cpow_ofReal_nonneg hn.le (inv_nonneg.mpr hx.le),
    Complex.ofReal_inv, inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, cpow_neg, inv_inv, div_eq_inv_mul, mul_comm]

/-- **The Perron identity for `ψ₁`**: for `x > 0`, `σ > 1`,
`Σ Λ(n) w₁(n/x) = (1/2π) ∫ L(Λ, σ + it) x^{σ + it} / ((σ + it)(σ + it + 1)) dt`. -/
theorem psi1_perron {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (Λ n : ℂ) * w1 (n / x) =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, L ↗Λ ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) * Kσ σ t := by
  set F : ℕ → ℝ → ℂ := fun n t => (Λ n : ℂ) * (((n / x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * Kσ σ t)
    with hF
  have hKint : Integrable (fun t : ℝ => Kσ σ t) := kernel_integrable hσ.le
  have hnormF : ∀ n t, ‖F n t‖ = Λ n * ((n / x : ℝ) ^ (-σ)) * ‖Kσ σ t‖ := by
    intro n t
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [hF, h0]
    have hnx : 0 < (n / x : ℝ) := div_pos (by exact_mod_cast hpos) hx
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnx]
    simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_self, add_zero]
    ring
  have hint : ∀ n, Integrable (F n) := by
    intro n
    have hc : Continuous fun t : ℝ => ((n / x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp only [CharP.cast_eq_zero, zero_div, ofReal_zero]
        apply continuous_const.congr; intro t
        rw [zero_cpow]; intro h; have := congr_arg Complex.re h; simp at this; linarith
      · have hnx : (((n / x : ℝ)) : ℂ) ≠ 0 := by
          exact_mod_cast (div_pos (by exact_mod_cast hpos) hx).ne'
        exact Continuous.const_cpow (by fun_prop) (Or.inl hnx)
    have hb : Integrable fun t : ℝ => ((n / x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * Kσ σ t := by
      refine hKint.bdd_mul (c := (n / x : ℝ) ^ (-σ) + 1) hc.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp only [CharP.cast_eq_zero, zero_div, ofReal_zero]
        rw [zero_cpow (by intro h; have := congr_arg Complex.re h; simp at this; linarith),
          norm_zero]; positivity
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (by exact_mod_cast hpos) hx)]
        simp
    exact hb.const_mul _
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hnormF, integral_const_mul]
    apply Summable.mul_right
    have hΛ := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
      (by simp only [ofReal_re]; linarith)).norm
    refine (hΛ.mul_left (x ^ σ)).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    rw [LSeries.term_of_ne_zero hpos.ne', norm_div, norm_natCast_cpow_of_pos hpos,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      ofReal_re, Real.div_rpow (by positivity) hx.le, Real.rpow_neg (by positivity),
      Real.rpow_neg hx.le]
    field_simp
  have key := integral_tsum_of_summable_integral_norm hint hsum
  -- the left side
  have hl : ∀ n, ∫ t, F n t = (2 * π : ℂ) * ((Λ n : ℂ) * w1 (n / x)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [hF, h0]
    have hinv := w1_inversion hσ.le (y := n / x) (div_pos (by exact_mod_cast hpos) hx)
    simp only [hF, integral_const_mul]
    have h2π : (2 * π : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    rw [← hinv]
    unfold Kσ
    field_simp
    congr 2; funext t; ring_nf
  -- the right side
  have hr : ∀ t : ℝ, ∑' n, F n t = L ↗Λ ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) * Kσ σ t := by
    intro t
    simp only [hF, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    rw [LSeries.term_of_ne_zero hpos.ne', cpow_div_eq (by exact_mod_cast hpos) hx]
    push_cast
    ring
  simp_rw [hl, hr] at key
  rw [tsum_mul_left] at key
  rw [← key]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  field_simp

/-- The same with `-ζ'/ζ`: `Σ Λ(n) w₁(n/x) = (1/2π) ∫ -ζ'/ζ(s) x^s / (s(s + 1)) dt` on
`Re s = σ > 1`; note `x Σ Λ(n) w₁(n/x) = Σ_{n ≤ x} Λ(n)(x - n) = ψ₁(x)`. -/
theorem psi1_perron_zeta {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (Λ n : ℂ) * w1 (n / x) =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, -deriv riemannZeta ((σ : ℂ) + t * I) /
        riemannZeta ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) * Kσ σ t := by
  rw [psi1_perron hx hσ]
  congr 2; funext t
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp; linarith)]

end LeanLab.PNTPort.ZetaZeros

