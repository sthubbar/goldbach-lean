module

public import LeanLab.Linnik.ExplicitFormula.Defs

/-!
# Perron step for the Cesaro kernel, Davenport ch. 17

AI wrote the Lean code. Binary Goldbach is OPEN.
`(1/2π) ∫ y^(-(c+it)) / ((c+it+1)(c+it+2)) dt = w(y)` for `y > 0`, `c > 0`, and hence
`S(x, χ) = (1/2π) ∫ F(2 + it) dt`, using `L(χΛ, s) = -L'/L(s, χ)` on `Re s > 1`.
Port target: `LeanLab.PNTPort.ZetaZeros.Perron1.psi1_perron` with the shift `s ↦ s + 1`,
and `LeanLab.PNTPort.PsiChi.SmoothedDirichlet.LSeries_chi_vonMangoldt_eq`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex MeasureTheory
open scoped Real


/-- Elementary: `w(y) = y max(0, 1 - y)`. -/
lemma wK_eq (y : ℝ) : wK y = y * max 0 (1 - y) := by
  unfold wK; split_ifs with h
  · rw [max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith)]; ring

/-- Elementary: `w` is continuous. -/
lemma wK_continuous : Continuous wK := by
  have : wK = fun y => y * max 0 (1 - y) := funext wK_eq
  rw [this]; fun_prop

/-- Davenport ch. 17: `𝓜 w (s) = ∫₀¹ t^(s-1) t (1 - t) dt`. -/
lemma mellin_wK_eq_interval (s : ℂ) :
    mellin (fun x ↦ (wK x : ℂ)) s = ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * (t * (1 - t)) := by
  unfold mellin
  rw [intervalIntegral.integral_of_le zero_le_one]
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    (f := fun t : ℝ => (t : ℂ) ^ (s - 1) • (wK t : ℂ)) measurableSet_Ioi
    (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0) (fun t ht => by
      have : 1 < t := by
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht; exact ht.2 ht.1
      simp [wK_of_gt this])
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only [smul_eq_mul]
  rw [wK_of_le ht.2]; push_cast; ring

/-- Davenport ch. 17: `𝓜 w (s) = 1/((s+1)(s+2))` for `Re s > -1`. -/
theorem mellin_wK {s : ℂ} (hs : -1 < s.re) :
    mellin (fun x ↦ (wK x : ℂ)) s = 1 / ((s + 1) * (s + 2)) := by
  rw [mellin_wK_eq_interval]
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hs2 : s + 1 + 1 ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have e : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * (t * (1 - t)) =
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ s) - ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s + 1) := by
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht _
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      rw [cpow_sub _ _ ht', cpow_one, cpow_add _ _ ht', cpow_one]
      field_simp
    · exact intervalIntegral.intervalIntegrable_cpow' hs
    · exact intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  rw [e, integral_cpow (Or.inl hs), integral_cpow (Or.inl (by simp; linarith))]
  simp only [ofReal_one, one_cpow, ofReal_zero]
  rw [zero_cpow hs1, zero_cpow hs2]
  have hs2' : s + 2 ≠ 0 := by rw [show s + 2 = s + 1 + 1 by ring]; exact hs2
  field_simp
  ring

/-- Elementary: `t^(σ-1) w(t)` is integrable on `(0, ∞)` for `σ > 0`. -/
lemma wK_mellinConvergent {σ : ℝ} (hσ : 0 < σ) : MellinConvergent (fun x ↦ (wK x : ℂ)) σ := by
  unfold MellinConvergent
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hii : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) * (wK t : ℂ)) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)).mul_continuousOn
        (Complex.continuous_ofReal.comp wK_continuous).continuousOn
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hii
    simpa [smul_eq_mul] using hii
  · refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [wK_of_gt ht]

/-- Elementary: `|1/((s+1)(s+2))| ≤ 1/(1+t²)` for `s = σ + it`, `σ ≥ 0`. -/
lemma norm_kernelK_le {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ‖1 / (((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2))‖ ≤ (1 + t ^ 2)⁻¹ := by
  have e1 : (σ : ℂ) + t * I + 1 = ((σ + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
  have e2 : (σ : ℂ) + t * I + 2 = ((σ + 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  rw [e1, e2]
  have h1 : 1 + t ^ 2 ≤ ‖((σ + 1 : ℝ) : ℂ) + t * I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]; nlinarith
  have h2 : ‖((σ + 1 : ℝ) : ℂ) + t * I‖ ≤ ‖((σ + 2 : ℝ) : ℂ) + t * I‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]; nlinarith
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [norm_div, norm_one, norm_mul, one_div]
  apply inv_anti₀ hpos
  calc 1 + t ^ 2 ≤ ‖((σ + 1 : ℝ) : ℂ) + t * I‖ ^ 2 := h1
    _ = ‖((σ + 1 : ℝ) : ℂ) + t * I‖ * ‖((σ + 1 : ℝ) : ℂ) + t * I‖ := by ring
    _ ≤ ‖((σ + 1 : ℝ) : ℂ) + t * I‖ * ‖((σ + 2 : ℝ) : ℂ) + t * I‖ := by gcongr

/-- The kernel `KK σ t = 1/((σ+it+1)(σ+it+2))`. -/
noncomputable def KK (σ t : ℝ) : ℂ := 1 / (((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2))

/-- Elementary: the kernel is continuous for `σ ≥ 0`. -/
lemma KK_continuous {σ : ℝ} (hσ : 0 ≤ σ) : Continuous fun t : ℝ => KK σ t := by
  unfold KK
  apply Continuous.div continuous_const (by fun_prop)
  intro t h
  rcases mul_eq_zero.mp h with h | h
  · have := congr_arg Complex.re h; simp at this; linarith
  · have := congr_arg Complex.re h; simp at this; linarith

/-- Elementary: the kernel is integrable on the line for `σ ≥ 0`. -/
lemma KK_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable fun t : ℝ => KK σ t :=
  Integrable.mono' integrable_inv_one_add_sq (KK_continuous hσ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_kernelK_le hσ t)

/-- Davenport ch. 17, the discontinuous integral for the kernel `1/((s+1)(s+2))`. -/
theorem kernel_perron {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ (-((c : ℂ) + t * I)) /
        (((c : ℂ) + t * I + 1) * ((c : ℂ) + t * I + 2)) = (wK y : ℂ) := by
  have hre : ∀ t : ℝ, -1 < ((c : ℂ) + t * I).re := fun t => by simp; linarith
  have hF : (fun t : ℝ => mellin (fun x ↦ (wK x : ℂ)) ((c : ℂ) + t * I)) =
      fun t : ℝ => KK c t := by
    funext t; rw [mellin_wK (hre t)]; rfl
  have hinv := mellinInv_mellin_eq c (fun x ↦ (wK x : ℂ)) hy
    (wK_mellinConvergent hc)
    (by unfold VerticalIntegrable; rw [hF]; exact KK_integrable hc.le)
    ((Complex.continuous_ofReal.comp wK_continuous).continuousAt)
  unfold mellinInv at hinv
  rw [← hinv]
  simp only [smul_eq_mul]
  congr 1
  · simp only [one_div, mul_inv_rev]
    exact (by push_cast; ring : (π : ℂ)⁻¹ * 2⁻¹ = ((π⁻¹ * 2⁻¹ : ℝ) : ℂ))
  · congr 1; funext t; rw [mellin_wK (hre t), mul_one_div]

/-- On `Re s > 1`, `Σ χ(n) Λ(n) n^(-s) = -L'/L(s, χ)`, for every Dirichlet character. -/
theorem lseries_chi_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -(deriv χ.LFunction s / χ.LFunction s) := by
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hL : ∀ z : ℂ, 1 < z.re → χ.LFunction z = LSeries (fun n => χ n) z :=
    fun z hz => DirichletCharacter.LFunction_eq_LSeries χ hz
  have hd : deriv χ.LFunction s = deriv (LSeries (fun n => χ n)) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hs] with z hz
    exact hL z hz
  rw [hd, hL s hs, ← neg_div]
  exact h


/-- Elementary: `(n/x)^(-s) = x^s / n^s` for `n, x > 0`. -/
lemma cpow_div_eq' {n x : ℝ} (hn : 0 < n) (hx : 0 < x) (s : ℂ) :
    ((n / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, mul_cpow_ofReal_nonneg hn.le (inv_nonneg.mpr hx.le),
    Complex.ofReal_inv, inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, cpow_neg, inv_inv, div_eq_inv_mul, mul_comm]

open scoped ArithmeticFunction.vonMangoldt in
/-- Davenport ch. 17, Perron for the Cesaro kernel and any coefficients with `|a(n)| ≤ Λ(n)`:
`Σ a(n) w(n/x) = (1/2π) ∫ L(a, σ+it) x^(σ+it) / ((σ+it+1)(σ+it+2)) dt`, `x > 0`, `σ > 1`. -/
theorem perron_coeff (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ Λ n) {x : ℝ} (hx : 0 < x) {σ : ℝ}
    (hσ : 1 < σ) :
    ∑' n : ℕ, a n * (wK (n / x) : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, LSeries a ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) *
        KK σ t := by
  have ha0 : a 0 = 0 := norm_le_zero_iff.mp (by simpa using ha 0)
  set F : ℕ → ℝ → ℂ := fun n t => a n * (((n / x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * KK σ t)
    with hF
  have hKint : Integrable (fun t : ℝ => KK σ t) := KK_integrable (by linarith)
  have hnormF : ∀ n t, ‖F n t‖ = ‖a n‖ * ((n / x : ℝ) ^ (-σ)) * ‖KK σ t‖ := by
    intro n t
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [hF, h0, ha0]
    have hnx : 0 < (n / x : ℝ) := div_pos (by exact_mod_cast hpos) hx
    simp only [hF, norm_mul]
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
    have hb : Integrable fun t : ℝ => ((n / x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * KK σ t := by
      refine hKint.bdd_mul (c := (n / x : ℝ) ^ (-σ) + 1) hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp only [CharP.cast_eq_zero, zero_div, ofReal_zero]
        rw [zero_cpow (by intro h; have := congr_arg Complex.re h; simp at this; linarith),
          norm_zero]; positivity
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (by exact_mod_cast hpos) hx)]
        simp
    exact hb.const_mul _
  have hΛsum : Summable fun n : ℕ => Λ n * ((n / x : ℝ) ^ (-σ)) := by
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
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hnormF, integral_const_mul]
    apply Summable.mul_right
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hx.le) _)) (fun n => ?_) hΛsum
    exact mul_le_mul_of_nonneg_right (ha n)
      (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hx.le) _)
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hl : ∀ n, ∫ t, F n t = (2 * π : ℂ) * (a n * (wK (n / x) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [hF, h0, ha0]
    have hk := kernel_perron (y := n / x) (div_pos (by exact_mod_cast hpos) hx)
      (by linarith : 0 < σ)
    have hI : ∫ t : ℝ, ((n / x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * KK σ t =
        2 * π * (wK (n / x) : ℂ) := by
      rw [← hk, ← mul_assoc, mul_one_div_cancel h2π, one_mul]
      unfold KK
      simp_rw [mul_one_div]
    simp only [hF, integral_const_mul]
    rw [hI]; ring
  have hr : ∀ t : ℝ, ∑' n, F n t =
      LSeries a ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) * KK σ t := by
    intro t
    simp only [hF, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0, ha0]
    rw [LSeries.term_of_ne_zero hpos.ne', cpow_div_eq' (by exact_mod_cast hpos) hx]
    push_cast
    ring
  simp_rw [hl, hr] at key
  rw [tsum_mul_left] at key
  rw [← key, ← mul_assoc, one_div_mul_cancel h2π, one_mul]

/-- Davenport ch. 17, Perron for the Cesaro sum: `S(x, χ) = (1/2π) ∫ F(2 + it) dt`. -/
theorem perron_chi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    cesaroChi χ x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, Fchi χ x ((2 : ℂ) + t * I) := by
  have hcoef : ∀ n : ℕ, ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  have hP := perron_coeff (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) hcoef hx
    (σ := 2) (by norm_num)
  have hfin : ∑' n : ℕ, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * (wK (n / x) : ℂ) =
      cesaroChi χ x := by
    unfold cesaroChi
    refine tsum_eq_sum (fun n hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    have hxn : x < n := by
      have := Nat.lt_floor_add_one x
      calc x < (⌊x⌋₊ : ℝ) + 1 := this
        _ ≤ n := by exact_mod_cast hn
    rw [wK_of_gt ((one_lt_div hx).mpr hxn)]
    simp
  rw [← hfin, hP]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have hre : 1 < ((2 : ℂ) + t * I).re := by simp
  have e2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by push_cast; ring
  rw [e2, lseries_chi_vonMangoldt χ hre]
  unfold Fchi KK
  rw [e2]
  ring

end LeanLab.Linnik.ExplicitFormula
