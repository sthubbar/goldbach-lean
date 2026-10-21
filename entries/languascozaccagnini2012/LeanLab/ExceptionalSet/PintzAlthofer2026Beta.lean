module

public import Mathlib

/-!
# Pintz and Althöfer 2026, Section 4.4: the β integral behind (4.14)

Unit U-1116, T2 FRONTIER, idea I-0080, run 20261019T2303Z-16260.

Plain math. For `X > 0` and real `n`,

  ∫_ℝ e(−nβ) (X⁻¹ − 2πiβ)⁻² dβ = n e^{−n/X} if n > 0, and 0 if n ≤ 0,

where e(x) = exp(2πix). This is the integral that turns the major arc model
`(X⁻¹ − 2πiβ)⁻²` of the exponential-weight circle method into its Fourier
coefficients `n e^{−n/X}`, the first elementary step of the model coefficients
(4.14) to (4.17) in `BesselInput`. It is classical; the lab proves it here by
Fourier inversion of `f(t) = t e^{−t/X}` on `t > 0`, extended by zero, whose
Fourier transform is `(X⁻¹ + 2πiβ)⁻²`, the Laplace integral
`∫₀^∞ t e^{−rt} dt = r⁻²` for `Re r > 0`.

Status: PROVED unconditional, KNOWN mathematics. It does not by itself discharge
`BesselInput`; Lemma 4, the zero sum, stays cited.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Beta

open Real MeasureTheory Set Filter Topology FourierTransform

/-- `f_X(t) = t e^{−t/X}` for `t > 0` and `0` for `t ≤ 0`, written with `max t 0`
so that continuity is immediate. -/
noncomputable def kern (X : ℝ) (t : ℝ) : ℂ :=
  ((max t 0 * Real.exp (-(max t 0) / X) : ℝ) : ℂ)

/-- The model `(X⁻¹ + 2πiβ)⁻²`. -/
noncomputable def model (X : ℝ) (β : ℝ) : ℂ :=
  1 / (((1 / X : ℝ) : ℂ) + ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2

lemma kern_of_pos {X t : ℝ} (ht : 0 < t) : kern X t = ((t * Real.exp (-t / X) : ℝ) : ℂ) := by
  simp [kern, max_eq_left ht.le]

lemma kern_of_nonpos {X t : ℝ} (ht : t ≤ 0) : kern X t = 0 := by
  simp [kern, max_eq_right ht]

lemma continuous_kern (X : ℝ) : Continuous (kern X) := by
  unfold kern
  fun_prop

/-- Laplace integral: `∫₀^∞ t e^{−rt} dt = 1/r²` for `Re r > 0`. -/
theorem laplace_t (r : ℂ) (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) * Complex.exp (-(r * t)) = 1 / r ^ 2 := by
  have hr0 : r ≠ 0 := by
    intro h; rw [h] at hr; simp at hr
  set F : ℝ → ℂ := fun t => -((t : ℂ) / r + 1 / r ^ 2) * Complex.exp (-(r * t)) with hF
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F ((x : ℂ) * Complex.exp (-(r * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-(r * 1)) x := (h1.const_mul r).neg
    have h3 := h2.cexp
    have h4 : HasDerivAt (fun t : ℝ => -((t : ℂ) / r + 1 / r ^ 2)) (-(1 / r)) x := by
      have := (h1.div_const r).add_const (1 / r ^ 2)
      exact this.neg
    convert h4.mul h3 using 1
    field_simp
    ring
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-(r * t))‖ = Real.exp (-(r.re * t)) := by
    intro t; rw [Complex.norm_exp]; simp
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(r * t))) (Ioi 0) := by
    have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r.re)
      (by norm_num) (by norm_num) hr
    refine Integrable.mono' hg ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * Complex.exp (-(r * t)))
        |>.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht',
        Real.rpow_one]
      apply le_of_eq; ring_nf
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => (t / ‖r‖ + 1 / ‖r‖ ^ 2) * Real.exp (-(r.re * t)))
        atTop (𝓝 0) := by
      have e1 : Tendsto (fun t : ℝ => (r.re * t) ^ 1 * Real.exp (-(r.re * t))) atTop (𝓝 0) :=
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_id.const_mul_atTop hr)
      have e2 : Tendsto (fun t : ℝ => Real.exp (-(r.re * t))) atTop (𝓝 0) := by
        have := Real.tendsto_exp_atBot.comp
          ((tendsto_id.const_mul_atTop hr).comp tendsto_id |> tendsto_neg_atTop_atBot.comp)
        simpa [Function.comp_def] using this
      have e3 := (e1.const_mul (1 / (r.re * ‖r‖))).add (e2.const_mul (1 / ‖r‖ ^ 2))
      simp only [mul_zero, add_zero] at e3
      refine e3.congr' (Eventually.of_forall fun t => ?_)
      have : r.re ≠ 0 := hr.ne'
      have : ‖r‖ ≠ 0 := norm_ne_zero_iff.2 hr0
      simp only [pow_one]
      field_simp
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hF]
    simp only
    rw [norm_mul, norm_neg, hnorm]
    gcongr
    calc ‖(t : ℂ) / r + 1 / r ^ 2‖ ≤ ‖(t : ℂ) / r‖ + ‖1 / r ^ 2‖ := norm_add_le _ _
      _ = t / ‖r‖ + 1 / ‖r‖ ^ 2 := by
        rw [norm_div, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
          norm_one]
  have := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (m := 0) (a := 0) (by fun_prop) hderiv hint hlim
  rw [this]
  simp [hF]

lemma model_re_pos {X : ℝ} (hX : 0 < X) (β : ℝ) :
    0 < (((1 / X : ℝ) : ℂ) + ((2 * π * β : ℝ) : ℂ) * Complex.I).re := by
  simp [hX]

/-- `f_X` is integrable on `ℝ`. -/
theorem integrable_kern {X : ℝ} (hX : 0 < X) : Integrable (kern X) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1 / X)
    (by norm_num) (by norm_num) (by positivity)
  have hon : IntegrableOn (kern X) (Ioi 0) := by
    refine Integrable.mono' hg (continuous_kern X).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [kern_of_pos ht', Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), Real.rpow_one]
    apply le_of_eq; ring_nf
  exact hon.integrable_of_forall_notMem_eq_zero fun t ht =>
    kern_of_nonpos (not_lt.1 ht)

/-- The Fourier transform of `f_X` is the model: `𝓕 f_X (β) = (X⁻¹ + 2πiβ)⁻²`. -/
theorem fourier_kern {X : ℝ} (hX : 0 < X) (β : ℝ) : 𝓕 (kern X) β = model X β := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
  · rw [model, ← laplace_t _ (model_re_pos hX β)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [kern_of_pos ht', smul_eq_mul]
    push_cast
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    have : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    field_simp
    ring
  · intro t ht
    rw [kern_of_nonpos (not_lt.1 ht), smul_zero]

lemma norm_model {X : ℝ} (hX : 0 < X) (β : ℝ) :
    ‖model X β‖ = X ^ 2 * (1 + (2 * π * X * β) ^ 2)⁻¹ := by
  rw [model, norm_div, norm_one, norm_pow]
  have h : ‖((1 / X : ℝ) : ℂ) + ((2 * π * β : ℝ) : ℂ) * Complex.I‖ ^ 2
      = (1 / X) ^ 2 + (2 * π * β) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [h]
  field_simp

lemma continuous_model {X : ℝ} (hX : 0 < X) : Continuous (model X) := by
  unfold model
  refine continuous_const.div (by fun_prop) fun β => ?_
  apply pow_ne_zero
  intro h
  have := model_re_pos hX β
  rw [h] at this
  simp at this

/-- The model is integrable on `ℝ`. -/
theorem integrable_model {X : ℝ} (hX : 0 < X) : Integrable (model X) := by
  have h1 : Integrable fun β : ℝ => (1 + (2 * π * X * β) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity : (2 * π * X : ℝ) ≠ 0)
  refine Integrable.mono' (h1.const_mul (X ^ 2)) (continuous_model hX).aestronglyMeasurable
    (Eventually.of_forall fun β => ?_)
  rw [norm_model hX]

/-- **The β integral**, for every real `n`:
`∫_ℝ e(−nβ) (X⁻¹ − 2πiβ)⁻² dβ = f_X(n)`, that is `n e^{−n/X}` for `n > 0` and `0` for
`n ≤ 0`. Fourier inversion of `f_X`. -/
theorem beta_integral {X : ℝ} (hX : 0 < X) (n : ℝ) :
    ∫ β : ℝ, Complex.exp (((-2 * π * n * β : ℝ) : ℂ) * Complex.I) *
        (1 / (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2) = kern X n := by
  have hinv := congrFun (Continuous.fourierInv_fourier_eq (continuous_kern X) (integrable_kern hX)
    (by rw [show 𝓕 (kern X) = model X from funext (fourier_kern hX)]; exact integrable_model hX)) n
  rw [← hinv, fourierInv_eq_fourier_comp_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun β => ?_)
  simp only [smul_eq_mul]
  rw [fourier_kern hX, model]
  congr 2
  · push_cast; ring
  · push_cast; ring

/-- The β integral for `n > 0`: `n e^{−n/X}`. -/
theorem beta_integral_pos {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    ∫ β : ℝ, Complex.exp (((-2 * π * n * β : ℝ) : ℂ) * Complex.I) *
        (1 / (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2)
      = ((n * Real.exp (-n / X) : ℝ) : ℂ) := by
  rw [beta_integral hX, kern_of_pos hn]

/-- The β integral for `n ≤ 0`: `0`. -/
theorem beta_integral_nonpos {X n : ℝ} (hX : 0 < X) (hn : n ≤ 0) :
    ∫ β : ℝ, Complex.exp (((-2 * π * n * β : ℝ) : ℂ) * Complex.I) *
        (1 / (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2) = 0 := by
  rw [beta_integral hX, kern_of_nonpos hn]

/-- Vacuity test: the hypotheses hold at `X = 1`, `n = 1`, giving `e^{−1}`. -/
example : ∫ β : ℝ, Complex.exp (((-2 * π * 1 * β : ℝ) : ℂ) * Complex.I) *
        (1 / (((1 / 1 : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2)
      = ((1 * Real.exp (-1 / 1) : ℝ) : ℂ) :=
  beta_integral_pos one_pos one_pos

/-! ### U-1122: the truncation tails of (4.14)

Pintz-Althöfer arXiv 2610.15559v1 Section 4.3, after (4.14): "The absolute value of the omitted
tails is O(qX/P)." Here explicitly: cutting the β integral to `|β| ≤ B` changes it by at most
`1/(2π²B)`; with `B = P/(qX)` that is `qX/(2π²P)`. -/

/-- The integrand of (4.14), `e(−nβ)(X⁻¹ − 2πiβ)⁻²`. -/
noncomputable def mInt (X n β : ℝ) : ℂ :=
  Complex.exp (((-2 * π * n * β : ℝ) : ℂ) * Complex.I) *
    (1 / (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2)

lemma norm_mInt {X : ℝ} (_hX : 0 < X) (n β : ℝ) : ‖mInt X n β‖ = ‖model X (-β)‖ := by
  rw [mInt, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, model]
  congr 3
  push_cast; ring

lemma norm_mInt_le {X : ℝ} (hX : 0 < X) (n : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    ‖mInt X n β‖ ≤ (4 * π ^ 2)⁻¹ * (β ^ 2)⁻¹ := by
  rw [norm_mInt hX, norm_model hX]
  have hb : 0 < β ^ 2 := by positivity
  have hpi : 0 < π := Real.pi_pos
  have h1 : 0 < 1 + (2 * π * X * -β) ^ 2 := by positivity
  rw [← mul_inv, ← div_eq_mul_inv, div_le_iff₀ h1, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * π * X * β)]

lemma integrable_mInt {X : ℝ} (hX : 0 < X) (n : ℝ) : Integrable (mInt X n) := by
  have hc : Continuous (mInt X n) := by
    have : mInt X n = fun β => Complex.exp (((-2 * π * n * β : ℝ) : ℂ) * Complex.I) *
        model X (-β) := by
      funext β; simp only [mInt, model]; congr 3; push_cast; ring
    rw [this]
    exact (by fun_prop : Continuous fun β : ℝ => Complex.exp (((-2 * π * n * β : ℝ) : ℂ) *
      Complex.I)).mul ((continuous_model hX).comp continuous_neg)
  refine Integrable.mono' (integrable_model hX).comp_neg.norm hc.aestronglyMeasurable
    (Eventually.of_forall fun β => ?_)
  rw [norm_mInt hX]

lemma tail_Ioi {X B : ℝ} (hX : 0 < X) (hB : 0 < B) (n : ℝ) (sgn : ℝ) (hs : sgn = 1 ∨ sgn = -1) :
    ∫ β in Ioi B, ‖mInt X n (sgn * β)‖ ≤ (4 * π ^ 2)⁻¹ * B⁻¹ := by
  have hmaj : IntegrableOn (fun β : ℝ => (4 * π ^ 2)⁻¹ * β ^ (-(2 : ℝ))) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hB).const_mul _
  have hle : ∀ β ∈ Ioi B, ‖mInt X n (sgn * β)‖ ≤ (4 * π ^ 2)⁻¹ * β ^ (-(2 : ℝ)) := by
    intro β hβ
    have hβ0 : (0 : ℝ) < β := lt_trans hB hβ
    have h1 := norm_mInt_le hX n (β := sgn * β) (by rcases hs with h | h <;> subst h <;> simp [hβ0.ne'])
    have e : ((sgn * β) ^ 2)⁻¹ = β ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hβ0.le, Real.rpow_two]
      rcases hs with h | h <;> subst h <;> ring
    rwa [e] at h1
  have hint : IntegrableOn (fun β => ‖mInt X n (sgn * β)‖) (Ioi B) := by
    refine Integrable.mono' hmaj ?_ ?_
    · have : Continuous fun β : ℝ => ‖mInt X n (sgn * β)‖ := by
        have : mInt X n = fun β => Complex.exp (((-2 * π * n * β : ℝ) : ℂ) * Complex.I) *
            model X (-β) := by
          funext β; simp only [mInt, model]; congr 3; push_cast; ring
        rw [this]
        exact ((by fun_prop : Continuous fun β : ℝ => Complex.exp (((-2 * π * n * (sgn * β) : ℝ) : ℂ) *
          Complex.I)).mul ((continuous_model hX).comp (continuous_const.mul continuous_id).neg)).norm
      exact this.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun β hβ => ?_)
      rw [norm_norm]; exact hle β hβ
  calc ∫ β in Ioi B, ‖mInt X n (sgn * β)‖ ≤ ∫ β in Ioi B, (4 * π ^ 2)⁻¹ * β ^ (-(2 : ℝ)) :=
        setIntegral_mono_on hint hmaj measurableSet_Ioi hle
    _ = (4 * π ^ 2)⁻¹ * B⁻¹ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hB]
        norm_num [Real.rpow_neg_one]

/-- **The tails of (4.14)**: `‖∫_ℝ − ∫_{−B}^{B}‖ ≤ 1/(2π²B)` for the integrand
`e(−nβ)(X⁻¹ − 2πiβ)⁻²`, every real `n`, `X > 0`, `B > 0`. -/
theorem tail_bound {X B : ℝ} (hX : 0 < X) (hB : 0 < B) (n : ℝ) :
    ‖(∫ β, mInt X n β) - ∫ β in Ioc (-B) B, mInt X n β‖ ≤ 1 / (2 * π ^ 2 * B) := by
  have hint := integrable_mInt hX n
  rw [← integral_add_compl (measurableSet_Ioc (a := -B) (b := B)) hint, add_sub_cancel_left,
    Set.compl_Ioc]
  have hdis : Disjoint (Iic (-B)) (Ioi B) :=
    Set.disjoint_left.2 fun x h1 h2 => by simp only [mem_Iic] at h1; simp only [mem_Ioi] at h2; linarith
  have hn := hint.norm
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [setIntegral_union hdis measurableSet_Ioi hn.integrableOn hn.integrableOn]
  have h1 := tail_Ioi hX hB n 1 (Or.inl rfl)
  have h2 := tail_Ioi hX hB n (-1) (Or.inr rfl)
  simp only [one_mul] at h1
  simp only [neg_one_mul] at h2
  rw [integral_comp_neg_Ioi B (fun β => ‖mInt X n β‖)] at h2
  have : (4 * π ^ 2)⁻¹ * B⁻¹ + (4 * π ^ 2)⁻¹ * B⁻¹ = 1 / (2 * π ^ 2 * B) := by
    field_simp; ring
  linarith

/-- Truncated (4.14): for `n > 0`, `∫_{−B}^{B} e(−nβ)(X⁻¹ − 2πiβ)⁻² dβ = n e^{−n/X} + O*(1/(2π²B))`. -/
theorem truncated_beta {X B n : ℝ} (hX : 0 < X) (hB : 0 < B) (hn : 0 < n) :
    ‖(∫ β in Ioc (-B) B, mInt X n β) - ((n * Real.exp (-n / X) : ℝ) : ℂ)‖ ≤ 1 / (2 * π ^ 2 * B) := by
  have h := tail_bound hX hB n
  have e : (∫ β, mInt X n β) = ((n * Real.exp (-n / X) : ℝ) : ℂ) := by
    simpa [mInt] using beta_integral_pos (X := X) hX hn
  rw [e, norm_sub_rev] at h
  exact h

/-! ### U-1123: summing the truncated integrals over q, the first half of (4.16)

(4.14) writes `v_X(n) = Σ_{q≤P} w_q ∫_{−P/(qX)}^{P/(qX)} e(−nβ)(X⁻¹ − 2πiβ)⁻² dβ` with
`w_q = μ(q)² c_q(n)/φ(q)²`. For ANY weights `w`, each truncated integral is `n e^{−n/X}` within
`qX/(2π²P)`, so the whole sum is `n e^{−n/X} Σ_{q≤P} w_q` within `Σ_{q≤P} |w_q| qX/(2π²P)`.
With (4.15), `Σ_{q≤P} q|c_q(n)|/φ(q)² ≪ X^η`, this is the `O(X^{1+η}/P)` of (4.16). -/

/-- The truncated model coefficient with general weights `w`. -/
noncomputable def vTrunc (X P : ℝ) (Q : ℕ) (w : ℕ → ℂ) (n : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, w q * ∫ β in Ioc (-(P / (q * X))) (P / (q * X)), mInt X n β

/-- **(4.16), the q ≤ P part**: `‖v − n e^{−n/X} Σ w_q‖ ≤ Σ |w_q| qX/(2π²P)`. -/
theorem vTrunc_approx {X P n : ℝ} (hX : 0 < X) (hP : 0 < P) (hn : 0 < n) (Q : ℕ) (w : ℕ → ℂ) :
    ‖vTrunc X P Q w n - ((n * Real.exp (-n / X) : ℝ) : ℂ) * ∑ q ∈ Finset.Icc 1 Q, w q‖ ≤
      ∑ q ∈ Finset.Icc 1 Q, ‖w q‖ * (q * X / (2 * π ^ 2 * P)) := by
  unfold vTrunc
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hq).1
  have hB : 0 < P / (q * X) := by positivity
  have h := truncated_beta hX hB hn
  rw [show w q * (∫ β in Ioc (-(P / (q * X))) (P / (q * X)), mInt X n β) -
      ((n * Real.exp (-n / X) : ℝ) : ℂ) * w q =
      w q * ((∫ β in Ioc (-(P / (q * X))) (P / (q * X)), mInt X n β) -
        ((n * Real.exp (-n / X) : ℝ) : ℂ)) by ring, norm_mul]
  have e : 1 / (2 * π ^ 2 * (P / (q * X))) = q * X / (2 * π ^ 2 * P) := by
    field_simp
  rw [e] at h
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

end LeanLab.ExceptionalSet.PintzAlthofer2026Beta
