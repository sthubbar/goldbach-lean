module

public import LeanLab.BhowmikGrimmelt2026.Decomp540a

/-!
Hardy 1914, Comptes rendus 158, pages 1012 to 1014.
The unshifted theta formula and residue contour shift remain analytic inputs.
Weighted differentiation and the corrected theta ray estimates are proved.
Only the zeroth and second moments are needed for the one zero target.
The theta boundary limit at every derivative order is proved from shifted Gaussian bounds.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory Set
open Complex Asymptotics Metric Function

/-- Hardy 1914 page 1013, the left side of display 3. -/
noncomputable def hardyMoment515 (p : ℕ) (α : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0,
    (Real.exp (α * t) + Real.exp (-α * t)) * t ^ (2 * p) * hardyXi515 (2 * t) /
      ((1 / 4 : ℝ) + 4 * t ^ 2)

/-- Hardy 1914 page 1013, the theta correction inside the derivative in display 3.
The Jacobi parameter is `I * exp (I * α)` and its nome is `exp (-π * exp (I * α))`. -/
noncomputable def hardyThetaCorrection515 (α : ℝ) : ℝ :=
  (((Real.pi / 2 : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I / 4) *
    jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I))).re

/-- Hardy 1914 page 1012: the real Xi agrees with the completed zeta expression. -/
theorem ofReal_hardyXi515 (t : ℝ) :
    (hardyXi515 t : ℂ) =
      (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
        (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1) / 2) *
          completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  have hr :
      (((completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re : ℝ) : ℂ) =
        completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
    Complex.conj_eq_iff_re.mp (conj_completedRiemannZeta_half_add_mul_I t)
  have hp :
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
        (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1) / 2 =
          (-((1 / 4 : ℝ) + t ^ 2) / 2 : ℝ) := by
    push_cast
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [hp, hardyXi515, Complex.ofReal_mul, hr]

/-- Hardy 1914 page 1012: Xi vanishes exactly at a critical line zero. -/
theorem hardyXi_eq_zero_iff515 (t : ℝ) :
    hardyXi515 t = 0 ↔
      riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have hp : -((1 / 4 : ℝ) + t ^ 2) / 2 ≠ 0 := by
    have := sq_nonneg t
    linarith
  have hs : (1 / 2 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hg : Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  have hr :
      (((completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re : ℝ) : ℂ) =
        completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
    Complex.conj_eq_iff_re.mp (conj_completedRiemannZeta_half_add_mul_I t)
  rw [hardyXi515, mul_eq_zero, or_iff_right hp, riemannZeta_def_of_ne_zero hs,
    div_eq_zero_iff, or_iff_left hg]
  constructor
  · intro h
    rw [← hr, h, Complex.ofReal_zero]
  · intro h
    rw [h, Complex.zero_re]

/-- Hardy 1914 page 1012: continuity of Xi on the real axis. -/
theorem continuous_hardyXi515 : Continuous hardyXi515 := by
  have hc : Continuous fun t : ℝ =>
      (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
    apply ContinuousAt.comp (differentiableAt_completedZeta ?_ ?_).continuousAt
      (by fun_prop)
    all_goals
      intro h
      have := congrArg Complex.re h
      norm_num at this
  exact (by fun_prop : Continuous fun t : ℝ => -((1 / 4 : ℝ) + t ^ 2) / 2).mul hc

/-- Hardy 1914 page 1012, display 1: the polynomial factor in Xi cancels the denominator. -/
theorem hardyXi_scaled515 (t : ℝ) :
    hardyXi515 (2 * t) / ((1 / 4 : ℝ) + 4 * t ^ 2) =
      -(1 / 2 : ℝ) *
        (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have hd : (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 := by positivity
  have he : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
  rw [hardyXi515, he]
  field_simp

/-- Hardy 1914 pages 1012 and 1013, displays 1 and 3, as a completed zeta integral. -/
theorem hardyMoment_eq_completed515 (p : ℕ) (α : ℝ) :
    hardyMoment515 p α = -(1 / 2 : ℝ) *
      ∫ t : ℝ in Ioi 0,
        (Real.exp (α * t) + Real.exp (-α * t)) * t ^ (2 * p) *
          (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  rw [hardyMoment515, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  calc
    _ = (Real.exp (α * t) + Real.exp (-α * t)) * t ^ (2 * p) *
        (hardyXi515 (2 * t) / ((1 / 4 : ℝ) + 4 * t ^ 2)) := by ring
    _ = _ := by rw [hardyXi_scaled515]; ring

/-- Hardy 1914 page 1013 display 2: the theta correction is continuous inside the strip. -/
theorem continuousAt_hardyThetaCorrection515 (α : ℝ) (hα : |α| < Real.pi / 2) :
    ContinuousAt hardyThetaCorrection515 α := by
  have ha : 0 < (Complex.I * Complex.exp ((α : ℂ) * Complex.I)).im := by
    simpa [Complex.exp_re] using Real.cos_pos_of_mem_Ioo (abs_lt.mp hα)
  have ht : ContinuousAt (fun β : ℝ =>
      jacobiTheta (Complex.I * Complex.exp ((β : ℂ) * Complex.I))) α :=
    (continuousAt_jacobiTheta ha).comp
      (f := fun β : ℝ => Complex.I * Complex.exp ((β : ℂ) * Complex.I)) (by fun_prop)
  unfold hardyThetaCorrection515
  exact Complex.continuous_re.continuousAt.comp
    ((continuousAt_const.mul (by fun_prop)).mul ht)

/-- Hardy 1914 page 1013 displays 2 and 3: interior smoothness of the theta correction.
This follows from complex differentiability of Jacobi theta on the upper half plane. -/
theorem contDiffAt_hardyThetaCorrection515 (n : ℕ) (α : ℝ) (hα : |α| < Real.pi / 2) :
    ContDiffAt ℝ n hardyThetaCorrection515 α := by
  have ha : 0 < (Complex.I * Complex.exp ((α : ℂ) * Complex.I)).im := by
    simpa [Complex.exp_re] using Real.cos_pos_of_mem_Ioo (abs_lt.mp hα)
  have ho : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd : DifferentiableOn ℂ jacobiTheta {z : ℂ | 0 < z.im} :=
    fun z hz => (differentiableAt_jacobiTheta hz).differentiableWithinAt
  have ht : ContDiffAt ℂ n jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) :=
    (hd.contDiffOn ho).contDiffAt (ho.mem_nhds ha)
  have hof : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hexp : ContDiff ℝ n Complex.exp := (show ContDiff ℂ n Complex.exp from Complex.contDiff_exp).restrict_scalars ℝ
  have htr : ContDiffAt ℝ n jacobiTheta
      (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) := ht.restrict_scalars ℝ
  have hinner : ContDiffAt ℝ n (fun β : ℝ =>
      Complex.I * Complex.exp ((β : ℂ) * Complex.I)) α :=
    contDiffAt_const.mul (hexp.contDiffAt.comp α (hof.contDiffAt.mul contDiffAt_const))
  have hr : ContDiffAt ℝ n (fun β : ℝ =>
      jacobiTheta (Complex.I * Complex.exp ((β : ℂ) * Complex.I))) α :=
    ContDiffAt.comp α (g := jacobiTheta) htr hinner
  unfold hardyThetaCorrection515
  exact Complex.reCLM.contDiff.contDiffAt.comp α
    ((contDiffAt_const.mul
      (hexp.contDiffAt.comp α ((hof.contDiffAt.mul contDiffAt_const).div_const 4))).mul hr)

/-- Hardy 1914 page 1013 display 2 from page 1012 display 1.
CONDITIONAL on the exact unshifted theta formula and residue contour shift in Decomp540a. -/
theorem hardy_mellin_base515 (α : ℝ) (hα : |α| < Real.pi / 2) :
    hardyMoment515 0 α = Real.pi * Real.cos (α / 4) - hardyThetaCorrection515 α := by
  have he : expMoment540 hardyAmplitude540 0 α = hardyMoment515 0 α := by
    rw [expMoment540, hardyMoment_eq_completed515, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [expMomentIntegrand540, hardyAmplitude540, pow_zero, one_mul]
    ring
  have hs := hardy_shifted_contour540 α hα
  rw [hardy_unshifted_theta540 α hα, he] at hs
  have hre : (Complex.exp ((α : ℂ) * I / 4)).re = Real.cos (α / 4) := by
    simp [Complex.exp_re]
  have hr : (Complex.exp ((α : ℂ) * I / 4) * ((Real.pi : ℂ) *
      (jacobiTheta (I * Complex.exp ((α : ℂ) * I)) - 1))).re =
      2 * hardyThetaCorrection515 α - Real.pi * Real.cos (α / 4) := by
    simp only [hardyThetaCorrection515, mul_sub, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, hre]
    ring
  rw [hr] at hs
  linarith

/-- Hardy 1914 page 1013, differentiation from display 2 to display 3.
Proved for every even order by the theta ray decay and dominated differentiation.
No cited Mellin or contour input is used by this derivative theorem. -/
theorem hardy_mellin_differentiation515 (p : ℕ) (α : ℝ)
    (hα : |α| < Real.pi / 2) :
    ContDiffAt ℝ (2 * p) (hardyMoment515 0) α ∧
      iteratedDeriv (2 * p) (hardyMoment515 0) α = hardyMoment515 p α := by
  let φ : ℝ := (|α| + Real.pi / 2) / 2
  have hφα : |α| < φ := by dsimp [φ]; linarith
  have hφpos : 0 < φ := lt_of_le_of_lt (abs_nonneg α) hφα
  have hφ : |φ| < Real.pi / 2 := by rw [abs_of_pos hφpos]; dsimp [φ]; linarith
  obtain ⟨C, hC, hdecay⟩ := hardyAmplitude_decay540 φ hφ
  have he (q : ℕ) : expMoment540 hardyAmplitude540 (2 * q) = hardyMoment515 q := by
    funext β
    rw [hardyMoment_eq_completed515, expMoment540, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [expMomentIntegrand540, hardyAmplitude540, pow_mul,
      neg_one_sq, one_pow, one_mul]
    ring
  have hzero : expMoment540 hardyAmplitude540 0 = hardyMoment515 0 := by simpa using he 0
  have hd := (contDiffOn_expMoment540 hardyAmplitude540 continuous_hardyAmplitude540
    φ C hC.le hdecay (2 * p) 0).contDiffAt
      ((isOpen_lt continuous_abs continuous_const).mem_nhds hφα)
  rw [hzero] at hd
  have hi := iteratedDeriv_expMoment540 hardyAmplitude540 continuous_hardyAmplitude540
    φ C hC.le hdecay (2 * p) α hφα
  rw [hzero, he p] at hi
  exact ⟨hd, hi⟩

/-- Hardy 1914 page 1013, display 3: the even derivative of the cosine term. -/
theorem hardy_cos_iteratedDeriv515 (p : ℕ) (α : ℝ) :
    iteratedDeriv (2 * p) (fun β : ℝ => Real.pi * Real.cos (β / 4)) α =
      (-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (α / 4) := by
  rw [iteratedDeriv_const_mul _ (by fun_prop)]
  have he : (fun β : ℝ => Real.cos (β / 4)) =
      (fun β : ℝ => Real.cos ((1 / 4 : ℝ) * β)) := by
    ext β
    congr 1
    ring
  rw [he, iteratedDeriv_comp_const_mul Real.contDiff_cos, Real.iteratedDeriv_even_cos]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply]
  have ha : (1 / 4 : ℝ) * α = α / 4 := by ring
  rw [ha, one_div_pow]
  ring

/-- Hardy 1914 page 1013 display 3, assembled from the base transform and proved differentiation.
CONDITIONAL only on the two base contour inputs. -/
theorem hardy_mellin_identity515 (p : ℕ) (α : ℝ) (hα : |α| < Real.pi / 2) :
    hardyMoment515 p α =
      (-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (α / 4) -
        iteratedDeriv (2 * p) hardyThetaCorrection515 α := by
  have he : hardyThetaCorrection515 =ᶠ[𝓝 α]
      (fun β : ℝ => Real.pi * Real.cos (β / 4) - hardyMoment515 0 β) := by
    have ho : {β : ℝ | |β| < Real.pi / 2} ∈ 𝓝 α :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hα
    filter_upwards [ho] with β hβ
    have hb := hardy_mellin_base515 β hβ
    linarith
  have hd := hardy_mellin_differentiation515 p α hα
  have hh := he.iteratedDeriv_eq (2 * p)
  rw [iteratedDeriv_fun_sub (by fun_prop) hd.1, hardy_cos_iteratedDeriv515, hd.2] at hh
  linarith

/-- Hardy 1914 page 1013 Section 2, after display 3: the shift to the cusp minus one
is a half characteristic theta function. This identity follows term by term from parity. -/
theorem jacobiTheta_sub_one515 (τ : ℂ) (_hτ : 0 < τ.im) : jacobiTheta (τ - 1) = jacobiTheta₂ (1 / 2) τ := by
  unfold jacobiTheta jacobiTheta₂
  apply tsum_congr
  intro n
  unfold jacobiTheta₂_term
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have hc : (n : ℂ) * ((n : ℂ) + 1) = (k : ℂ) + (k : ℂ) := by
    exact_mod_cast hk
  have he : 2 * Real.pi * Complex.I * (n : ℂ) * (1 / 2) + Real.pi * Complex.I * (n : ℂ) ^ 2 * τ =
      Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ - 1) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    linear_combination (Real.pi * Complex.I) * hc
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
/-- Hardy 1914 page 1013 Section 2, after display 3: inversion of the shifted theta.
This is the elementary modular route toward the printed cusp limit. The quantitative
derivative bounds remain separate. -/
theorem jacobiTheta_cusp_transform515 (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta (τ - 1) =
      1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) *
        Complex.exp (-Real.pi * Complex.I * (1 / 2 : ℂ) ^ 2 / τ) *
          jacobiTheta₂ ((1 / 2 : ℂ) / τ) (-1 / τ) := by
  rw [jacobiTheta_sub_one515 τ hτ, jacobiTheta₂_functional_equation]

/-- Hardy 1914 page 1013 Section 2, after display 3: the shifted Gaussian theta sum is bounded by the corresponding positive Gaussian sum. -/
theorem half_gaussian_bound515 (v : ℂ) (hv : 0 < v.im) :
    ‖∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * v)‖ ≤
      ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * v.im) := by
  have hn (n : ℤ) :
      ‖Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * v)‖ =
        Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * v.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  have hs : Summable (fun n : ℤ => Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * v.im)) := by
    apply (HurwitzKernelBounds.summable_f_int 0 (1 / 2) hv).congr
    intro n
    simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
  have hs' : Summable (fun n : ℤ => ‖Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * v)‖) := by
    simpa only [hn] using hs
  simpa only [hn] using norm_tsum_le_tsum_norm hs'

/-- Hardy 1914 page 1013 Section 2: the nonzero half characteristic Gaussian has exponential decay at infinite height. This uses the existing Mathlib Hurwitz kernel bound. -/
theorem half_gaussian_decay515 : ∃ c : ℝ, 0 < c ∧
    (fun y : ℝ => ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * y))
      =O[atTop] (fun y : ℝ => Real.exp (-c * y)) := by
  have ha : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
    rw [Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num)]
    norm_num
  obtain ⟨c, hc, h⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub ((1 / 2 : ℝ) : UnitAddCircle)
  refine ⟨c, hc, ?_⟩
  simpa only [if_neg ha, sub_zero, HurwitzKernelBounds.F_int, Function.Periodic.lift_coe,
    HurwitzKernelBounds.f_int, pow_zero, one_mul] using h


/-- Hardy 1914 page 1013 Section 2: shift the Jacobi parameter by one to put the cusp minus one at zero. -/
noncomputable def cuspW515 (α : ℝ) : ℂ := 1 + I * Complex.exp ((α : ℂ) * I)
/-- Hardy 1914 page 1013 Section 2: the inverted shifted Jacobi parameter used in the modular route. -/
noncomputable def cuspV515 (α : ℝ) : ℂ := -1 / cuspW515 α
/-- Hardy 1914 page 1013 Section 2: the inverted parameter lies on the vertical line of real part minus one half. -/
theorem cuspV_coords515 (α : ℝ) (hα : |α| < Real.pi / 2) :
    (cuspV515 α).re = -(1 / 2 : ℝ) ∧
      (cuspV515 α).im = (1 + Real.sin α) / (2 * Real.cos α) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo (abs_lt.mp hα)
  have hs : Real.sin α ≠ 1 := by
    intro he
    have hh := Real.sin_sq_add_cos_sq α
    rw [he] at hh
    nlinarith [sq_pos_of_pos hc]
  have hd : 1 - Real.sin α ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hr : (cuspW515 α).re = 1 - Real.sin α := by simp [cuspW515, Complex.exp_re, Complex.exp_im, sub_eq_add_neg]
  have hi : (cuspW515 α).im = Real.cos α := by simp [cuspW515, Complex.exp_re]
  have hn : Complex.normSq (cuspW515 α) = 2 * (1 - Real.sin α) := by
    rw [Complex.normSq_apply, hr, hi]
    nlinarith [Real.sin_sq_add_cos_sq α]
  constructor
  · simp only [cuspV515, neg_div, neg_re, one_div, Complex.inv_re, hr, hn]
    field_simp
  · simp only [cuspV515, neg_div, neg_im, one_div, Complex.inv_im, hi, hn, neg_div, neg_neg]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq α]

/-- Hardy 1914 page 1013 Section 2: the inverted shifted parameter tends to infinite height along the printed alpha path. -/
theorem cuspV_height_tendsto515 : Tendsto (fun α : ℝ => (cuspV515 α).im) (𝓝[<] (Real.pi / 2)) atTop := by
  have hstrip : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), |α| < Real.pi / 2 := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] :
      -(Real.pi / 2) < Real.pi / 2)] with α hα
    exact abs_lt.mpr hα
  have hcos : Tendsto Real.cos (𝓝[<] (Real.pi / 2)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Real.continuous_cos.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
    · filter_upwards [hstrip] with α hα
      exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hα)
  have hn : Tendsto (fun α : ℝ => (1 + Real.sin α) / 2)
      (𝓝[<] (Real.pi / 2)) (𝓝 (1 : ℝ)) := by
    simpa using ((Real.continuous_sin.tendsto (Real.pi / 2)).mono_left
      nhdsWithin_le_nhds).const_add 1 |>.div_const 2
  have hh := (tendsto_inv_nhdsGT_zero.comp hcos).atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hn
  apply hh.congr'
  filter_upwards [hstrip] with α hα
  rw [(cuspV_coords515 α hα).2]
  simp only [Function.comp_apply]
  ring


/-- Hardy 1914 page 1013 Section 2: completion of the square in the shifted modular formula gives a half characteristic Gaussian series. -/
theorem cusp_half_gaussian515 (w : ℂ) (hw : 0 < w.im) :
    jacobiTheta (w - 1) = 1 / (-I * w) ^ (1 / 2 : ℂ) *
      ∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (-1 / w)) := by
  have hp : Complex.exp (-Real.pi * I * (1 / 2 : ℂ) ^ 2 / w) *
      jacobiTheta₂ ((1 / 2 : ℂ) / w) (-1 / w) =
        ∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) - 1 / 2) ^ 2 * (-1 / w)) := by
    rw [jacobiTheta₂, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [jacobiTheta₂_term]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hn : (∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) - 1 / 2) ^ 2 * (-1 / w))) =
      ∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (-1 / w)) := by
    rw [← (Equiv.neg ℤ).tsum_eq (f := fun n : ℤ =>
      Complex.exp (Real.pi * I * ((n : ℂ) - 1 / 2) ^ 2 * (-1 / w)))]
    apply tsum_congr
    intro n
    simp only [Equiv.neg_apply, Int.cast_neg]
    congr 1
    ring
  rw [jacobiTheta_cusp_transform515 w hw, mul_assoc, hp, hn]

/-- Hardy 1914 page 1013 Section 2: the norm of the modular square root prefactor is the square root of the norm of the inverted parameter. -/
theorem cusp_prefactor_norm515 (w : ℂ) : ‖1 / (-I * w) ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖-1 / w‖ := by
  have he : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [he, norm_div, norm_one, Complex.norm_cpow_real]
  rw [← Real.sqrt_eq_rpow, norm_mul, norm_neg, Complex.norm_I, one_mul]
  simp only [norm_div, norm_neg, norm_one, one_div, Real.sqrt_inv]


/-- Hardy 1914 page 1013 Section 2, the last term of display 3 at p zero: the theta correction tends to zero. Proved from modular inversion and exponential Gaussian decay. -/
theorem hardy_theta_flat_zero515 :
    Tendsto hardyThetaCorrection515 (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  obtain ⟨c, hc, hdec⟩ := half_gaussian_decay515
  obtain ⟨C, hC, hbound⟩ := hdec.exists_pos
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hbound.bound
  have hV := cuspV_height_tendsto515
  have hstrip : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), |α| < Real.pi / 2 := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] :
      -(Real.pi / 2) < Real.pi / 2)] with α hα
    exact abs_lt.mpr hα
  have hlarge : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), max Y 1 ≤ (cuspV515 α).im :=
    hV.eventually (eventually_ge_atTop _)
  have hE : Tendsto (fun y : ℝ => Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hYE : Tendsto (fun y : ℝ => y * Real.exp (-c * y)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
  have hG : Tendsto (fun y : ℝ => (2 + y) * Real.exp (-c * y)) atTop (𝓝 0) := by
    have hg := (hE.const_mul 2).add hYE
    simp only [mul_zero, zero_add] at hg
    apply hg.congr'
    filter_upwards [] with y
    ring
  have hG' : Tendsto (fun α : ℝ => (Real.pi / 2 * C) *
      ((2 + (cuspV515 α).im) * Real.exp (-c * (cuspV515 α).im)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (hG.const_mul (Real.pi / 2 * C)).comp hV
  have he : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), ‖hardyThetaCorrection515 α‖ ≤
      (Real.pi / 2 * C) * ((2 + (cuspV515 α).im) * Real.exp (-c * (cuspV515 α).im)) := by
    filter_upwards [hstrip, hlarge] with α hα hlarge
    have hu : 0 < (cuspV515 α).im := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      ((le_max_right Y 1).trans hlarge)
    have hw : 0 < (cuspW515 α).im := by
      simpa [cuspW515, Complex.exp_re] using Real.cos_pos_of_mem_Ioo (abs_lt.mp hα)
    have hS : ‖∑' n : ℤ, Complex.exp
        (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * cuspV515 α)‖ ≤
          C * Real.exp (-c * (cuspV515 α).im) := by
      apply (half_gaussian_bound515 (cuspV515 α) hu).trans
      apply (le_abs_self _).trans
      simpa only [Real.norm_eq_abs, Real.abs_exp] using
        hY ((cuspV515 α).im) ((le_max_left Y 1).trans hlarge)
    have hF : ‖1 / (-I * cuspW515 α) ^ (1 / 2 : ℂ)‖ ≤ 2 + (cuspV515 α).im := by
      rw [cusp_prefactor_norm515]
      change Real.sqrt ‖cuspV515 α‖ ≤ _
      have hnorm := Complex.norm_le_abs_re_add_abs_im (cuspV515 α)
      rw [(cuspV_coords515 α hα).1, abs_neg,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_pos hu] at hnorm
      have hsqrt : Real.sqrt ‖cuspV515 α‖ ≤ 1 + ‖cuspV515 α‖ := by
        nlinarith [Real.sq_sqrt (norm_nonneg (cuspV515 α)),
          Real.sqrt_nonneg ‖cuspV515 α‖, sq_nonneg (Real.sqrt ‖cuspV515 α‖ - 1)]
      linarith
    have htheta : jacobiTheta (I * Complex.exp ((α : ℂ) * I)) =
        1 / (-I * cuspW515 α) ^ (1 / 2 : ℂ) *
          ∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * cuspV515 α) := by
      calc
        _ = jacobiTheta (cuspW515 α - 1) := by congr 1; unfold cuspW515; ring
        _ = _ := by simpa only [cuspV515] using cusp_half_gaussian515 (cuspW515 α) hw
    have hphase : ‖Complex.exp ((α : ℂ) * I / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hcoef : ‖((Real.pi / 2 : ℝ) : ℂ)‖ = Real.pi / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have htbound : ‖jacobiTheta (I * Complex.exp ((α : ℂ) * I))‖ ≤
        (2 + (cuspV515 α).im) * (C * Real.exp (-c * (cuspV515 α).im)) := by
      rw [htheta, norm_mul]
      exact mul_le_mul hF hS (norm_nonneg _) (by positivity)
    rw [hardyThetaCorrection515, Real.norm_eq_abs]
    calc
      _ ≤ ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.exp ((α : ℂ) * I / 4) *
          jacobiTheta (I * Complex.exp ((α : ℂ) * I))‖ := Complex.abs_re_le_norm _
      _ = (Real.pi / 2) * ‖jacobiTheta (I * Complex.exp ((α : ℂ) * I))‖ := by
        rw [norm_mul, norm_mul, hcoef, hphase, mul_one]
      _ ≤ (Real.pi / 2) * ((2 + (cuspV515 α).im) *
          (C * Real.exp (-c * (cuspV515 α).im))) :=
        mul_le_mul_of_nonneg_left htbound (by positivity)
      _ = _ := by ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun α => norm_nonneg (hardyThetaCorrection515 α)) he hG')

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem cusp_theta_exponential_bound515 : ∃ c C Y : ℝ, 0 < c ∧ 0 < C ∧
    ∀ w : ℂ, 0 < w.im → Y ≤ (-1 / w).im →
      ‖jacobiTheta (w - 1)‖ ≤ C * (1 + ‖-1 / w‖) * Real.exp (-c * (-1 / w).im) := by
  obtain ⟨c, hc, hdec⟩ := half_gaussian_decay515
  obtain ⟨C, hC, hbound⟩ := hdec.exists_pos
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hbound.bound
  refine ⟨c, C, max Y 1, hc, hC, ?_⟩
  intro w hw hy
  have hv : 0 < (-1 / w).im := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_right Y 1).trans hy)
  have hS : ‖∑' n : ℤ, Complex.exp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (-1 / w))‖ ≤
      C * Real.exp (-c * (-1 / w).im) := by
    apply (half_gaussian_bound515 (-1 / w) hv).trans
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hY ((-1 / w).im) ((le_max_left Y 1).trans hy)
  have hF : ‖1 / (-I * w) ^ (1 / 2 : ℂ)‖ ≤ 1 + ‖-1 / w‖ := by
    rw [cusp_prefactor_norm515]
    nlinarith [Real.sq_sqrt (norm_nonneg (-1 / w)), Real.sqrt_nonneg ‖-1 / w‖,
      sq_nonneg (Real.sqrt ‖-1 / w‖ - 1)]
  rw [cusp_half_gaussian515 w hw, norm_mul]
  calc
    _ ≤ (1 + ‖-1 / w‖) * (C * Real.exp (-c * (-1 / w).im)) :=
      mul_le_mul hF hS (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem cusp_ball_geometry515 (z w : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hz : z.im = δ) (hn : ‖z‖ ≤ 2 * δ) (hw : w ∈ closedBall z (δ / 2)) :
    0 < w.im ∧ ‖w‖ ≤ 3 * δ ∧
      1 / (18 * δ) ≤ (-1 / w).im ∧ ‖-1 / w‖ ≤ 2 / δ := by
  have hd : ‖w - z‖ ≤ δ / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have him := (Complex.abs_im_le_norm (w - z)).trans hd
  have hi : δ / 2 ≤ w.im := by
    have := (abs_le.mp him).1
    simp only [sub_im, hz] at this
    linarith
  have hip : 0 < w.im := lt_of_lt_of_le (by linarith) hi
  have hnw : ‖w‖ ≤ 3 * δ := by
    calc
      ‖w‖ = ‖(w - z) + z‖ := by congr 1; ring
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 3 * δ := by linarith
  have hlo : δ / 2 ≤ ‖w‖ := hi.trans ((le_abs_self w.im).trans (Complex.abs_im_le_norm w))
  have hnp : 0 < ‖w‖ := lt_of_lt_of_le (by linarith) hlo
  have hvnorm : ‖-1 / w‖ = 1 / ‖w‖ := by simp only [norm_div, norm_neg, norm_one]
  have hvim : (-1 / w).im = w.im / ‖w‖ ^ 2 := by
    simp only [neg_div, one_div, neg_im, Complex.inv_im, neg_div, neg_neg,
      Complex.normSq_eq_norm_sq]
  refine ⟨hip, hnw, ?_, ?_⟩
  · rw [hvim]
    apply (div_le_div_iff₀ (by positivity : 0 < 18 * δ) (sq_pos_of_pos hnp)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg w) hnw 2
    nlinarith
  · rw [hvnorm]
    apply (div_le_div_iff₀ hnp hδ).mpr
    linarith

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem cusp_center_norm515 (α : ℝ) (ha : 0 ≤ α) (hb : α < Real.pi / 2) :
    ‖cuspW515 α‖ ≤ 2 * Real.cos α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb⟩
  have hs : 0 ≤ Real.sin α := Real.sin_nonneg_of_mem_Icc ⟨ha, by linarith [Real.pi_pos]⟩
  have ht : 0 ≤ (1 - Real.sin α) * (1 + 2 * Real.sin α) :=
    mul_nonneg (sub_nonneg.mpr (Real.sin_le_one _)) (by positivity)
  have hn : ‖cuspW515 α‖ ^ 2 = 2 * (1 - Real.sin α) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [cuspW515, Complex.exp_re, Complex.exp_im, sub_eq_add_neg]
    nlinarith [Real.sin_sq_add_cos_sq α]
  nlinarith [Real.sin_sq_add_cos_sq α, norm_nonneg (cuspW515 α)]

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem cusp_theta_derivatives_vanish515 (n : ℕ) :
    Tendsto (fun α : ℝ => iteratedDeriv n (fun w : ℂ => jacobiTheta (w - 1)) (cuspW515 α))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  obtain ⟨c, C, Y, hc, hC, hbound⟩ := cusp_theta_exponential_bound515
  let x : ℝ → ℝ := fun α => (Real.cos α)⁻¹
  have hstrip : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), 0 < α ∧ α < Real.pi / 2 :=
    Ioo_mem_nhdsLT (by positivity)
  have hx : Tendsto x (𝓝[<] (Real.pi / 2)) atTop := by
    have hcos : Tendsto Real.cos (𝓝[<] (Real.pi / 2)) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa using (Real.continuous_cos.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
      · filter_upwards [hstrip] with α hα
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα.2⟩
    exact tendsto_inv_nhdsGT_zero.comp hcos
  have hlarge : ∀ᶠ α in 𝓝[<] (Real.pi / 2), max (18 * Y) 1 ≤ x α :=
    hx.eventually (eventually_ge_atTop _)
  have ha : 0 < c / 18 := by positivity
  have hpow (k : ℕ) : Tendsto (fun y : ℝ => y ^ k * Real.exp (-(c / 18) * y))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (c / 18) ha
  have hlim : Tendsto (fun α : ℝ => (n.factorial : ℝ) * C *
      (1 + 2 * x α) * (2 * x α) ^ n * Real.exp (-(c / 18) * x α))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h := (((hpow n).add ((hpow (n + 1)).const_mul 2)).const_mul
      ((n.factorial : ℝ) * C * 2 ^ n)).comp hx
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [] with α
    simp only [Function.comp_apply, mul_pow, pow_succ]
    ring
  have he : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2),
      ‖iteratedDeriv n (fun w : ℂ => jacobiTheta (w - 1)) (cuspW515 α)‖ ≤
        (n.factorial : ℝ) * C * (1 + 2 * x α) * (2 * x α) ^ n *
          Real.exp (-(c / 18) * x α) := by
    filter_upwards [hstrip, hlarge] with α hα hlarge
    have hδ : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα.2⟩
    have hz : (cuspW515 α).im = Real.cos α := by simp [cuspW515, Complex.exp_re]
    have hn := cusp_center_norm515 α hα.1.le hα.2
    have hgeom (w : ℂ) (hw : w ∈ closedBall (cuspW515 α) (Real.cos α / 2)) :=
      cusp_ball_geometry515 (cuspW515 α) w (Real.cos α) hδ hz hn hw
    have hd : DifferentiableOn ℂ (fun w : ℂ => jacobiTheta (w - 1)) {w : ℂ | 0 < w.im} := by
      intro w hw
      exact ((differentiableAt_jacobiTheta (by simpa using hw)).comp w (by fun_prop)).differentiableWithinAt
    have hdiff : DiffContOnCl ℂ (fun w : ℂ => jacobiTheta (w - 1))
        (ball (cuspW515 α) (Real.cos α / 2)) :=
      hd.diffContOnCl_ball (fun w hw => (hgeom w hw).1)
    have hSphere (w : ℂ) (hw : w ∈ sphere (cuspW515 α) (Real.cos α / 2)) :
        ‖jacobiTheta (w - 1)‖ ≤ C * (1 + 2 * x α) * Real.exp (-(c / 18) * x α) := by
      have hg := hgeom w (sphere_subset_closedBall hw)
      have hi : x α / 18 ≤ (-1 / w).im := by
        convert hg.2.2.1 using 1
        dsimp [x]
        ring
      have hy : Y ≤ (-1 / w).im := by
        have hh := (le_max_left (18 * Y) 1).trans hlarge
        linarith
      have hnorm : ‖-1 / w‖ ≤ 2 * x α := by simpa only [x, div_eq_mul_inv] using hg.2.2.2
      have hex : Real.exp (-c * (-1 / w).im) ≤ Real.exp (-(c / 18) * x α) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        _ ≤ C * (1 + ‖-1 / w‖) * Real.exp (-c * (-1 / w).im) := hbound w hg.1 hy
        _ ≤ _ := by gcongr
    have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
      (by positivity : 0 < Real.cos α / 2) hdiff hSphere
    apply hh.trans_eq
    have hp : ((Real.cos α / 2) ^ n)⁻¹ = (2 * x α) ^ n := by
      rw [← inv_pow, inv_div]
      simp only [x, div_eq_mul_inv]
    rw [div_eq_mul_inv, hp]
    ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun α => norm_nonneg _) he hlim)

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem flat_scomp515 (f g : ℂ → ℂ) (a : ℝ) (hf : ContDiff ℂ ⊤ f)
    (hg : ∀ᶠ t : ℝ in 𝓝[<] a, ContDiffAt ℂ ⊤ g (f (t : ℂ)))
    (hflat : ∀ k : ℕ, Tendsto (fun t : ℝ => iteratedDeriv k g (f (t : ℂ))) (𝓝[<] a) (𝓝 0))
    (n : ℕ) : Tendsto (fun t : ℝ => iteratedDeriv n (g ∘ f) (t : ℂ)) (𝓝[<] a) (𝓝 0) := by
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[<] a) (𝓝 (a : ℂ)) :=
    (Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds
  have hprod (c : OrderedFinpartition n) : Tendsto
      (fun t : ℝ => (∏ j, iteratedDeriv (c.partSize j) f (t : ℂ)))
      (𝓝[<] a) (𝓝 (∏ j, iteratedDeriv (c.partSize j) f (a : ℂ))) := by
    apply tendsto_finsetProd
    intro j hj
    exact ((hf.continuous_iteratedDeriv (c.partSize j) (by simp)).tendsto _).comp hreal
  have hterm (c : OrderedFinpartition n) : Tendsto
      (fun t : ℝ => (∏ j, iteratedDeriv (c.partSize j) f (t : ℂ)) *
        iteratedDeriv c.length g (f (t : ℂ))) (𝓝[<] a) (𝓝 0) := by
    simpa only [mul_zero] using (hprod c).mul (hflat c.length)
  have hs : Tendsto
      (fun t : ℝ => ∑ c : OrderedFinpartition n,
        (∏ j, iteratedDeriv (c.partSize j) f (t : ℂ)) *
          iteratedDeriv c.length g (f (t : ℂ))) (𝓝[<] a) (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun c hc => hterm c)
  apply hs.congr'
  filter_upwards [hg] with t ht
  simpa only [smul_eq_mul] using
    (iteratedDeriv_scomp_eq_sum_orderedFinpartition (i := n) ht hf.contDiffAt (by simp)).symm

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem flat_mul515 (f g : ℂ → ℂ) (a : ℝ) (hf : ContDiff ℂ ⊤ f)
    (hg : ∀ᶠ t : ℝ in 𝓝[<] a, ContDiffAt ℂ ⊤ g (t : ℂ))
    (hflat : ∀ k : ℕ, Tendsto (fun t : ℝ => iteratedDeriv k g (t : ℂ)) (𝓝[<] a) (𝓝 0))
    (n : ℕ) : Tendsto (fun t : ℝ => iteratedDeriv n (f * g) (t : ℂ)) (𝓝[<] a) (𝓝 0) := by
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[<] a) (𝓝 (a : ℂ)) :=
    (Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds
  have hterm (i : ℕ) : Tendsto
      (fun t : ℝ => (n.choose i : ℂ) * iteratedDeriv i f (t : ℂ) * iteratedDeriv (n - i) g (t : ℂ))
      (𝓝[<] a) (𝓝 0) := by
    have hf' := ((hf.continuous_iteratedDeriv i (by simp)).tendsto (a : ℂ)).comp hreal
    simpa only [mul_zero, Function.comp_apply] using (hf'.const_mul (n.choose i : ℂ)).mul (hflat (n - i))
  have hs : Tendsto (fun t : ℝ => ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i f (t : ℂ) * iteratedDeriv (n - i) g (t : ℂ))
      (𝓝[<] a) (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range (n + 1)) (fun i hi => hterm i)
  apply hs.congr'
  filter_upwards [hg] with t ht
  exact (iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (ht.of_le (by simp))).symm

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem iteratedDeriv_real_part515 (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (n : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ U) :
    iteratedDeriv n (fun t : ℝ => (F (t : ℂ)).re) x = (iteratedDeriv n F (x : ℂ)).re := by
  have hD (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k F) U := by
    induction k with
    | zero => simpa using hF
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun t : ℝ => (F (t : ℂ)).re) =ᶠ[𝓝 x]
        (fun t : ℝ => (iteratedDeriv n F (t : ℂ)).re) := by
      have hu : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ U :=
        Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hu] with t ht
      exact ih t ht
    rw [he.deriv_eq]
    simpa only [iteratedDeriv_succ] using
      ((hD n).differentiableAt (hU.mem_nhds hx)).hasDerivAt.real_of_complex.deriv

/-- Hardy 1914 page 1013, Section 2 after display 3.
Auxiliary estimate for the theta cusp derivative limit. -/
theorem hardy_theta_derivatives_flat515 (n : ℕ) :
    Tendsto (iteratedDeriv n hardyThetaCorrection515) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  let W : ℂ → ℂ := fun z => 1 + Complex.I * Complex.exp (z * Complex.I)
  let G : ℂ → ℂ := fun w => jacobiTheta (w - 1)
  let P : ℂ → ℂ := fun z => (Real.pi / 2 : ℂ) * Complex.exp (z * Complex.I / 4)
  let H : ℂ → ℂ := G ∘ W
  let F : ℂ → ℂ := P * H
  have hW : ContDiff ℂ ⊤ W := by dsimp [W]; fun_prop
  have hP : ContDiff ℂ ⊤ P := by dsimp [P]; fun_prop
  have hOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hG : DifferentiableOn ℂ G {w : ℂ | 0 < w.im} := by
    intro w hw
    exact ((differentiableAt_jacobiTheta (by simpa using hw)).comp w
      (differentiableAt_id.sub_const 1)).differentiableWithinAt
  have hstrip : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), |α| < Real.pi / 2 := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] :
      -(Real.pi / 2) < Real.pi / 2)] with α hα
    exact abs_lt.mpr hα
  have hwim (α : ℝ) (hα : |α| < Real.pi / 2) : 0 < (W (α : ℂ)).im := by
    simpa [W, Complex.exp_re] using Real.cos_pos_of_mem_Ioo (abs_lt.mp hα)
  have hg : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), ContDiffAt ℂ ⊤ G (W (α : ℂ)) := by
    filter_upwards [hstrip] with α hα
    exact (hG.contDiffOn hOpen).contDiffAt (hOpen.mem_nhds (hwim α hα))
  have hflatG (k : ℕ) : Tendsto (fun α : ℝ => iteratedDeriv k G (W (α : ℂ)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa only [G, W, cuspW515] using cusp_theta_derivatives_vanish515 k
  have hflatH (k : ℕ) : Tendsto (fun α : ℝ => iteratedDeriv k H (α : ℂ))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := flat_scomp515 W G _ hW hg hflatG k
  have hH : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), ContDiffAt ℂ ⊤ H (α : ℂ) := by
    filter_upwards [hg] with α hα
    exact hα.comp (α : ℂ) hW.contDiffAt
  have hflatF := flat_mul515 P H (Real.pi / 2) hP hH hflatH n
  let U : Set ℂ := {z | 0 < (W z).im}
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_im.comp hW.continuous)
  have hF : DifferentiableOn ℂ F U := by
    intro z hz
    apply (hP.differentiable (by simp)).differentiableAt.mul _ |>.differentiableWithinAt
    exact ((hG.differentiableAt (hOpen.mem_nhds hz)).comp z
      (hW.differentiable (by simp)).differentiableAt)
  have heq : (fun t : ℝ => (F (t : ℂ)).re) = hardyThetaCorrection515 := by
    funext t
    simp [F, P, H, G, W, Function.comp_apply, hardyThetaCorrection515]
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hflatF
  apply (show Tendsto (fun α : ℝ => (iteratedDeriv n F (α : ℂ)).re)
    (𝓝[<] (Real.pi / 2)) (𝓝 0) from by simpa only [F, Function.comp_def, Complex.zero_re] using hr).congr'
  filter_upwards [hstrip] with α hα
  exact (heq ▸ iteratedDeriv_real_part515 F U hU hF n α (hwim α hα)).symm

/-- Hardy 1914 page 1013, Section 2, the limit of the last term of display 3.
The path approaches the theta cusp with nome tending to minus one.
Modular Gaussian decay and Cauchy estimates prove every even derivative limit. -/
theorem hardy_theta_flat515 (p : ℕ) :
    Tendsto (iteratedDeriv (2 * p) hardyThetaCorrection515)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  exact hardy_theta_derivatives_flat515 (2 * p)

/-- Hardy 1914 page 1013, Section 3: the interior moments have the printed limit.
CONDITIONAL on the Mellin identity and theta cusp limit. -/
theorem hardy_moment_limit_of515 (p : ℕ)
    (hm : ∀ α : ℝ, |α| < Real.pi / 2 →
      hardyMoment515 p α =
        (-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (α / 4) -
          iteratedDeriv (2 * p) hardyThetaCorrection515 α)
    (ht : Tendsto (iteratedDeriv (2 * p) hardyThetaCorrection515)
      (𝓝[<] (Real.pi / 2)) (𝓝 0)) :
    Tendsto (hardyMoment515 p) (𝓝[<] (Real.pi / 2))
      (𝓝 ((-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (Real.pi / 8))) := by
  have hc : Tendsto (fun α : ℝ =>
      (-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (α / 4))
      (𝓝[<] (Real.pi / 2))
      (𝓝 ((-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (Real.pi / 8))) := by
    have : Continuous fun α : ℝ =>
        (-1 : ℝ) ^ p * Real.pi / 4 ^ (2 * p) * Real.cos (α / 4) := by fun_prop
    have heq : (Real.pi / 2) / 4 = Real.pi / 8 := by ring
    simpa only [heq] using (this.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), |α| < Real.pi / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ α : ℝ in 𝓝[<] (Real.pi / 2), -Real.pi / 2 < α from
        (eventually_gt_nhds (by linarith [Real.pi_pos] :
          -Real.pi / 2 < Real.pi / 2)).filter_mono nhdsWithin_le_nhds)] with α ha hb
    exact abs_lt.mpr ⟨by simpa only [neg_div] using hb, ha⟩
  have hh := hc.sub ht
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [he] with α hα
  exact (hm α hα).symm

/-- Hardy 1914 page 1013, Section 3: both signs of the limiting moments occur.
The cosine factor is strictly positive. -/
theorem hardy_cos_pos515 : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

/-- Hardy 1914 page 1013, Section 3, restricted to the one zero target:
the zeroth and second moment limits force opposite signs of Xi.
CONDITIONAL on the two displayed moment limits. -/
theorem hardyXi_signs_of_moment_limits515
    (hzero : Tendsto (hardyMoment515 0) (𝓝[<] (Real.pi / 2))
      (𝓝 (Real.pi * Real.cos (Real.pi / 8))))
    (hone : Tendsto (hardyMoment515 1) (𝓝[<] (Real.pi / 2))
      (𝓝 (-Real.pi / 16 * Real.cos (Real.pi / 8)))) :
    (∃ a : ℝ, 0 < a ∧ hardyXi515 a < 0) ∧
      (∃ b : ℝ, 0 < b ∧ 0 < hardyXi515 b) := by
  constructor
  · by_contra hn
    push Not at hn
    have hl : 0 ≤ -Real.pi / 16 * Real.cos (Real.pi / 8) :=
      ge_of_tendsto' hone fun α => by
        apply setIntegral_nonneg measurableSet_Ioi
        intro t ht
        apply div_nonneg
        · exact mul_nonneg
            (mul_nonneg (by positivity) (pow_nonneg (le_of_lt ht) _))
            (hn (2 * t) (by simpa using ht))
        · positivity
    have hc := hardy_cos_pos515
    have hp := Real.pi_pos
    have : -Real.pi / 16 * Real.cos (Real.pi / 8) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hc
    linarith
  · by_contra hn
    push Not at hn
    have hl : Real.pi * Real.cos (Real.pi / 8) ≤ 0 :=
      le_of_tendsto' hzero fun α => by
        apply setIntegral_nonpos measurableSet_Ioi
        intro t ht
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (by positivity) (pow_nonneg (le_of_lt ht) _))
            (hn (2 * t) (by simpa using ht))
        · positivity
    exact (not_le_of_gt (mul_pos Real.pi_pos hardy_cos_pos515)) hl

/-- Hardy 1914 page 1012, the real critical line function:
opposite signs give a critical line zero by the intermediate value theorem. -/
theorem hardy_zero_of_signs515 {a b : ℝ}
    (ha : hardyXi515 a < 0) (hb : 0 < hardyXi515 b) :
    ∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have hz : (0 : ℝ) ∈ uIcc (hardyXi515 a) (hardyXi515 b) :=
    mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩)
  obtain ⟨t, _, ht⟩ := intermediate_value_uIcc continuous_hardyXi515.continuousOn hz
  exact ⟨t, (hardyXi_eq_zero_iff515 t).mp ht⟩

/-- Hardy 1914 page 1013 Section 3, one critical line zero from the interior moments.
CONDITIONAL only on the two base contour inputs. Theta flatness and differentiation are proved. -/
theorem hardy_critical_line_zero515 :
    ∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have hzero : Tendsto (hardyMoment515 0) (𝓝[<] (Real.pi / 2))
      (𝓝 (Real.pi * Real.cos (Real.pi / 8))) := by
    simpa using hardy_moment_limit_of515 0
      (fun α hα => by simpa using hardy_mellin_base515 α hα)
      (by simpa using hardy_theta_flat_zero515)
  have hone : Tendsto (hardyMoment515 1) (𝓝[<] (Real.pi / 2))
      (𝓝 (-Real.pi / 16 * Real.cos (Real.pi / 8))) := by
    simpa only [Nat.mul_one, pow_one, neg_one_mul,
      show (4 : ℝ) ^ 2 = 16 by norm_num] using hardy_moment_limit_of515 1 (hardy_mellin_identity515 1)
      (hardy_theta_flat515 1)
  obtain ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩ := hardyXi_signs_of_moment_limits515 hzero hone
  exact hardy_zero_of_signs515 ha hb

/-- Hardy 1914 page 1013 display 2, continuity from the proved dominated differentiation theorem. -/
theorem continuousAt_hardyMoment_zero515 (α : ℝ) (hα : |α| < Real.pi / 2) :
    ContinuousAt (hardyMoment515 0) α := by
  exact (hardy_mellin_differentiation515 0 α hα).1.continuousAt

/-- Hardy 1914 page 1013 displays 2 and 3, the proved order zero case.
The continuity supplier has no cited analytic input. -/
theorem hardy_mellin_differentiation_zero515 (α : ℝ) (hα : |α| < Real.pi / 2) :
    ContDiffAt ℝ 0 (hardyMoment515 0) α ∧
      iteratedDeriv 0 (hardyMoment515 0) α = hardyMoment515 0 α := by
  refine ⟨contDiffAt_zero.mpr ?_, by simp⟩
  refine ⟨{β : ℝ | |β| < Real.pi / 2},
    (isOpen_lt continuous_abs continuous_const).mem_nhds hα, ?_⟩
  intro β hβ
  exact (continuousAt_hardyMoment_zero515 β hβ).continuousWithinAt

/-- Hardy 1914 page 1013 displays 2 and 3, every local finite smoothness order.
The proof uses the dominated derivative theorem and no base transform. -/
theorem contDiffAt_hardyMoment_zero515 (n : ℕ) (α : ℝ) (hα : |α| < Real.pi / 2) :
    ContDiffAt ℝ n (hardyMoment515 0) α := by
  exact (hardy_mellin_differentiation515 n α hα).1.of_le
    (by exact_mod_cast (show n ≤ 2 * n by omega))

end LeanLab.BhowmikGrimmelt2026
