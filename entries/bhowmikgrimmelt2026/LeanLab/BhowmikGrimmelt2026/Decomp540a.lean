module

public import Mathlib

/-!
Auxiliary theta ray and exponential moment estimates for Hardy 1914.
Source: Comptes rendus 158, page 1012 display 1 and page 1013 displays 2 and 3.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open Real Complex Filter Topology MeasureTheory Set Asymptotics

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
noncomputable def expMomentIntegrand540 (f : ℝ → ℝ) (n : ℕ) (α t : ℝ) : ℝ :=
  (Real.exp (α * t) + (-1 : ℝ) ^ n * Real.exp (-α * t)) * t ^ n * f t

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
noncomputable def expMoment540 (f : ℝ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, expMomentIntegrand540 f n α t

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem hasDerivAt_expMomentIntegrand540 (f : ℝ → ℝ) (n : ℕ) (α t : ℝ) :
    HasDerivAt (fun β => expMomentIntegrand540 f n β t)
      (expMomentIntegrand540 f (n + 1) α t) α := by
  have hp : HasDerivAt (fun β : ℝ => Real.exp (β * t)) (Real.exp (α * t) * t) α :=
    by simpa only [Function.comp_def, id_eq, one_mul] using (Real.hasDerivAt_exp _).comp α ((hasDerivAt_id α).mul_const t)
  have hn : HasDerivAt (fun β : ℝ => Real.exp (-β * t))
      (Real.exp (-α * t) * (-t)) α := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-α * t)).comp α (((hasDerivAt_id α).neg).mul_const t)
  have hh := ((hp.add (hn.const_mul ((-1 : ℝ) ^ n))).mul_const (t ^ n)).mul_const (f t)
  convert hh using 1
  · ext β
    simp only [expMomentIntegrand540, Pi.add_apply]
  · simp only [expMomentIntegrand540, pow_succ]
    ring

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem expMomentIntegrand_bound540 (f : ℝ → ℝ) (n : ℕ) (α t b φ C : ℝ)
    (ht : 0 ≤ t) (hα : |α| ≤ b) (_hC : 0 ≤ C)
    (hf : |f t| ≤ C * Real.exp (-φ * t)) :
    ‖expMomentIntegrand540 f n α t‖ ≤
      2 * C * (t ^ n * Real.exp (-(φ - b) * t)) := by
  have hpos : Real.exp (α * t) ≤ Real.exp (b * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self α).trans hα) ht)
  have hneg : Real.exp (-α * t) ≤ Real.exp (b * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((neg_le_abs α).trans hα) ht)
  have hweight : |Real.exp (α * t) + (-1 : ℝ) ^ n * Real.exp (-α * t)| ≤
      2 * Real.exp (b * t) := by
    calc
      _ ≤ |Real.exp (α * t)| + |(-1 : ℝ) ^ n * Real.exp (-α * t)| := abs_add_le _ _
      _ = Real.exp (α * t) + Real.exp (-α * t) := by simp
      _ ≤ _ := by linarith
  rw [expMomentIntegrand540, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg ht]
  calc
    _ ≤ (2 * Real.exp (b * t)) * t ^ n * (C * Real.exp (-φ * t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hweight (pow_nonneg ht _)) hf
        (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show -(φ - b) * t = b * t + -φ * t by ring, Real.exp_add]
      ring

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem integrable_expMoment_majorant540 (n : ℕ) (φ b C : ℝ) (hb : b < φ) :
    IntegrableOn (fun t : ℝ => 2 * C * (t ^ n * Real.exp (-(φ - b) * t))) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := 1) (b := φ - b) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)) (by norm_num) (by linarith)
  simpa only [Real.rpow_natCast, Real.rpow_one, IntegrableOn] using hi.const_mul (2 * C)

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem continuous_expMomentIntegrand540 (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (α : ℝ) :
    Continuous (expMomentIntegrand540 f n α) := by
  unfold expMomentIntegrand540
  fun_prop

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem integrable_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (n : ℕ) (α : ℝ) (hα : |α| < φ) :
    IntegrableOn (expMomentIntegrand540 f n α) (Ioi 0) := by
  refine (integrable_expMoment_majorant540 n φ |α| C hα).mono'
    (continuous_expMomentIntegrand540 f hf n α).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact expMomentIntegrand_bound540 f n α t |α| φ C ht.le le_rfl hC (hbound t ht.le)

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem hasDerivAt_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (n : ℕ) (α : ℝ) (hα : |α| < φ) :
    HasDerivAt (expMoment540 f n) (expMoment540 f (n + 1) α) α := by
  let b : ℝ := (|α| + φ) / 2
  have hab : |α| < b := by dsimp [b]; linarith
  have hbφ : b < φ := by dsimp [b]; linarith
  have hs : {β : ℝ | |β| < b} ∈ 𝓝 α :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hab
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := expMomentIntegrand540 f n)
    (F' := expMomentIntegrand540 f (n + 1)) hs
    (Eventually.of_forall fun β => (continuous_expMomentIntegrand540 f hf n β).aestronglyMeasurable)
    (integrable_expMoment540 f hf φ C hC hbound n α hα)
    (continuous_expMomentIntegrand540 f hf (n + 1) α).aestronglyMeasurable
    ?_ (integrable_expMoment_majorant540 (n + 1) φ b C hbφ) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro β hβ
    exact expMomentIntegrand_bound540 f (n + 1) β t b φ C ht.le hβ.le hC (hbound t ht.le)
  · exact Eventually.of_forall fun t β hβ => hasDerivAt_expMomentIntegrand540 f n β t

/-- Hardy 1914 page 1013, auxiliary calculus for displays 2 and 3. -/
theorem iteratedDeriv_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (n : ℕ) (α : ℝ) (hα : |α| < φ) :
    iteratedDeriv n (expMoment540 f 0) α = expMoment540 f n α := by
  induction n generalizing α with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (expMoment540 f 0) =ᶠ[𝓝 α] expMoment540 f n := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hα] with β hβ
      exact ih β hβ
    rw [he.deriv_eq]
    exact (hasDerivAt_expMoment540 f hf φ C hC hbound n α hα).deriv

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
noncomputable def thetaMellinKernel540 (z : ℂ) : ℂ :=
  z ^ 2 * iteratedDeriv 2 (fun w : ℂ => jacobiTheta (I * w)) z +
    (3 / 2 : ℂ) * z * deriv (fun w : ℂ => jacobiTheta (I * w)) z

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem differentiableOn_thetaMellinKernel540 :
    DifferentiableOn ℂ thetaMellinKernel540 {z : ℂ | 0 < z.re} := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun w : ℂ => jacobiTheta (I * w)) {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_jacobiTheta (by simpa using hz)).comp z
      (by fun_prop)).differentiableWithinAt
  have hdd := (hd.deriv ho).deriv ho
  intro z hz
  have hd1 := (hd.deriv ho).differentiableAt (ho.mem_nhds hz)
  have hd2 := hdd.differentiableAt (ho.mem_nhds hz)
  unfold thetaMellinKernel540
  have hh := ((differentiableAt_id.pow 2).mul hd2).add
    ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (3 / 2 : ℂ) * z) z).mul hd1)
  convert hh.differentiableWithinAt using 1
  ext w
  simp [iteratedDeriv_succ]

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem ray_positive_re540 (φ x : ℝ) (hφ : |φ| < Real.pi / 2) (hx : 0 < x) :
    0 < ((x : ℂ) * Complex.exp ((φ : ℂ) * I)).re := by
  simpa [Complex.exp_re] using mul_pos hx (Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ))

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem continuousOn_theta_ray540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)))
      (Ioi 0) := by
  exact differentiableOn_thetaMellinKernel540.continuousOn.comp (by fun_prop)
    (fun x hx => ray_positive_re540 φ x hφ hx)

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem mellin_ray_phase_norm540 (φ t : ℝ) :
    ‖Complex.exp ((φ : ℂ) * I * ((1 / 4 : ℂ) + (t : ℂ) * I))‖ = Real.exp (-φ * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem mellin_ray_power_norm540 (x t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1)‖ = x ^ (-3 / 4 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  norm_num

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_cauchy_bound540 (n : ℕ) (z : ℂ) (hz : 1 ≤ z.re) :
    ‖iteratedDeriv n (fun w : ℂ => jacobiTheta (I * w) - 1) z‖ ≤
      (n.factorial : ℝ) * (2 / (1 - Real.exp (-Real.pi / 2))) *
        Real.exp (-Real.pi * (z.re - 1 / 2)) / (1 / 2 : ℝ) ^ n := by
  have hp : 0 < 1 - Real.exp (-Real.pi / 2) := by
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have hgeom (w : ℂ) (hw : w ∈ Metric.closedBall z (1 / 2)) : z.re - 1 / 2 ≤ w.re := by
    have hd : ‖w - z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hr := (Complex.abs_re_le_norm (w - z)).trans hd
    have hh := (abs_le.mp hr).1
    simp only [Complex.sub_re] at hh
    linarith
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun w : ℂ => jacobiTheta (I * w) - 1) {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (((differentiableAt_jacobiTheta (by simpa using hw)).comp w
      (by fun_prop)).sub_const 1).differentiableWithinAt
  have hdiff : DiffContOnCl ℂ (fun w : ℂ => jacobiTheta (I * w) - 1)
      (Metric.ball z (1 / 2)) :=
    hd.diffContOnCl_ball (fun w hw => by change 0 < w.re; have := hgeom w hw; linarith)
  rw [mul_assoc (n.factorial : ℝ)]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hdiff
  intro w hw
  have hg := hgeom w (Metric.sphere_subset_closedBall hw)
  have hwpos : 0 < w.re := by linarith
  calc
    _ ≤ (2 / (1 - Real.exp (-Real.pi * w.re))) * Real.exp (-Real.pi * w.re) := by
      simpa using norm_jacobiTheta_sub_one_le (τ := I * w) (by simpa using hwpos)
    _ ≤ (2 / (1 - Real.exp (-Real.pi / 2))) * Real.exp (-Real.pi * (z.re - 1 / 2)) := by
      have hr : 1 / 2 ≤ w.re := by linarith
      have hex : Real.exp (-Real.pi * w.re) ≤ Real.exp (-Real.pi / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      apply mul_le_mul
      · apply div_le_div_of_nonneg_left (by norm_num) hp
        linarith
      · apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      · positivity
      · positivity

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_kernel_bound540 (z : ℂ) (hz : 1 ≤ z.re) :
    ‖thetaMellinKernel540 z‖ ≤
      (8 * ‖z‖ ^ 2 + 3 * ‖z‖) * (2 / (1 - Real.exp (-Real.pi / 2))) *
        Real.exp (-Real.pi * (z.re - 1 / 2)) := by
  let T : ℂ → ℂ := fun w => jacobiTheta (I * w)
  have hd : deriv (fun w => T w - 1) = deriv T := by
    ext w
    exact deriv_sub_const 1
  have hdd : iteratedDeriv 2 (fun w => T w - 1) = iteratedDeriv 2 T := by
    simp only [iteratedDeriv_succ', iteratedDeriv_one]
    rw [hd]
  have h1 := theta_cauchy_bound540 1 z hz
  have h2 := theta_cauchy_bound540 2 z hz
  rw [iteratedDeriv_one] at h1
  change ‖deriv (fun w => T w - 1) z‖ ≤ _ at h1
  rw [hd] at h1
  change ‖iteratedDeriv 2 (fun w => T w - 1) z‖ ≤ _ at h2
  rw [hdd] at h2
  norm_num at h1 h2
  have hn : ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) := by norm_num
  calc
    _ ≤ ‖z‖ ^ 2 * ‖iteratedDeriv 2 T z‖ +
        (3 / 2 : ℝ) * ‖z‖ * ‖deriv T z‖ := by
      change ‖z ^ 2 * iteratedDeriv 2 T z + (3 / 2 : ℂ) * z * deriv T z‖ ≤ _
      calc
        _ ≤ ‖z ^ 2 * iteratedDeriv 2 T z‖ + ‖(3 / 2 : ℂ) * z * deriv T z‖ := norm_add_le _ _
        _ ≤ (‖z ^ 2‖ * ‖iteratedDeriv 2 T z‖) +
            (‖(3 / 2 : ℂ) * z‖ * ‖deriv T z‖) :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = _ := by rw [Complex.norm_pow, Complex.norm_mul, hn]
    _ ≤ ‖z‖ ^ 2 * (8 * (2 / (1 - Real.exp (-Real.pi / 2))) * Real.exp (-Real.pi * (z.re - 1 / 2))) +
        (3 / 2 : ℝ) * ‖z‖ * (2 * (2 / (1 - Real.exp (-Real.pi / 2))) * Real.exp (-Real.pi * (z.re - 1 / 2))) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        convert h2 using 1 <;> ring
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        convert h1 using 1 <;> ring
    _ = _ := by ring

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_ray_top540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    (fun x : ℝ => thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)))
      =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
  let c : ℝ := Real.cos φ
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ)
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have ha : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  have ht : Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-(Real.pi * c) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℕ) (Real.pi * c) ha
  have he : ∀ᶠ x : ℝ in atTop, x ^ 4 * Real.exp (-(Real.pi * c) * x) ≤ 1 :=
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun x hx => hx.le)
  refine Asymptotics.isBigO_iff.mpr ⟨11 * C * Real.exp (Real.pi / 2), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (1 / c)), he] with x hx hex
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxp : 0 < x := by linarith
  have hxc : 1 ≤ x * c := by
    have hh := (le_max_right 1 (1 / c)).trans hx
    exact (div_le_iff₀ hc).mp hh
  let z : ℂ := (x : ℂ) * Complex.exp ((φ : ℂ) * I)
  have hzr : z.re = x * c := by simp [z, c, Complex.exp_re]
  have hzn : ‖z‖ = x := by simp [z, norm_mul, Complex.norm_exp, abs_of_pos hxp]
  have hb := theta_kernel_bound540 z (by rwa [hzr])
  rw [hzr, hzn] at hb
  have hp : 8 * x ^ 2 + 3 * x ≤ 11 * x ^ 2 := by nlinarith
  have hExp : Real.exp (-Real.pi * (x * c - 1 / 2)) =
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * c) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : x ^ 2 * Real.exp (-(Real.pi * c) * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two]
    rw [← one_div (x ^ 2)]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ ≤ (8 * x ^ 2 + 3 * x) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := hb
    _ ≤ (11 * x ^ 2) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := by gcongr
    _ = (11 * C * Real.exp (Real.pi / 2)) *
        (x ^ 2 * Real.exp (-(Real.pi * c) * x)) := by rw [hExp]; ring
    _ ≤ (11 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]

/-- Hardy 1914 page 1012 display 1, auxiliary differentiated modular identity. -/
theorem theta_modular540 (z : ℂ) (hz : 0 < z.re) :
    jacobiTheta (I * z) = z ^ ((-1 / 2 : ℝ) : ℂ) * jacobiTheta (I * z⁻¹) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let τ : UpperHalfPlane := ⟨I * z, by simpa using hz⟩
  have hh := jacobiTheta_S_smul τ
  have hτ : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = I * z⁻¹ := by
    simp only [UpperHalfPlane.modular_S_smul, τ]
    field_simp
    simp [I_sq]
  have hc : -I * (τ : ℂ) = z := by dsimp [τ]; simp [← mul_assoc]
  rw [hτ, hc] at hh
  have hpow : z ^ ((-1 / 2 : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) = 1 := by
    rw [← Complex.cpow_add _ _ hz0]
    norm_num
  rw [hh, ← mul_assoc, hpow, one_mul]

/-- Hardy 1914 page 1012 display 1, auxiliary differentiated modular identity. -/
theorem hasDerivAt_theta_modular540 (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => jacobiTheta (I * w))
      (z ^ ((-1 / 2 : ℝ) : ℂ) *
        (-(jacobiTheta (I * z⁻¹)) / (2 * z) -
          deriv (fun w : ℂ => jacobiTheta (I * w)) z⁻¹ / z ^ 2)) z := by
  let T : ℂ → ℂ := fun w => jacobiTheta (I * w)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hi : 0 < (z⁻¹).re := by simpa [Complex.inv_re] using div_pos hz (Complex.normSq_pos.mpr hz0)
  have hT : DifferentiableAt ℂ T z⁻¹ :=
    (differentiableAt_jacobiTheta (by simpa using hi)).comp z⁻¹ (by fun_prop)
  have hq := (hasDerivAt_id z).cpow_const (c := ((-1 / 2 : ℝ) : ℂ)) hslit
  have hcomp := hT.hasDerivAt.comp z (hasDerivAt_inv hz0)
  have hprod := hq.mul hcomp
  have he : T =ᶠ[𝓝 z] (fun w : ℂ => w ^ ((-1 / 2 : ℝ) : ℂ) * T w⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with w hw
    exact theta_modular540 w hw
  have hcp : z ^ (((-1 / 2 : ℝ) : ℂ) - 1) = z ^ ((-1 / 2 : ℝ) : ℂ) / z := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  apply HasDerivAt.congr_of_eventuallyEq (f := fun w : ℂ => w ^ ((-1 / 2 : ℝ) : ℂ) * T w⁻¹) ?_ he
  convert hprod using 1
  · ext w
    simp [Function.comp_def, id_eq]
  · simp only [Function.comp_apply, id_eq, one_mul, hcp]
    dsimp [T]
    push_cast
    field_simp
    ring

/-- Hardy 1914 page 1012 display 1, auxiliary differentiated modular identity. -/
theorem theta_kernel_modular540 (z : ℂ) (hz : 0 < z.re) :
    thetaMellinKernel540 z = z ^ ((-1 / 2 : ℝ) : ℂ) * thetaMellinKernel540 z⁻¹ := by
  let T : ℂ → ℂ := fun w => jacobiTheta (I * w)
  let q : ℂ → ℂ := fun w => w ^ ((-1 / 2 : ℝ) : ℂ)
  let A : ℂ → ℂ := fun w => -(T w⁻¹) / (2 * w) - deriv T w⁻¹ / w ^ 2
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hi : 0 < (z⁻¹).re := by simpa [Complex.inv_re] using div_pos hz (Complex.normSq_pos.mpr hz0)
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hT : DifferentiableOn ℂ T {w : ℂ | 0 < w.re} := by
    intro w hw
    exact ((differentiableAt_jacobiTheta (by simpa using hw)).comp w (by fun_prop)).differentiableWithinAt
  have hT0 := (hT.differentiableAt (ho.mem_nhds hi)).hasDerivAt.comp z (hasDerivAt_inv hz0)
  have hT1 := ((hT.deriv ho).differentiableAt (ho.mem_nhds hi)).hasDerivAt.comp z (hasDerivAt_inv hz0)
  have hA := ((hT0.neg).div ((hasDerivAt_id z).const_mul 2) (mul_ne_zero (by norm_num) hz0)).sub
    (hT1.div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz0))
  have hq := (hasDerivAt_id z).cpow_const (c := ((-1 / 2 : ℝ) : ℂ))
    (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  have hprod := hq.mul hA
  have he : deriv T =ᶠ[𝓝 z] (fun w : ℂ => q w * A w) := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact (hasDerivAt_theta_modular540 w hw).deriv
  have hcp : z ^ (((-1 / 2 : ℝ) : ℂ) - 1) = q z / z := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  have hp : HasDerivAt (fun w : ℂ => q w * A w)
      (q z * (3 * T z⁻¹ / (4 * z ^ 2) + 3 * deriv T z⁻¹ / z ^ 3 +
        deriv (deriv T) z⁻¹ / z ^ 4)) z := by
    convert hprod using 1
    · ext w
      simp [q, A, Function.comp_def]
    · simp only [Function.comp_apply, id_eq, mul_one, hcp, Pi.sub_apply, Pi.div_apply,
        Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat, pow_one]
      dsimp [A, q]
      push_cast
      field_simp
      ring
  have hsecond := hp.congr_of_eventuallyEq he
  have hfirst := (hasDerivAt_theta_modular540 z hz).deriv
  change deriv T z = q z * A z at hfirst
  unfold thetaMellinKernel540
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  change z ^ 2 * deriv (deriv T) z + (3 / 2 : ℂ) * z * deriv T z =
    q z * ((z⁻¹) ^ 2 * deriv (deriv T) z⁻¹ + (3 / 2 : ℂ) * z⁻¹ * deriv T z⁻¹)
  rw [hsecond.deriv, hfirst]
  dsimp [A, q]
  field_simp
  ring

/-- Hardy 1914 page 1012 display 1, the proved differentiated modular identity on an interior ray. -/
theorem theta_ray_modular540 (φ x : ℝ) (hφ : |φ| < Real.pi / 2) (hx : 0 < x) :
    thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) =
      ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) ^ ((-1 / 2 : ℝ) : ℂ) *
        thetaMellinKernel540 ((x⁻¹ : ℝ) * Complex.exp (((-φ : ℝ) : ℂ) * I)) := by
  have hh := theta_kernel_modular540 _ (ray_positive_re540 φ x hφ hx)
  have hi : ((x : ℂ) * Complex.exp ((φ : ℂ) * I))⁻¹ =
      (x⁻¹ : ℝ) * Complex.exp (((-φ : ℝ) : ℂ) * I) := by
    simp only [mul_inv_rev, ← Complex.exp_neg, Complex.ofReal_inv, Complex.ofReal_neg, neg_mul]
    ring
  simpa only [hi] using hh



/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem theta_ray_zero540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    (fun x : ℝ => thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ (-( -1 : ℝ))) := by
  have hneg : |-φ| < Real.pi / 2 := by simpa using hφ
  obtain ⟨C, hC, htop⟩ := Asymptotics.isBigO_iff'.mp (theta_ray_top540 (-φ) hneg)
  have hinv := (tendsto_inv_nhdsGT_zero.eventually htop)
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hinv, self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x ht hx hx1
  have hxp : 0 < x := hx
  rw [theta_ray_modular540 φ x hφ hxp, norm_mul, Complex.norm_cpow_real]
  have hnorm : ‖(x : ℂ) * Complex.exp ((φ : ℂ) * I)‖ = x := by
    simp [Complex.norm_exp, abs_of_pos hxp]
  rw [hnorm]
  have hpow : (x⁻¹) ^ (-(2 : ℝ)) = x ^ (2 : ℝ) := by
    rw [Real.inv_rpow hxp.le, ← Real.rpow_neg hxp.le, neg_neg]
  have hbound : x ^ (-1 / 2 : ℝ) * ‖thetaMellinKernel540 ((x⁻¹ : ℝ) *
      Complex.exp (((-φ : ℝ) : ℂ) * I))‖ ≤ C * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (C * ‖(x⁻¹) ^ (-(2 : ℝ))‖) :=
        mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hxp.le _)
      _ = C * (x ^ (-1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
        rw [hpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
        ring
      _ = _ := by rw [← Real.rpow_add hxp]; norm_num
  have hsmall : x ^ (3 / 2 : ℝ) ≤ x ^ (1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hxp hx1.le (by norm_num)
  calc
    _ ≤ C * x ^ (3 / 2 : ℝ) := hbound
    _ ≤ C * x ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hsmall hC.le
    _ = _ := by simp only [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos hxp]

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem integrable_theta_ray540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => x ^ (-3 / 4 : ℝ) *
      ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖) (Ioi 0) := by
  have hc := continuousOn_theta_ray540 φ hφ
  have hm := mellinConvergent_of_isBigO_rpow
    (s := (1 / 4 : ℂ)) (a := 2) (b := -1)
    (hc.locallyIntegrableOn measurableSet_Ioi) (theta_ray_top540 φ hφ)
    (by norm_num) (theta_ray_zero540 φ hφ) (by norm_num)
  have hi := (mellin_convergent_iff_norm (s := (1 / 4 : ℂ))
    Subset.rfl measurableSet_Ioi (hc.aestronglyMeasurable measurableSet_Ioi)).mp hm
  convert hi using 1 <;> norm_num

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
noncomputable def hardyAmplitude540 (t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re

/-- Hardy 1914 page 1012 display 1, auxiliary theta ray estimate. -/
theorem continuous_hardyAmplitude540 : Continuous hardyAmplitude540 := by
  have hc : Continuous fun t : ℝ =>
      (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
    apply ContinuousAt.comp (differentiableAt_completedZeta ?_ ?_).continuousAt (by fun_prop)
    all_goals
      intro h
      have := congrArg Complex.re h
      norm_num at this
  exact hc.const_mul _

/-- Hardy 1914 page 1012, the displayed definition of Xi. -/
noncomputable def hardyXi515 (t : ℝ) : ℝ :=
  -((1 / 4 : ℝ) + t ^ 2) / 2 *
    (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re

/-- Hardy 1914 page 1013 displays 2 and 3, smoothness from the exponential majorant. -/
theorem contDiffOn_expMoment540 (f : ℝ → ℝ) (hf : Continuous f) (φ C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ C * Real.exp (-φ * t))
    (m n : ℕ) : ContDiffOn ℝ m (expMoment540 f n) {α : ℝ | |α| < φ} := by
  have ho : IsOpen {α : ℝ | |α| < φ} := isOpen_lt continuous_abs continuous_const
  have hd (k : ℕ) : DifferentiableOn ℝ (expMoment540 f k) {α : ℝ | |α| < φ} := by
    intro α hα
    exact (hasDerivAt_expMoment540 f hf φ C hC hbound k α hα).differentiableAt.differentiableWithinAt
  induction m generalizing n with
  | zero => exact contDiffOn_zero.mpr (hd n).continuousOn
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ENat) = (m : WithTop ENat) + 1 by simp]
    apply (contDiffOn_succ_iff_deriv_of_isOpen ho).mpr
    refine ⟨hd n, by simp, ?_⟩
    exact (ih (n + 1)).congr fun α hα =>
      (hasDerivAt_expMoment540 f hf φ C hC hbound n α hα).deriv

/-- Hardy 1914 page 1012 display 1, the Mathlib theta Mellin form in its convergence region. -/
theorem completedZeta_theta_mellin540 (w : ℂ) (hw : 1 / 2 < w.re) :
    completedRiemannZeta (2 * w) =
      mellin (fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) w / 2 := by
  have hk (x : ℝ) : (HurwitzZeta.evenKernel 0 x : ℂ) = jacobiTheta (I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  have h := ((HurwitzZeta.hurwitzEvenFEPair 0).hasMellin (s := w) hw).2
  change (HurwitzZeta.hurwitzEvenFEPair 0).Λ (2 * w / 2) / 2 = _
  rw [show (2 : ℂ) * w / 2 = w by ring, ← h]
  congr 1
  congr 1
  ext x
  simp [HurwitzZeta.hurwitzEvenFEPair, hk]


/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem mellin_euler_derivative540 (f f' : ℝ → ℂ) (s : ℂ) (hs : s ≠ 0)
    (hf : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hfi : MellinConvergent f s)
    (hdi : MellinConvergent (fun x : ℝ => (x : ℂ) * f' x) s)
    (hzero : Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) (𝓝[>] 0) (𝓝 0))
    (htop : Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) atTop (𝓝 0)) :
    mellin (fun x : ℝ => (x : ℂ) * f' x) s = -s * mellin f s := by
  have hpow (x : ℝ) (hx : 0 < x) : (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hh := Complex.cpow_add (s - 1) 1 hx0
    simpa only [sub_add_cancel, Complex.cpow_one] using hh.symm
  have hi1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * f' x) (Ioi 0) := by
    apply hdi.congr_fun _ measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul]
    rw [← mul_assoc, hpow x hx]
  have hi2 : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * f x) (Ioi 0) := by
    have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using hfi
    simpa only [IntegrableOn, mul_assoc] using hi.const_mul s
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x : ℂ) ^ s) (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (v := f) (v' := f') (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (fun x hx => hasDerivAt_ofReal_cpow_const hx.ne' hs)
    (fun x hx => hf x hx) hi1 hi2 hzero htop
  simp only [sub_zero, zero_sub] at h
  calc
    _ = ∫ x : ℝ in Ioi 0, (x : ℂ) ^ s * f' x := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul]
      rw [← mul_assoc, hpow x hx]
    _ = -(∫ x : ℝ in Ioi 0, (s * (x : ℂ) ^ (s - 1)) * f x) := h
    _ = -s * mellin f s := by
      rw [mellin, ← integral_neg, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul]
      ring

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_sector_rectangle540 (s : ℂ) (a b φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    let F : ℂ → ℂ := fun z => Complex.exp (s * z) * thetaMellinKernel540 (Complex.exp z)
    (∫ x : ℝ in a..b, F (x : ℂ)) - (∫ x : ℝ in a..b, F ((x : ℂ) + (φ : ℂ) * I)) +
      I * (∫ y : ℝ in 0..φ, F ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in 0..φ, F ((a : ℂ) + (y : ℂ) * I)) = 0 := by
  dsimp only
  let F : ℂ → ℂ := fun z => Complex.exp (s * z) * thetaMellinKernel540 (Complex.exp z)
  have hdiff : DifferentiableOn ℂ F (Complex.Rectangle (a : ℂ) ((b : ℂ) + (φ : ℂ) * I)) := by
    intro z hz
    have him : z.im ∈ uIcc 0 φ := by simpa [Complex.Rectangle] using hz.2
    have hi : |z.im| ≤ |φ| := by
      rcases mem_uIcc.mp him with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
        linarith [h.1]
    have hr : 0 < (Complex.exp z).re := by
      rw [Complex.exp_re]
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hi.trans_lt hφ)))
    have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    have hk := differentiableOn_thetaMellinKernel540.differentiableAt (ho.mem_nhds hr)
    exact ((by fun_prop : DifferentiableAt ℂ (fun u => Complex.exp (s * u)) z).mul
      (hk.comp z (by fun_prop))).differentiableWithinAt
  simpa [F, Complex.Rectangle, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (a : ℂ)
      ((b : ℂ) + (φ : ℂ) * I) hdiff

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_sector_top540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ v : ℝ, |v| ≤ |φ| →
      ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((v : ℂ) * I))‖ ≤ C * x ^ (-(2 : ℝ)) := by
  let c : ℝ := Real.cos φ
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ)
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have ha : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  have ht : Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-(Real.pi * c) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℕ) (Real.pi * c) ha
  have he : ∀ᶠ x : ℝ in atTop, x ^ 4 * Real.exp (-(Real.pi * c) * x) ≤ 1 :=
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun x hx => hx.le)
  refine ⟨11 * C * Real.exp (Real.pi / 2), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (1 / c)), he] with x hx hex
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxp : 0 < x := by linarith
  have hxc : 1 ≤ x * c := by
    have hh := (le_max_right 1 (1 / c)).trans hx
    exact (div_le_iff₀ hc).mp hh
  intro v hv
  have hvcos : c ≤ Real.cos v := by
    dsimp [c]
    rw [← Real.cos_abs φ, ← Real.cos_abs v]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hv
  let z : ℂ := (x : ℂ) * Complex.exp ((v : ℂ) * I)
  have hzr : x * c ≤ z.re := by simpa [z, Complex.exp_re] using mul_le_mul_of_nonneg_left hvcos hxp.le
  have hzn : ‖z‖ = x := by simp [z, norm_mul, Complex.norm_exp, abs_of_pos hxp]
  have hb := theta_kernel_bound540 z (hxc.trans hzr)
  rw [hzn] at hb
  have hbe : Real.exp (-Real.pi * (z.re - 1 / 2)) ≤ Real.exp (-Real.pi * (x * c - 1 / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hb' : ‖thetaMellinKernel540 z‖ ≤
      (8 * x ^ 2 + 3 * x) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := by
    exact hb.trans (mul_le_mul_of_nonneg_left hbe (by positivity))
  have hp : 8 * x ^ 2 + 3 * x ≤ 11 * x ^ 2 := by nlinarith
  have hExp : Real.exp (-Real.pi * (x * c - 1 / 2)) =
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * c) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : x ^ 2 * Real.exp (-(Real.pi * c) * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two]
    rw [← one_div (x ^ 2)]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ ≤ (8 * x ^ 2 + 3 * x) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := hb'
    _ ≤ (11 * x ^ 2) * C * Real.exp (-Real.pi * (x * c - 1 / 2)) := by gcongr
    _ = (11 * C * Real.exp (Real.pi / 2)) *
        (x ^ 2 * Real.exp (-(Real.pi * c) * x)) := by rw [hExp]; ring
    _ ≤ (11 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_sector_zero540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in 𝓝[>] 0, ∀ v : ℝ, |v| ≤ |φ| →
      ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((v : ℂ) * I))‖ ≤ C * x := by
  obtain ⟨C, hC, htop⟩ := theta_sector_top540 φ hφ
  have hinv := (tendsto_inv_nhdsGT_zero.eventually htop)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hinv, self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x ht hx hx1
  have hxp : 0 < x := hx
  intro v hv
  have hvφ : |v| < Real.pi / 2 := hv.trans_lt hφ
  have ht' := ht (-v) (by simpa using hv)
  rw [theta_ray_modular540 v x hvφ hxp, norm_mul, Complex.norm_cpow_real]
  have hnorm : ‖(x : ℂ) * Complex.exp ((v : ℂ) * I)‖ = x := by
    simp [Complex.norm_exp, abs_of_pos hxp]
  rw [hnorm]
  have hpow : (x⁻¹) ^ (-(2 : ℝ)) = x ^ (2 : ℝ) := by
    rw [Real.inv_rpow hxp.le, ← Real.rpow_neg hxp.le, neg_neg]
  have hbound : x ^ (-1 / 2 : ℝ) * ‖thetaMellinKernel540 ((x⁻¹ : ℝ) *
      Complex.exp (((-v : ℝ) : ℂ) * I))‖ ≤ C * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) * (C * (x⁻¹) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg hxp.le _)
      _ = C * (x ^ (-1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
        rw [hpow]
        ring
      _ = _ := by rw [← Real.rpow_add hxp]; norm_num
  have hsmall : x ^ (3 / 2 : ℝ) ≤ x ^ (1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hxp hx1.le (by norm_num)
  calc
    _ ≤ C * x ^ (3 / 2 : ℝ) := hbound
    _ ≤ C * x ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hsmall hC.le
    _ = _ := by rw [Real.rpow_one]

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_arc_bound540 (φ t u C k : ℝ) (hC : 0 ≤ C)
    (hK : ∀ v ∈ uIcc 0 φ,
      ‖thetaMellinKernel540 (Complex.exp ((u : ℂ) + (v : ℂ) * I))‖ ≤ C * Real.exp (k * u)) :
    ‖∫ v : ℝ in 0..φ, Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) *
      ((u : ℂ) + (v : ℂ) * I)) * thetaMellinKernel540 (Complex.exp ((u : ℂ) + (v : ℂ) * I))‖ ≤
      (C * Real.exp (|t| * |φ|) * Real.exp ((k + 1 / 4) * u)) * |φ| := by
  have hint : ∀ v ∈ uIoc 0 φ,
      ‖Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * ((u : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp ((u : ℂ) + (v : ℂ) * I))‖ ≤
          C * Real.exp (|t| * |φ|) * Real.exp ((k + 1 / 4) * u) := by
    intro v hv
    have habs : |v| ≤ |φ| := by simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hv)
    have htv : -t * v ≤ |t| * |φ| := by
      calc
        _ = -(t * v) := by ring
        _ ≤ |t * v| := neg_le_abs _
        _ = |t| * |v| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    have hphase : ‖Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) *
        ((u : ℂ) + (v : ℂ) * I))‖ = Real.exp (u / 4 - t * v) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [norm_mul, hphase]
    calc
      _ ≤ Real.exp (u / 4 + |t| * |φ|) * (C * Real.exp (k * u)) :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hK v (uIoc_subset_uIcc hv))
          (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by
        rw [Real.exp_add, ← mul_assoc]
        rw [show u / 4 = (1 / 4 : ℝ) * u by ring,
          show (k + 1 / 4) * u = (1 / 4 : ℝ) * u + k * u by ring, Real.exp_add]
        ring
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const hint

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_outer_arc540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..φ,
      Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * ((R : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp ((R : ℂ) + (v : ℂ) * I))) atTop (𝓝 0) := by
  obtain ⟨C, hC, htop⟩ := theta_sector_top540 φ hφ
  have he := Real.tendsto_exp_atTop.eventually htop
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖∫ v : ℝ in 0..φ, Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * ((R : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp ((R : ℂ) + (v : ℂ) * I))‖ ≤
      C * Real.exp (|t| * |φ|) * Real.exp (-(7 / 4 : ℝ) * R) * |φ| := by
    filter_upwards [he] with R hR
    have hK (v : ℝ) (hv : v ∈ uIcc 0 φ) :
        ‖thetaMellinKernel540 (Complex.exp ((R : ℂ) + (v : ℂ) * I))‖ ≤ C * Real.exp (-2 * R) := by
      have hb := hR v (by simpa using abs_sub_left_of_mem_uIcc hv)
      have hp : (Real.exp R) ^ (-(2 : ℝ)) = Real.exp (-2 * R) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      simpa only [Complex.exp_add, Complex.ofReal_exp, hp] using hb
    have hb := theta_log_arc_bound540 φ t R C (-2) hC.le hK
    convert hb using 1 <;> norm_num
  have hlim : Tendsto (fun R : ℝ => C * Real.exp (|t| * |φ|) *
      Real.exp (-(7 / 4 : ℝ) * R) * |φ|) atTop (𝓝 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (7 / 4 : ℝ) (by norm_num)
    simpa only [Real.rpow_zero, one_mul, mul_zero, zero_mul] using
      (hh.const_mul (C * Real.exp (|t| * |φ|))).mul_const |φ|
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) hbound hlim)

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem theta_log_inner_arc540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..φ,
      Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * (((-R : ℝ) : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp (((-R : ℝ) : ℂ) + (v : ℂ) * I))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hzero⟩ := theta_sector_zero540 φ hφ
  have he := (Real.tendsto_exp_atBot_nhdsGT.comp tendsto_neg_atTop_atBot).eventually hzero
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖∫ v : ℝ in 0..φ, Complex.exp (((1 / 4 : ℂ) + (t : ℂ) * I) * (((-R : ℝ) : ℂ) + (v : ℂ) * I)) *
        thetaMellinKernel540 (Complex.exp (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
      C * Real.exp (|t| * |φ|) * Real.exp (-(5 / 4 : ℝ) * R) * |φ| := by
    filter_upwards [he] with R hR
    have hK (v : ℝ) (hv : v ∈ uIcc 0 φ) :
        ‖thetaMellinKernel540 (Complex.exp (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ C * Real.exp (1 * -R) := by
      have hb := hR v (by simpa using abs_sub_left_of_mem_uIcc hv)
      simpa only [Function.comp_apply, Complex.exp_add, Complex.ofReal_exp, one_mul] using hb
    have hb := theta_log_arc_bound540 φ t (-R) C 1 hC.le hK
    convert hb using 1 <;> ring
  have hlim : Tendsto (fun R : ℝ => C * Real.exp (|t| * |φ|) *
      Real.exp (-(5 / 4 : ℝ) * R) * |φ|) atTop (𝓝 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (5 / 4 : ℝ) (by norm_num)
    simpa only [Real.rpow_zero, one_mul, mul_zero, zero_mul] using
      (hh.const_mul (C * Real.exp (|t| * |φ|))).mul_const |φ|
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) hbound hlim)

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem mellin_ray_log_integrand540 (w : ℂ) (φ u : ℝ) :
    Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (φ : ℂ) * I)) =
    Complex.exp ((φ : ℂ) * I * w) *
      ((Real.exp u : ℂ) * ((Real.exp u : ℂ) ^ (w - 1) *
        thetaMellinKernel540 ((Real.exp u : ℂ) * Complex.exp ((φ : ℂ) * I)))) := by
  have hp : (Real.exp u : ℂ) ^ (w - 1) = Complex.exp ((u : ℂ) * (w - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have he : Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) =
      Complex.exp ((φ : ℂ) * I * w) * (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (w - 1) := by
    rw [hp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  ring

/-- Hardy 1914 page 1012 display 1, auxiliary Mellin and sector calculus. -/
theorem mellin_ray_log540 (w : ℂ) (φ : ℝ) :
    (∫ u : ℝ, Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (φ : ℂ) * I))) =
    Complex.exp ((φ : ℂ) * I * w) *
      ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (w - 1) *
        thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) *
    thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))
  rw [← integral_comp_exp g, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  simpa only [g, Complex.real_smul] using mellin_ray_log_integrand540 w φ u

/-- Hardy 1914 page 1012 display 1, proved sector rotation of the corrected theta Mellin integral. -/
theorem theta_mellin_rotate540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 (x : ℂ)) =
    Complex.exp ((φ : ℂ) * I * ((1 / 4 : ℂ) + (t : ℂ) * I)) *
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I)) := by
  let w : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  let F : ℂ → ℂ := fun z => Complex.exp (w * z) * thetaMellinKernel540 (Complex.exp z)
  have hlog (ψ : ℝ) (hψ : |ψ| < Real.pi / 2) :
      Integrable (fun u : ℝ => F ((u : ℂ) + (ψ : ℂ) * I)) := by
    let g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) *
      thetaMellinKernel540 ((x : ℂ) * Complex.exp ((ψ : ℂ) * I))
    have hc := continuousOn_theta_ray540 ψ hψ
    have hm := mellinConvergent_of_isBigO_rpow (s := w) (a := 2) (b := -1)
      (hc.locallyIntegrableOn measurableSet_Ioi) (theta_ray_top540 ψ hψ)
      (by dsimp [w]; norm_num) (theta_ray_zero540 ψ hψ) (by dsimp [w]; norm_num)
    have hg : IntegrableOn g (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul, g] using hm
    have hi := ((integrable_comp_exp g).mpr hg).const_mul (Complex.exp ((ψ : ℂ) * I * w))
    apply hi.congr
    filter_upwards [] with u
    simpa only [F, g, Complex.real_smul] using (mellin_ray_log_integrand540 w ψ u).symm
  have h0 := hlog 0 (by simpa using (by positivity : (0 : ℝ) < Real.pi / 2))
  have hφint := hlog φ hφ
  have hA := intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have hB := intervalIntegral_tendsto_integral hφint tendsto_neg_atTop_atBot tendsto_id
  have hout := theta_log_outer_arc540 φ t hφ
  have hin := theta_log_inner_arc540 φ t hφ
  have hlim := ((hA.sub hB).add (hout.const_mul I)).sub (hin.const_mul I)
  simp only [mul_zero, add_zero, sub_zero] at hlim
  have hconst : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop
      (𝓝 ((∫ u : ℝ, F ((u : ℂ) + (0 : ℂ) * I)) -
        ∫ u : ℝ, F ((u : ℂ) + (φ : ℂ) * I))) := by
    apply hlim.congr'
    filter_upwards [] with R
    simpa only [id_eq, F, w, Complex.ofReal_zero, zero_mul, add_zero] using
      theta_log_sector_rectangle540 w (-R) R φ hφ
  have heq := sub_eq_zero.mp (tendsto_nhds_unique hconst tendsto_const_nhds)
  change (∫ u : ℝ, Complex.exp (w * ((u : ℂ) + (0 : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (0 : ℂ) * I))) =
    (∫ u : ℝ, Complex.exp (w * ((u : ℂ) + (φ : ℂ) * I)) *
      thetaMellinKernel540 (Complex.exp ((u : ℂ) + (φ : ℂ) * I))) at heq
  have hz := mellin_ray_log540 w 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.exp_zero, one_mul, mul_one] at hz
  simp only [zero_mul, add_zero] at heq
  rw [hz, mellin_ray_log540 w φ] at heq
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] using heq

/-- Hardy 1914 page 1012, the unshifted theta contour at real part one. -/
noncomputable def hardyUnshifted540 (α : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(α : ℂ) * I * ((1 : ℂ) + (t : ℂ) * I)) *
    completedRiemannZeta (2 * ((1 : ℂ) + (t : ℂ) * I))

/-! ## (A1) `Γ(1+it)Γ(1-it) = π t / sinh(π t)` -/

private theorem gamma_prod_540 (t : ℝ) (ht : t ≠ 0) :
    Complex.Gamma (1 + (t : ℂ) * Complex.I) * Complex.Gamma (1 - (t : ℂ) * Complex.I) =
      ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
  have hI : ((t : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    simpa using ht
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 + (t : ℂ) * Complex.I)) =
      -(((Real.sinh (Real.pi * t)) : ℂ)) * Complex.I := by
    have harg : (Real.pi : ℂ) * (1 + (t : ℂ) * Complex.I) =
        (Real.pi : ℂ) + (((Real.pi * t : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.sin_add_mul_I, Complex.sin_pi, Complex.cos_pi]
    rw [← Complex.ofReal_sinh]
    ring
  have href := Complex.Gamma_mul_Gamma_one_sub (1 + (t : ℂ) * Complex.I)
  rw [show (1 : ℂ) - (1 + (t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) by ring, hsin] at href
  have hone := Complex.Gamma_add_one (-((t : ℂ) * Complex.I)) (neg_ne_zero.mpr hI)
  rw [show -((t : ℂ) * Complex.I) + 1 = 1 - (t : ℂ) * Complex.I by
    rw [sub_eq_add_neg, add_comm]] at hone
  rw [hone, ← mul_assoc, mul_comm (Complex.Gamma (1 + (t : ℂ) * Complex.I)),
    mul_assoc, href]
  push_cast
  field_simp

/-- `|π t / sinh(π t)| ≤ 60 (1+|t|) e^{-π|t|}`. -/
private theorem abs_pi_div_sinh_le_540 (t : ℝ) :
    |Real.pi * t / Real.sinh (Real.pi * t)| ≤
      60 * (1 + |t|) * Real.exp (-Real.pi * |t|) := by
  have hpi := Real.pi_pos
  rcases eq_or_ne t 0 with h0 | ht
  · subst h0
    simp
  have hspos : 0 < |t| := abs_pos.mpr ht
  have hval : |Real.pi * t / Real.sinh (Real.pi * t)| =
      Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
    rw [abs_div, abs_mul, abs_of_pos hpi, Real.abs_sinh, abs_mul, abs_of_pos hpi]
  rw [hval]
  have hsinhpos : 0 < Real.sinh (Real.pi * |t|) := Real.sinh_pos_iff.mpr (by positivity)
  rcases lt_or_ge (Real.pi * |t|) 1 with hsmall | hbig
  · have hle1 : Real.pi * |t| / Real.sinh (Real.pi * |t|) ≤ 1 := by
      rw [div_le_one hsinhpos]
      have := (Real.self_le_sinh_iff).mpr (le_of_lt (by positivity : (0:ℝ) < Real.pi * |t|))
      linarith
    have hprod : Real.exp (-Real.pi * |t|) * Real.exp (Real.pi * |t|) = 1 := by
      rw [← Real.exp_add]; simp
    have hexp3 : (1/3 : ℝ) ≤ Real.exp (-Real.pi * |t|) := by
      have hb : Real.exp (Real.pi * |t|) ≤ 3 := by
        have h1 : Real.exp (Real.pi * |t|) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        linarith [Real.exp_one_lt_three]
      have hp : (0:ℝ) < Real.exp (-Real.pi * |t|) := Real.exp_pos _
      nlinarith [Real.exp_pos (Real.pi * |t|)]
    have hlow : (1:ℝ) ≤ 60 * (1 + |t|) * Real.exp (-Real.pi * |t|) := by
      have h1 : (1:ℝ) ≤ 60 * (1 + |t|) := by nlinarith
      have hp : (0:ℝ) < Real.exp (-Real.pi * |t|) := Real.exp_pos _
      nlinarith
    linarith
  · have hsinh_low : Real.exp (Real.pi * |t|) / 3 ≤ Real.sinh (Real.pi * |t|) := by
      have heq : Real.sinh (Real.pi * |t|) =
          (Real.exp (Real.pi * |t|) - Real.exp (-(Real.pi * |t|))) / 2 := Real.sinh_eq _
      have hbig1 : 1 ≤ Real.pi * |t| := hbig
      have hb : 2 ≤ Real.exp (Real.pi * |t|) := by
        have := Real.add_one_le_exp (Real.pi * |t|)
        linarith
      have hprod : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
        rw [← Real.exp_add]; simp
      have hp1 : (0:ℝ) < Real.exp (-(Real.pi * |t|)) := Real.exp_pos _
      have hp2 : (0:ℝ) < Real.exp (Real.pi * |t|) := Real.exp_pos _
      rw [heq]
      nlinarith
    have hstep : Real.pi * |t| / Real.sinh (Real.pi * |t|) ≤
        3 * Real.pi * |t| * Real.exp (-(Real.pi * |t|)) := by
      rw [div_le_iff₀ hsinhpos]
      have key : Real.exp (Real.pi * |t|) / 3 * (3 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) =
          Real.pi * |t| := by
        have h1 : Real.exp (Real.pi * |t|) * Real.exp (-(Real.pi * |t|)) = 1 := by
          rw [← Real.exp_add]; simp
        calc Real.exp (Real.pi * |t|) / 3 * (3 * Real.pi * |t| * Real.exp (-(Real.pi * |t|)))
            = (Real.exp (Real.pi * |t|) * Real.exp (-(Real.pi * |t|))) * (Real.pi * |t|) := by ring
          _ = Real.pi * |t| := by rw [h1, one_mul]
      calc Real.pi * |t|
          = Real.exp (Real.pi * |t|) / 3 *
            (3 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) := key.symm
        _ ≤ Real.sinh (Real.pi * |t|) * (3 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) :=
            mul_le_mul_of_nonneg_right hsinh_low (by positivity)
        _ = 3 * Real.pi * |t| * Real.exp (-(Real.pi * |t|)) * Real.sinh (Real.pi * |t|) := by ring
    have h3 : 3 * Real.pi * |t| ≤ 60 * (1 + |t|) := by
      have hplt : (3:ℝ) * Real.pi ≤ 60 := by nlinarith [Real.pi_lt_four]
      have habs : (0:ℝ) ≤ |t| := abs_nonneg t
      nlinarith
    have h5 : Real.exp (-(Real.pi * |t|)) = Real.exp (-Real.pi * |t|) := by
      congr 1
      ring
    rw [h5] at hstep
    have he2 : (0:ℝ) < Real.exp (-Real.pi * |t|) := Real.exp_pos _
    have h4 : 3 * Real.pi * |t| * Real.exp (-Real.pi * |t|) ≤
        60 * (1 + |t|) * Real.exp (-Real.pi * |t|) :=
      mul_le_mul_of_nonneg_right h3 he2.le
    linarith

/-- `‖Γ(1+it)‖ ≤ 8 (1+|t|) e^{-(π/2)|t|}`. -/
private theorem gamma_norm_bound_540 (t : ℝ) :
    ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤
      8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  rcases eq_or_ne t 0 with h0 | ht
  · subst h0
    have h1 : Complex.Gamma (1 + ((0:ℝ) : ℂ) * Complex.I) = 1 := by
      simp
    rw [h1, norm_one]
    have he : Real.exp (-(Real.pi / 2) * |(0:ℝ)|) = 1 := by simp
    rw [he, mul_one, abs_zero]
    norm_num
  · have hc1 : starRingEnd ℂ (1 + (t : ℂ) * Complex.I) = 1 - (t : ℂ) * Complex.I := by
      rw [sub_eq_add_neg]
      simp
    have hconj : Complex.Gamma (1 - (t : ℂ) * Complex.I) =
        starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I)) := by
      rw [← hc1]
      exact Complex.Gamma_conj _
    have hnorm : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2 =
        |Real.pi * t / Real.sinh (Real.pi * t)| := by
      have hprod := gamma_prod_540 t ht
      have h2 : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I) *
          Complex.Gamma (1 - (t : ℂ) * Complex.I)‖ =
          ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2 := by
        rw [hconj, Complex.norm_mul, sq,
          show ‖starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I))‖ =
            ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ from norm_star _]
      rw [← h2, hprod, Complex.norm_real, Real.norm_eq_abs]
    set s := |t| with hs
    have hs0 : 0 ≤ s := by rw [hs]; exact abs_nonneg t
    have hexp : (Real.exp (-(Real.pi / 2) * s)) ^ 2 = Real.exp (-Real.pi * s) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hsq : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2 ≤
        (8 * (1 + s) * Real.exp (-(Real.pi / 2) * s)) ^ 2 := by
      rw [hnorm]
      have hb := abs_pi_div_sinh_le_540 t
      rw [← hs] at hb
      have hexp2 : (8 * (1 + s) * Real.exp (-(Real.pi / 2) * s)) ^ 2 =
          64 * (1 + s) ^ 2 * Real.exp (-Real.pi * s) := by
        rw [mul_pow, mul_pow, hexp]
        ring
      rw [hexp2]
      have he : 0 < Real.exp (-Real.pi * s) := Real.exp_pos _
      have h1 : 0 ≤ 1 + s := by linarith
      nlinarith
    have hnn : 0 ≤ 8 * (1 + s) * Real.exp (-(Real.pi / 2) * s) := by positivity
    have hstep := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hstep
    rwa [hs]

/-! ## (A2) integrability of the exponential majorants -/

/-- `(1+t)^n ≤ 2^n (1+t^n)` for `0 ≤ t`. -/
private theorem one_add_pow_le_540 (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have hmax : 1 + t ≤ 2 * max 1 t := by
    rcases le_or_gt 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith
  have hmaxpow : (max 1 t) ^ n ≤ 1 + t ^ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    rcases le_or_gt 1 t with h1 | h1
    · rw [max_eq_right h1]
      have h0 : 0 ≤ t ^ n := pow_nonneg ht n
      linarith
    · rw [max_eq_left h1.le]
      have h0 : 0 ≤ t ^ n := pow_nonneg ht n
      have h1n : (1:ℝ) ^ n = 1 := one_pow n
      rw [h1n]
      linarith
  calc (1 + t) ^ n ≤ (2 * max 1 t) ^ n := pow_le_pow_left₀ (by linarith) hmax n
    _ = 2 ^ n * (max 1 t) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (1 + t ^ n) := by
        apply mul_le_mul_of_nonneg_left hmaxpow
        exact pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n

/-- `t ↦ e^{-ct}(1+t)^n` is integrable on `Ioi 0`. -/
private theorem integrableOn_exp_mul_pow_540 (c : ℝ) (hc : 0 < c) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t)) * (1 + t) ^ n) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := c)
      (by norm_num) (by norm_num) hc
    simpa using this
  have h2 : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(c * t))) (Ioi 0) := by
    have hn1 : (-1:ℝ) < (n : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := c)
      hn1 (by norm_num) hc
    simpa [Real.rpow_natCast] using this
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-(c * t)) * (1 + t ^ n)) (Ioi 0) := by
    have h := h1.add h2
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t _
    show Real.exp (-(c * t)) + t ^ n * Real.exp (-(c * t)) =
      Real.exp (-(c * t)) * (1 + t ^ n)
    ring
  have hmaj : IntegrableOn (fun t : ℝ =>
      (2:ℝ) ^ n * (Real.exp (-(c * t)) * (1 + t ^ n))) (Ioi 0) := h3.const_mul _
  refine hmaj.mono' ?_ ?_
  · have hc1 : Continuous fun t : ℝ => Real.exp (-(c * t)) := by fun_prop
    have hc2 : Continuous fun t : ℝ => (1 + t) ^ n := by fun_prop
    exact (hc1.mul hc2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpos : (0:ℝ) ≤ Real.exp (-(c * t)) := (Real.exp_pos _).le
    have ht' : (0:ℝ) < t := ht
    have hnn2 : (0:ℝ) ≤ (1 + t) ^ n := pow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpos hnn2)]
    calc Real.exp (-(c * t)) * (1 + t) ^ n
        ≤ Real.exp (-(c * t)) * (2 ^ n * (1 + t ^ n)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le_540 t ht.le n) hpos
      _ = 2 ^ n * (Real.exp (-(c * t)) * (1 + t ^ n)) := by ring

/-- `t ↦ e^{-c|t|}(1+|t|)^n` is integrable. -/
private theorem exp_abs_pow_integrable_540 (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ => Real.exp (-(c * |t|)) * (1 + |t|) ^ n) := by
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|)) * (1 + |t|) ^ n) (Ioi 0) := by
    refine (integrableOn_exp_mul_pow_540 c hc n).congr_fun ?_ measurableSet_Ioi
    intro t ht
    show Real.exp (-(c * t)) * (1 + t) ^ n = Real.exp (-(c * |t|)) * (1 + |t|) ^ n
    rw [abs_of_pos ht]
  have hIic : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|)) * (1 + |t|) ^ n) (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
      (f := fun t : ℝ => Real.exp (-(c * |t|)) * (1 + |t|) ^ n) (s := Set.Ioi 0) (μ := volume)
    have hset : (Set.Iio (0:ℝ)) = Neg.neg ⁻¹' (Set.Ioi (0:ℝ)) := by
      ext z
      simp
    rw [hset]
    refine (hmp.mpr hIoi).congr_fun ?_ ?_
    · intro t _
      show Real.exp (-(c * |-t|)) * (1 + |-t|) ^ n =
        Real.exp (-(c * |t|)) * (1 + |t|) ^ n
      rw [abs_neg]
    · rw [← hset]
      exact measurableSet_Iio
  have hun : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|)) * (1 + |t|) ^ n)
      (Ioi 0 ∪ Iic 0) := hIoi.union hIic
  rwa [Set.Ioi_union_Iic, integrableOn_univ] at hun

/-! ## (A3) exponential decay of `Λ(2+2it)` -/

/-- The `ζ` factor on the line `Re = 2` is bounded by `∑ 1/n²`. -/
private theorem norm_tsum_zeta_line_540 (t : ℝ) :
    ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)‖ ≤
      ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
  have hterm : ∀ n : ℕ,
      ‖(1 : ℂ) / (n : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)‖ = (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h
      simp only [Nat.cast_zero]
      have hz : (0:ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I) = 0 := by
        apply Complex.zero_cpow
        intro hc
        have := congrArg Complex.re hc
        norm_num at this
      rw [hz, div_zero, norm_zero]
      norm_num
    · have hn : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      have hcast : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by push_cast; ring
      have hval : ‖(((n : ℝ)) : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)‖ = (n : ℝ) ^ 2 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hn]
        have hre : (2 + 2 * (t : ℂ) * Complex.I).re = 2 := by simp
        rw [hre, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [norm_div, norm_one, hcast, hval]
  have hfun : (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)‖) =
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := funext hterm
  have hZ : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  calc ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)‖ :=
        norm_tsum_le_tsum_norm (hfun ▸ hZ)
    _ = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by rw [hfun]

/-- `‖Λ(2+2it)‖ ≤ K (1+|t|) e^{-(π/2)|t|}`. -/
private theorem completedZeta_line_bound_540 :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖ ≤
        K * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  classical
  set Z := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 with hZdef
  have hZnn : 0 ≤ Z := tsum_nonneg (fun n => by positivity)
  refine ⟨8 * Real.pi⁻¹ * (Z + 1), by positivity, fun t => ?_⟩
  have hs : (1:ℝ) < (2 + 2 * (t : ℂ) * Complex.I).re := by simp
  have hfac : 2 + 2 * (t : ℂ) * Complex.I = 2 * (1 + (t : ℂ) * Complex.I) := by ring
  rw [completedZeta_eq_tsum_of_one_lt_re hs, hfac]
  rw [show -(2 * (1 + (t : ℂ) * Complex.I)) / 2 = -(1 + (t : ℂ) * Complex.I) by ring]
  rw [show 2 * (1 + (t : ℂ) * Complex.I) / 2 = (1 + (t : ℂ) * Complex.I) by ring]
  rw [norm_mul, norm_mul]
  have hpi : ‖(Real.pi : ℂ) ^ (-(1 + (t : ℂ) * Complex.I))‖ = Real.pi⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-(1 + (t : ℂ) * Complex.I)).re = -1 := by simp
    rw [hre, Real.rpow_neg_one]
  rw [hpi]
  have hZle : ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 * (1 + (t : ℂ) * Complex.I))‖ ≤ Z := by
    have h := norm_tsum_zeta_line_540 t
    have heq : (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ (2 * (1 + (t : ℂ) * Complex.I))) =
        (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ (2 + 2 * (t : ℂ) * Complex.I)) := by
      funext n
      congr 2
      ring
    rw [heq]
    exact h
  have hπpos : (0:ℝ) < Real.pi⁻¹ := by positivity
  have h1 := gamma_norm_bound_540 t
  have hstep : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ *
      ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 * (1 + (t : ℂ) * Complex.I))‖ ≤
      (8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Z :=
    mul_le_mul h1 hZle (norm_nonneg _) (by positivity)
  have hbound : Real.pi⁻¹ * ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ *
      ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 * (1 + (t : ℂ) * Complex.I))‖ ≤
      Real.pi⁻¹ * (8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Z := by
    calc Real.pi⁻¹ * ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ *
          ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 * (1 + (t : ℂ) * Complex.I))‖
        = Real.pi⁻¹ * (‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ *
          ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (2 * (1 + (t : ℂ) * Complex.I))‖) := by ring
      _ ≤ Real.pi⁻¹ * ((8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Z) :=
          mul_le_mul_of_nonneg_left hstep hπpos.le
      _ = Real.pi⁻¹ * (8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Z := by ring
  refine le_trans hbound ?_
  have hZ1 : Z ≤ Z + 1 := by linarith
  have hpos2 : (0:ℝ) ≤ Real.pi⁻¹ * (8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) := by
    positivity
  calc Real.pi⁻¹ * (8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Z
      ≤ Real.pi⁻¹ * (8 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * (Z + 1) := by
        apply mul_le_mul_of_nonneg_left hZ1 hpos2
    _ = 8 * Real.pi⁻¹ * (Z + 1) * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by ring

/-! ## (C1) the strip `|Im u| < π/2`, and the identity theorem -/

private theorem isOpen_strip_540 : IsOpen {u : ℂ | |u.im| < Real.pi / 2} :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

private theorem convex_strip_540 : Convex ℝ {u : ℂ | |u.im| < Real.pi / 2} := by
  have h : {u : ℂ | |u.im| < Real.pi / 2} =
      Complex.imCLM ⁻¹' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Complex.imCLM_apply, Set.mem_Ioo, abs_lt,
      and_comm]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap

/-- Identity principle in the strip: two holomorphic functions agreeing on the reals agree on the
strip. -/
private theorem strip_identity_540 (A B : ℂ → ℂ)
    (hA : DifferentiableOn ℂ A {u : ℂ | |u.im| < Real.pi / 2})
    (hB : DifferentiableOn ℂ B {u : ℂ | |u.im| < Real.pi / 2})
    (hreal : ∀ x : ℝ, A (x : ℂ) = B (x : ℂ)) :
    ∀ u : ℂ, |u.im| < Real.pi / 2 → A u = B u := by
  have hAan : AnalyticOnNhd ℂ A {u : ℂ | |u.im| < Real.pi / 2} :=
    hA.analyticOnNhd isOpen_strip_540
  have hBan : AnalyticOnNhd ℂ B {u : ℂ | |u.im| < Real.pi / 2} :=
    hB.analyticOnNhd isOpen_strip_540
  have hmem : ((1 / 2 : ℝ) : ℂ) ∈ closure (({z : ℂ | A z = B z}) \ {((1 / 2 : ℝ) : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(((1 / 2 + ε / 2 : ℝ)) : ℂ), ?_, ?_⟩
    · simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      refine ⟨hreal (1 / 2 + ε / 2), ?_⟩
      intro h
      have h' : (1 / 2 + ε / 2 : ℝ) = 1 / 2 := by exact_mod_cast h
      linarith
    · have hdiff : ((1 / 2 : ℝ) : ℂ) - (((1 / 2 + ε / 2 : ℝ)) : ℂ) = (((-(ε / 2)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
      linarith
  have h0 : ((1 / 2 : ℝ) : ℂ) ∈ {u : ℂ | |u.im| < Real.pi / 2} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]
    exact half_pos Real.pi_pos
  exact fun u hu => hAan.eqOn_of_preconnected_of_mem_closure hBan
    (convex_strip_540.isPreconnected) h0 hmem hu

/-- The theta side `u ↦ π e^u (θ(i e^u) - 1)` is holomorphic on the strip. -/
private theorem differentiable_strip_theta_540 :
    DifferentiableOn ℂ (fun u : ℂ => (Real.pi : ℂ) *
      (Complex.exp u * (jacobiTheta (Complex.I * Complex.exp u) - 1)))
      {u : ℂ | |u.im| < Real.pi / 2} := by
  intro u hu
  have hre : 0 < (Complex.exp u).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hu))
  have him : (Complex.I * Complex.exp u).im = (Complex.exp u).re := by simp
  have hd1 : DifferentiableAt ℂ jacobiTheta (Complex.I * Complex.exp u) :=
    differentiableAt_jacobiTheta (by rw [him]; exact hre)
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.I * z) (Complex.exp u) := by fun_prop
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta (Complex.I * z)) (Complex.exp u) :=
    hd1.comp (Complex.exp u) hd2
  have hd4 : DifferentiableAt ℂ (fun u : ℂ => jacobiTheta (Complex.I * Complex.exp u)) u :=
    hd3.comp u Complex.differentiableAt_exp
  have hprod : DifferentiableAt ℂ
      (fun u : ℂ => Complex.exp u * (jacobiTheta (Complex.I * Complex.exp u) - 1)) u :=
    Complex.differentiableAt_exp.mul (hd4.sub_const 1)
  exact (hprod.const_mul (Real.pi : ℂ)).differentiableWithinAt

/-! ## (C2) differentiability of `u ↦ ∫ exp(-(t u) I) Λ(2+2it) dt` on the strip -/

private theorem hasDerivAt_strip_integral_540
    (K : ℝ) (hKpos : 0 < K)
    (hK : ∀ t : ℝ, ‖completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖ ≤
      K * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|))
    (u : ℂ) (hu : |u.im| < Real.pi / 2) :
    HasDerivAt (fun w : ℂ => ∫ t : ℝ, Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I))
      (∫ t : ℝ, (-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * u) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)) u := by
  classical
  set θ := |u.im| with hθ
  set r := (Real.pi / 2 - θ) / 2 with hr
  have hθlt : θ < Real.pi / 2 := hu
  have hrpos : 0 < r := by rw [hr]; linarith
  have hr_eq : Real.pi / 2 - (θ + r) = r := by rw [hr]; ring
  have himw : ∀ w ∈ Metric.ball u r, |w.im| ≤ θ + r := by
    intro w hw
    have hd : ‖w - u‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h1 : |w.im - u.im| ≤ ‖w - u‖ := by
      simpa using Complex.abs_im_le_norm (w - u)
    have h2 : w.im = u.im + (w.im - u.im) := by ring
    calc |w.im| = |u.im + (w.im - u.im)| := congrArg abs h2
      _ ≤ |u.im| + |w.im - u.im| := abs_add_le _ _
      _ ≤ θ + r := by rw [hθ]; linarith
  have hexp_re : ∀ (t : ℝ) (w : ℂ), (-((t : ℂ) * w) * Complex.I).re = t * w.im := by
    intro t w
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hexp_bound : ∀ (t : ℝ) (w : ℂ), |w.im| ≤ θ + r →
      ‖Complex.exp (-((t : ℂ) * w) * Complex.I)‖ ≤ Real.exp ((θ + r) * |t|) := by
    intro t w hw
    rw [Complex.norm_exp, hexp_re]
    apply Real.exp_le_exp.mpr
    calc t * w.im ≤ |t * w.im| := le_abs_self _
      _ = |t| * |w.im| := abs_mul _ _
      _ ≤ |t| * (θ + r) := mul_le_mul_of_nonneg_left hw (abs_nonneg t)
      _ = (θ + r) * |t| := by ring
  have hΛcont : ∀ t : ℝ, ContinuousAt completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I) := by
    intro t
    have hne0 : (2 + 2 * (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hne1 : (2 + 2 * (t : ℂ) * Complex.I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    exact (differentiableAt_completedZeta hne0 hne1).continuousAt
  have hFcont : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (-((t : ℂ) * w) * Complex.I) *
      completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I) := by
    intro w
    rw [continuous_iff_continuousAt]
    intro t
    have hg : ContinuousAt (fun u : ℝ => 2 + 2 * (u : ℂ) * Complex.I) t := by fun_prop
    have hcomp : ContinuousAt (fun u : ℝ => completedRiemannZeta (2 + 2 * (u : ℂ) * Complex.I)) t :=
      ContinuousAt.comp (f := fun u : ℝ => 2 + 2 * (u : ℂ) * Complex.I)
        (g := completedRiemannZeta) (x := t) (hΛcont t) hg
    exact (by fun_prop : ContinuousAt (fun t : ℝ => Complex.exp (-((t : ℂ) * w) * Complex.I)) t).mul hcomp
  have hF'cont : ∀ w : ℂ, Continuous fun t : ℝ =>
      (-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I) := by
    intro w
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun t : ℝ =>
        (-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * w) * Complex.I)) t := by fun_prop
    have hg : ContinuousAt (fun u : ℝ => 2 + 2 * (u : ℂ) * Complex.I) t := by fun_prop
    have hcomp : ContinuousAt (fun u : ℝ => completedRiemannZeta (2 + 2 * (u : ℂ) * Complex.I)) t :=
      ContinuousAt.comp (f := fun u : ℝ => 2 + 2 * (u : ℂ) * Complex.I)
        (g := completedRiemannZeta) (x := t) (hΛcont t) hg
    exact h1.mul hcomp
  have hcomb : ∀ t : ℝ, Real.exp ((θ + r) * |t|) * Real.exp (-(Real.pi / 2) * |t|) =
      Real.exp (-(r * |t|)) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    have hsum : (θ + r) + -(Real.pi / 2) = -r := by rw [hr]; ring
    calc (θ + r) * |t| + -(Real.pi / 2) * |t| = ((θ + r) + -(Real.pi / 2)) * |t| := by ring
      _ = -r * |t| := by rw [hsum]
      _ = -(r * |t|) := by ring
  have hnormF : ∀ w ∈ Metric.ball u r, ∀ t : ℝ,
      ‖Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖ ≤
        K * (1 + |t|) * Real.exp (-(r * |t|)) := by
    intro w hw t
    have hexp_le := hexp_bound t w (himw w hw)
    have hΛ := hK t
    calc ‖Complex.exp (-((t : ℂ) * w) * Complex.I) *
          completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖
        = ‖Complex.exp (-((t : ℂ) * w) * Complex.I)‖ *
          ‖completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖ := norm_mul _ _
      _ ≤ Real.exp ((θ + r) * |t|) * (K * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) := by
          apply mul_le_mul hexp_le hΛ (norm_nonneg _) (Real.exp_pos _).le
      _ = K * (1 + |t|) * Real.exp (-(r * |t|)) := by rw [← hcomb t]; ring
  have hnormF' : ∀ w ∈ Metric.ball u r, ∀ t : ℝ,
      ‖(-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖ ≤
        K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|)) := by
    intro w hw t
    have hexp_le := hexp_bound t w (himw w hw)
    have hΛ := hK t
    have hc : ‖(-((t : ℂ)) * Complex.I)‖ = |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hkey : |t| * (Real.exp ((θ + r) * |t|) *
          (K * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|))) =
        K * (|t| * (1 + |t|)) * Real.exp (-(r * |t|)) := by
      rw [← hcomb t]; ring
    have hquad : |t| * (1 + |t|) ≤ (1 + |t|) ^ 2 := by
      have h7 : (0:ℝ) ≤ |t| := abs_nonneg t
      nlinarith
    calc ‖(-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * w) * Complex.I) *
          completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖
        = |t| * (‖Complex.exp (-((t : ℂ) * w) * Complex.I)‖ *
          ‖completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)‖) := by
            rw [norm_mul, norm_mul, hc]
            ring
      _ ≤ |t| * (Real.exp ((θ + r) * |t|) *
          (K * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
            apply mul_le_mul hexp_le hΛ (norm_nonneg _) (Real.exp_pos _).le
      _ = K * (|t| * (1 + |t|)) * Real.exp (-(r * |t|)) := hkey
      _ ≤ K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|)) := by
          have hpos : (0:ℝ) ≤ K * Real.exp (-(r * |t|)) := by positivity
          have hstep := mul_le_mul_of_nonneg_left hquad hpos
          calc K * (|t| * (1 + |t|)) * Real.exp (-(r * |t|))
              = (K * Real.exp (-(r * |t|))) * (|t| * (1 + |t|)) := by ring
            _ ≤ (K * Real.exp (-(r * |t|))) * ((1 + |t|) ^ 2) := hstep
            _ = K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|)) := by ring
  have hbound_int : Integrable (fun t : ℝ => K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|))) := by
    have h1 := exp_abs_pow_integrable_540 r hrpos 2
    have h2 := h1.const_mul K
    refine h2.congr ?_
    filter_upwards [] with t
    ring
  have hint : Integrable (fun t : ℝ => Complex.exp (-((t : ℂ) * u) * Complex.I) *
      completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)) := by
    refine Integrable.mono' hbound_int (hFcont u).aestronglyMeasurable ?_
    filter_upwards [] with t
    have h := hnormF u (Metric.mem_ball_self hrpos) t
    have h6 : (1 + |t|) ≤ (1 + |t|) ^ 2 := by
      have h7 : (0:ℝ) ≤ |t| := abs_nonneg t
      nlinarith
    have hpos : (0:ℝ) ≤ K * Real.exp (-(r * |t|)) := by positivity
    have hstep : K * (1 + |t|) * Real.exp (-(r * |t|)) ≤
        K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|)) := by
      calc K * (1 + |t|) * Real.exp (-(r * |t|))
          = (K * Real.exp (-(r * |t|))) * (1 + |t|) := by ring
        _ ≤ (K * Real.exp (-(r * |t|))) * (1 + |t|) ^ 2 :=
            mul_le_mul_of_nonneg_left h6 hpos
        _ = K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|)) := by ring
    linarith
  have hdiff : ∀ t : ℝ, ∀ w ∈ Metric.ball u r,
      HasDerivAt (fun w : ℂ => Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I))
        ((-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * w) * Complex.I) *
          completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)) w := by
    intro t w _
    have h1 : HasDerivAt (fun w : ℂ => (t : ℂ) * w) ((t : ℂ)) w := by
      simpa using (hasDerivAt_id w).const_mul (t : ℂ)
    have h2 : HasDerivAt (fun w : ℂ => -((t : ℂ) * w)) (-((t : ℂ))) w := h1.neg
    have h3 : HasDerivAt (fun w : ℂ => -((t : ℂ) * w) * Complex.I) (-((t : ℂ)) * Complex.I) w :=
      h2.mul_const Complex.I
    have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-((t : ℂ) * w) * Complex.I))
        (Complex.exp (-((t : ℂ) * w) * Complex.I) * (-((t : ℂ)) * Complex.I)) w :=
      (Complex.hasDerivAt_exp (-((t : ℂ) * w) * Complex.I)).comp w h3
    have h4 := hexp.mul_const (completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I))
    convert h4 using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := fun t : ℝ => K * (1 + |t|) ^ 2 * Real.exp (-(r * |t|)))
    (F := fun w t => Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I))
    (F' := fun w t => (-((t : ℂ)) * Complex.I) * Complex.exp (-((t : ℂ) * w) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I))
    (s := Metric.ball u r) (Metric.ball_mem_nhds u hrpos)
    (by filter_upwards [Metric.ball_mem_nhds u hrpos] with w _; exact (hFcont w).aestronglyMeasurable)
    hint ((hF'cont u).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t w hw => hnormF' w hw t))
    hbound_int (Filter.Eventually.of_forall hdiff)).2

/-! ## (B) Mellin inversion at a real point -/

private theorem axis_identity_540
    (hmellin : ∀ w : ℂ, 1 / 2 < w.re →
      completedRiemannZeta (2 * w) =
        mellin (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) w / 2)
    (htop : (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) =O[atTop]
      (fun x : ℝ => x ^ (-(2 : ℝ))))
    (hzero : (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))))
    (x : ℝ) (hx : 0 < x) :
    (∫ t : ℝ, Complex.exp (-((t : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)) =
      Real.pi * x * (jacobiTheta (Complex.I * (x : ℂ)) - 1) := by
  classical
  have hthcont : ∀ y : ℝ, 0 < y →
      ContinuousAt (fun z : ℝ => jacobiTheta (Complex.I * (z : ℂ)) - 1) y := by
    intro y hy
    have him : (Complex.I * (y : ℂ)).im = y := by simp
    have hd : DifferentiableAt ℂ jacobiTheta (Complex.I * (y : ℂ)) :=
      differentiableAt_jacobiTheta (by rw [him]; exact hy)
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta (Complex.I * z)) (y : ℂ) :=
      hd.comp (y : ℂ) (by fun_prop)
    have hc : ContinuousAt (fun z : ℝ => jacobiTheta (Complex.I * (z : ℂ))) y :=
      (hd2.continuousAt).comp (Complex.continuous_ofReal.continuousAt (x := y))
    exact (hc.sub continuousAt_const)
  have hcont : ContinuousOn (fun y : ℝ => jacobiTheta (Complex.I * (y : ℂ)) - 1) (Ioi 0) :=
    fun y hy => (hthcont y hy).continuousWithinAt
  have hmc : MellinConvergent (fun y : ℝ => (jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2) 1 := by
    have hmain : MellinConvergent (fun y : ℝ => jacobiTheta (Complex.I * (y : ℂ)) - 1) 1 := by
      refine mellinConvergent_of_isBigO_rpow (s := (1 : ℂ)) (a := 2) (b := 1/2)
        (hcont.locallyIntegrableOn measurableSet_Ioi) htop ?_ hzero ?_
      · show (1:ℂ).re < 2
        rw [Complex.one_re]
        norm_num
      · show (1:ℝ)/2 < (1:ℂ).re
        rw [Complex.one_re]
        norm_num
    exact hmain.div_const 2
  have hmellin' : ∀ y : ℝ, mellin (fun z : ℝ => (jacobiTheta (Complex.I * (z : ℂ)) - 1) / 2)
      ((1 : ℝ) + (y : ℂ) * Complex.I) = completedRiemannZeta (2 * (1 + (y : ℂ) * Complex.I)) := by
    intro y
    have hre1 : (1 + (y : ℂ) * Complex.I).re = 1 := by simp
    have hw : (1 / 2 : ℝ) < (1 + (y : ℂ) * Complex.I).re := by rw [hre1]; norm_num
    have h := hmellin (1 + (y : ℂ) * Complex.I) hw
    rw [show ((1 : ℝ) + (y : ℂ) * Complex.I) = (1 + (y : ℂ) * Complex.I) by push_cast; ring]
    rw [h, mellin_div_const]
  have hΛc : ∀ y : ℝ, ContinuousAt completedRiemannZeta (2 * (1 + (y : ℂ) * Complex.I)) := by
    intro y
    have hne0 : (2 * (1 + (y : ℂ) * Complex.I)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hne1 : (2 * (1 + (y : ℂ) * Complex.I)) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    exact (differentiableAt_completedZeta hne0 hne1).continuousAt
  have hFf : Complex.VerticalIntegrable
      (mellin (fun y : ℝ => (jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2)) 1 := by
    obtain ⟨K, hKpos, hK⟩ := completedZeta_line_bound_540
    have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
    have hmaj := exp_abs_pow_integrable_540 (Real.pi / 2) hpi2 1
    have hdecay : Integrable (fun y : ℝ => completedRiemannZeta (2 * (1 + (y : ℂ) * Complex.I))) := by
      refine Integrable.mono' (hmaj.const_mul K) ?_ ?_
      · have hcont2 : Continuous fun y : ℝ => completedRiemannZeta (2 * (1 + (y : ℂ) * Complex.I)) := by
          rw [continuous_iff_continuousAt]
          intro y
          exact ContinuousAt.comp (f := fun u : ℝ => 2 * (1 + (u : ℂ) * Complex.I))
            (g := completedRiemannZeta) (x := y) (hΛc y)
            (by fun_prop : ContinuousAt (fun u : ℝ => 2 * (1 + (u : ℂ) * Complex.I)) y)
        exact hcont2.aestronglyMeasurable
      · filter_upwards [] with y
        have h := hK y
        have h1 : (2 * (1 + (y : ℂ) * Complex.I)) = (2 + 2 * (y : ℂ) * Complex.I) := by ring
        rw [h1]
        have heq : K * (Real.exp (-(Real.pi / 2 * |y|)) * (1 + |y|) ^ 1) =
            K * (1 + |y|) * Real.exp (-(Real.pi / 2) * |y|) := by
          rw [pow_one]
          ring
        rw [heq]
        exact h
    refine hdecay.congr ?_
    filter_upwards [] with y
    exact (hmellin' y).symm
  have hfcont : ContinuousAt (fun y : ℝ => (jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2) x :=
    (hthcont x hx).div_const 2
  have hinv := mellinInv_mellin_eq 1 (fun y : ℝ => (jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2)
    hx hmc hFf hfcont
  rw [mellinInv] at hinv
  simp only [smul_eq_mul, one_div] at hinv
  have hlogeq : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      rfl
    · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]
      rfl
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hexp_log : Complex.exp (-((Real.log x : ℝ) : ℂ)) = ((x : ℂ))⁻¹ := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hx,
      Complex.ofReal_inv]
  have hpt : ∀ y : ℝ, (x : ℂ) ^ (-((1 : ℝ) + (y : ℂ) * Complex.I)) *
      mellin (fun z : ℝ => (jacobiTheta (Complex.I * (z : ℂ)) - 1) / 2)
        ((1 : ℝ) + (y : ℂ) * Complex.I)
      = (x : ℂ)⁻¹ * (Complex.exp (-((y : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) *
        completedRiemannZeta (2 + 2 * (y : ℂ) * Complex.I)) := by
    intro y
    have hm : mellin (fun z : ℝ => (jacobiTheta (Complex.I * (z : ℂ)) - 1) / 2)
        ((1 : ℝ) + (y : ℂ) * Complex.I) = completedRiemannZeta (2 + 2 * (y : ℂ) * Complex.I) := by
      rw [hmellin']
      congr 1
      ring
    have hcp : (x : ℂ) ^ (-((1 : ℝ) + (y : ℂ) * Complex.I)) =
        (x : ℂ)⁻¹ * Complex.exp (-((y : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero hx0, hlogeq]
      rw [show ((Real.log x : ℝ) : ℂ) * -((1 : ℝ) + (y : ℂ) * Complex.I) =
          -((Real.log x : ℝ) : ℂ) + (-((y : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) by
        push_cast
        ring_nf]
      rw [Complex.exp_add, hexp_log]
      try ring
    rw [hcp, hm]
    ring
  have hcongr : (fun y : ℝ => (x : ℂ) ^ (-((1 : ℝ) + (y : ℂ) * Complex.I)) *
      mellin (fun z : ℝ => (jacobiTheta (Complex.I * (z : ℂ)) - 1) / 2)
        ((1 : ℝ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => (x : ℂ)⁻¹ * (Complex.exp (-((y : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) *
        completedRiemannZeta (2 + 2 * (y : ℂ) * Complex.I))) := funext hpt
  rw [hcongr, integral_const_mul] at hinv
  have hkey : (jacobiTheta (Complex.I * (x : ℂ)) - 1) =
      2 * ((2 * (Real.pi : ℂ))⁻¹ * ((x : ℂ)⁻¹ * ∫ t : ℝ,
        Complex.exp (-((t : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I))) := by
    have h' : (2 * (Real.pi : ℂ))⁻¹ * ((x : ℂ)⁻¹ * ∫ t : ℝ,
        Complex.exp (-((t : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) *
        completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)) =
        (jacobiTheta (Complex.I * (x : ℂ)) - 1) / 2 := by
      have h2 := hinv
      simp only [Complex.real_smul] at h2
      rw [← h2]
      push_cast
      ring
    rw [h']
    ring
  rw [hkey]
  set J : ℂ := ∫ t : ℝ, Complex.exp (-((t : ℂ) * ((Real.log x : ℝ) : ℂ)) * Complex.I) *
      completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I) with hJ
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hπ
  have hc1 : (Real.pi : ℂ) * 2 * (2 * (Real.pi : ℂ))⁻¹ = 1 := by
    rw [mul_comm (Real.pi : ℂ) 2, mul_inv_cancel₀ h2π]
  have hc2 : (x : ℂ) * (x : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  show J = (Real.pi : ℂ) * (x : ℂ) * (2 * ((2 * (Real.pi : ℂ))⁻¹ * ((x : ℂ)⁻¹ * J)))
  rw [show (Real.pi : ℂ) * (x : ℂ) * (2 * ((2 * (Real.pi : ℂ))⁻¹ * ((x : ℂ)⁻¹ * J)))
      = ((Real.pi : ℂ) * 2 * (2 * (Real.pi : ℂ))⁻¹) * ((x : ℂ) * (x : ℂ)⁻¹) * J by ring,
    hc1, hc2, one_mul, one_mul]

/-! ## (D) assembly -/

private theorem hardy_unshifted_theta540_core
    (hmellin : ∀ w : ℂ, 1 / 2 < w.re →
      completedRiemannZeta (2 * w) =
        mellin (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) w / 2)
    (htop : (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) =O[atTop]
      (fun x : ℝ => x ^ (-(2 : ℝ))))
    (hzero : (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))))
    (α : ℝ) (hα : |α| < Real.pi / 2) :
    (∫ t : ℝ, Complex.exp (-(α : ℂ) * Complex.I * ((1 : ℂ) + (t : ℂ) * Complex.I)) *
        completedRiemannZeta (2 * ((1 : ℂ) + (t : ℂ) * Complex.I))) =
      (Real.pi : ℂ) * (jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1) := by
  classical
  obtain ⟨K, hKpos, hK⟩ := completedZeta_line_bound_540
  set A : ℂ → ℂ := fun u => ∫ t : ℝ, Complex.exp (-((t : ℂ) * u) * Complex.I) *
      completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I) with hA
  set B : ℂ → ℂ := fun u => (Real.pi : ℂ) *
      (Complex.exp u * (jacobiTheta (Complex.I * Complex.exp u) - 1)) with hB
  have hAdiff : DifferentiableOn ℂ A {u : ℂ | |u.im| < Real.pi / 2} := by
    intro u hu
    exact (hasDerivAt_strip_integral_540 K hKpos hK u hu).differentiableAt.differentiableWithinAt
  have hBdiff : DifferentiableOn ℂ B {u : ℂ | |u.im| < Real.pi / 2} :=
    differentiable_strip_theta_540
  have hreal : ∀ u : ℝ, A (u : ℂ) = B (u : ℂ) := by
    intro u
    have hx : 0 < Real.exp u := Real.exp_pos u
    have h := axis_identity_540 hmellin htop hzero (Real.exp u) hx
    rw [Real.log_exp] at h
    simp only [hA, hB]
    rw [h, Complex.ofReal_exp]
    ring
  have hstrip := strip_identity_540 A B hAdiff hBdiff hreal
  have hiu : |(((α : ℂ) * Complex.I)).im| < Real.pi / 2 := by
    have him : (((α : ℂ) * Complex.I)).im = α := by simp
    rw [him]
    exact hα
  have hAval := hstrip ((α : ℂ) * Complex.I) hiu
  simp only [hA, hB] at hAval
  have hpt : ∀ t : ℝ, Complex.exp (-(α : ℂ) * Complex.I * ((1 : ℂ) + (t : ℂ) * Complex.I)) *
      completedRiemannZeta (2 * ((1 : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (-(α : ℂ) * Complex.I) *
        (Complex.exp (-((t : ℂ) * ((α : ℂ) * Complex.I)) * Complex.I) *
          completedRiemannZeta (2 + 2 * (t : ℂ) * Complex.I)) := by
    intro t
    have h1 : -(α : ℂ) * Complex.I * ((1 : ℂ) + (t : ℂ) * Complex.I) =
        -(α : ℂ) * Complex.I + (-((t : ℂ) * ((α : ℂ) * Complex.I)) * Complex.I) := by ring
    have h2 : 2 * ((1 : ℂ) + (t : ℂ) * Complex.I) = 2 + 2 * (t : ℂ) * Complex.I := by ring
    rw [h1, h2, Complex.exp_add]
    ring
  rw [funext hpt, integral_const_mul, hAval]
  have hexp : Complex.exp (-(α : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  calc Complex.exp (-(α : ℂ) * Complex.I) *
        ((Real.pi : ℂ) * (Complex.exp ((α : ℂ) * Complex.I) *
          (jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1)))
      = (Real.pi : ℂ) * (Complex.exp (-(α : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I)) *
        (jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1) := by ring
    _ = (Real.pi : ℂ) * (jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1) := by
        rw [hexp]; ring

/-- The two theta bounds, proved here so that the leaf below does not depend on a
declaration that appears later in the file. -/
private theorem theta_raw_bounds540' :
    ((fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) =O[atTop]
      (fun x : ℝ => x ^ (-(2 : ℝ)))) ∧
    ((fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))) := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hk (x : ℝ) : (HurwitzZeta.evenKernel 0 x : ℂ) = jacobiTheta (Complex.I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  have he : (fun x : ℝ => P.f x - P.f₀) =
      (fun x : ℝ => jacobiTheta (Complex.I * (x : ℂ)) - 1) := by
    ext x
    simp [P, HurwitzZeta.hurwitzEvenFEPair, hk]
  constructor
  · rw [← he]
    exact P.hf_top (-2)
  · rw [← he]
    exact P.hf_zero'


/-- LEAF Hardy 1914 page 1012, the unshifted display before display 1.
The line has real part one and the theta parameter has positive real part.
This is the unshifted complex theta transform, before crossing the pole. -/
theorem hardy_unshifted_theta540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    hardyUnshifted540 α = (Real.pi : ℂ) *
      (jacobiTheta (I * Complex.exp ((α : ℂ) * I)) - 1) := by
  have h := hardy_unshifted_theta540_core completedZeta_theta_mellin540 theta_raw_bounds540'.1
    theta_raw_bounds540'.2 α hα
  simpa only [hardyUnshifted540] using h


/-! ## (E0) copies of the later theta/xi decay chain (needed above leaf 2) -/

private theorem theta_euler_top540b540 :
    (fun x : ℝ => (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have hlim : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-Real.pi * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℕ) Real.pi Real.pi_pos
  have he : ∀ᶠ x : ℝ in atTop, x ^ 3 * Real.exp (-Real.pi * x) ≤ 1 :=
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono fun x hx => hx.le
  have hd : deriv (fun w : ℂ => jacobiTheta (I * w) - 1) =
      deriv (fun w : ℂ => jacobiTheta (I * w)) := by
    ext w
    exact deriv_sub_const 1
  refine Asymptotics.isBigO_iff.mpr ⟨2 * C * Real.exp (Real.pi / 2), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with x hx hex
  have hxp : 0 < x := by linarith
  have hb := theta_cauchy_bound540 1 (x : ℂ) hx
  rw [iteratedDeriv_one, hd] at hb
  norm_num at hb
  have hbound : ‖deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ)‖ ≤
      2 * C * Real.exp (-Real.pi * (x - 1 / 2)) := by dsimp [C]; convert hb using 1 <;> ring
  have hfin : x * Real.exp (-Real.pi * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two, ← one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ = x * ‖deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]
    _ ≤ x * (2 * C * Real.exp (-Real.pi * (x - 1 / 2))) :=
      mul_le_mul_of_nonneg_left hbound hxp.le
    _ = (2 * C * Real.exp (Real.pi / 2)) * (x * Real.exp (-Real.pi * x)) := by
      rw [show -Real.pi * (x - 1 / 2) = Real.pi / 2 + -Real.pi * x by ring, Real.exp_add]
      ring
    _ ≤ (2 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]

private theorem theta_euler_zero540b540 :
    (fun x : ℝ => (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Cf, hCf, hf⟩ := Asymptotics.isBigO_iff'.mp theta_raw_bounds540'.1
  obtain ⟨Cd, hCd, hd⟩ := Asymptotics.isBigO_iff'.mp theta_euler_top540b540
  have hfi := tendsto_inv_nhdsGT_zero.eventually hf
  have hdi := tendsto_inv_nhdsGT_zero.eventually hd
  have hy := tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop (1 : ℝ))
  refine Asymptotics.isBigO_iff.mpr ⟨(Cf + 1) / 2 + Cd, ?_⟩
  filter_upwards [hfi, hdi, hy, self_mem_nhdsWithin] with x hfx hdx hyx hx
  have hxp : 0 < x := hx
  have hp : (x⁻¹) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hyx (by norm_num)
  have hpn : ‖(x⁻¹) ^ (-(2 : ℝ))‖ ≤ 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hxp.le) _)]
  have hfb : ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1‖ ≤ Cf := by
    simpa only [mul_one] using hfx.trans (mul_le_mul_of_nonneg_left hpn hCf.le)
  have hdb : ‖((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)‖ ≤ Cd := by
    simpa only [mul_one] using hdx.trans (mul_le_mul_of_nonneg_left hpn hCd.le)
  have htheta : ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))‖ ≤ Cf + 1 := by
    calc
      _ = ‖(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by simpa using add_le_add_right hfb 1
  have hform : (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ) =
      (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) *
        (-(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))) / 2 -
          ((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)) := by
    rw [(hasDerivAt_theta_modular540 (x : ℂ) hxp).deriv]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hxp.ne'] <;> ring
  have hrest : ‖-(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))) / 2 -
      ((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)‖ ≤ (Cf + 1) / 2 + Cd := by
    apply (norm_sub_le _ _).trans
    rw [norm_div, norm_neg]
    norm_num only [Complex.norm_ofNat]
    exact add_le_add (div_le_div_of_nonneg_right htheta (by norm_num)) hdb
  rw [hform, norm_mul, Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hxp, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
  simpa only [neg_div, mul_comm] using
    mul_le_mul_of_nonneg_left hrest (Real.rpow_nonneg hxp.le (-1 / 2))

private theorem theta_weighted_boundary540b540 (f : ℝ → ℂ)
    (htop : f =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))))
    (hzero : f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ))))
    (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 2) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) (𝓝[>] 0) (𝓝 0) := by
  have general (l : Filter ℝ) (r : ℝ) (hpos : ∀ᶠ x : ℝ in l, 0 < x)
      (hf : f =O[l] (fun x : ℝ => x ^ r))
      (hr : Tendsto (fun x : ℝ => x ^ (w.re + r)) l (𝓝 0)) :
      Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) l (𝓝 0) := by
    obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp hf
    have he : ∀ᶠ x : ℝ in l, ‖(x : ℂ) ^ w * f x‖ ≤ C * x ^ (w.re + r) := by
      filter_upwards [hb, hpos] with x hx hxp
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      calc
        _ ≤ x ^ w.re * (C * ‖x ^ r‖) :=
          mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hxp.le _)
        _ = C * x ^ (w.re + r) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _), Real.rpow_add hxp]
          ring
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) he
        (by simpa only [mul_zero] using hr.const_mul C))
  constructor
  · apply general atTop (-2) (eventually_gt_atTop 0) htop
    rw [show w.re + -(2 : ℝ) = -(2 - w.re) by ring]
    exact tendsto_rpow_neg_atTop (show 0 < 2 - w.re by linarith)
  · apply general (𝓝[>] 0) (-(1 / 2)) self_mem_nhdsWithin hzero
    have hp : 0 < w.re + -(1 / 2 : ℝ) := by linarith
    have hh0 : Tendsto (fun x : ℝ => x ^ (w.re + -(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.zero_rpow hp.ne'] using (Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)
    exact hh0.mono_left nhdsWithin_le_nhds

private theorem theta_kernel_mellin_right540b540 (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 2) :
    mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      2 * w * (w - 1 / 2) * completedRiemannZeta (2 * w) := by
  let T : ℂ → ℂ := fun z => jacobiTheta (I * z)
  let G : ℝ → ℂ := fun x => T (x : ℂ) - 1
  let E : ℝ → ℂ := fun x => (x : ℂ) * deriv T (x : ℂ)
  let E' : ℝ → ℂ := fun x => deriv T (x : ℂ) + (x : ℂ) * deriv (deriv T) (x : ℂ)
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw1; linarith
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hT : DifferentiableOn ℂ T {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_jacobiTheta (by simpa using hz)).comp z (by fun_prop)).differentiableWithinAt
  have hfG (x : ℝ) (hx : 0 < x) : HasDerivAt G (deriv T (x : ℂ)) x := by
    exact ((hT.differentiableAt (ho.mem_nhds hx)).hasDerivAt.sub_const 1).comp_ofReal
  have hfE (x : ℝ) (hx : 0 < x) : HasDerivAt E (E' x) x := by
    have hh := ((hasDerivAt_id (x : ℂ)).mul
      ((hT.deriv ho).differentiableAt (ho.mem_nhds hx)).hasDerivAt).comp_ofReal
    simpa only [E, E', Pi.mul_apply, id_eq, one_mul] using hh
  have hmG : MellinConvergent G w := mellinConvergent_of_isBigO_rpow
    ((continuousOn_of_forall_continuousAt fun x hx => (hfG x hx).continuousAt).locallyIntegrableOn measurableSet_Ioi)
    theta_raw_bounds540'.1 hw2 theta_raw_bounds540'.2 hw1
  have hmE : MellinConvergent E w := mellinConvergent_of_isBigO_rpow
    ((continuousOn_of_forall_continuousAt fun x hx => (hfE x hx).continuousAt).locallyIntegrableOn measurableSet_Ioi)
    theta_euler_top540b540 hw2 theta_euler_zero540b540 hw1
  have hangle : |(0 : ℝ)| < Real.pi / 2 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 2)
  have hcK : ContinuousOn (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa using continuousOn_theta_ray540 0 hangle
  have htK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    simpa using theta_ray_top540 0 hangle
  have hzK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    simpa using theta_ray_zero540 0 hangle
  have hmK : MellinConvergent (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w :=
    mellinConvergent_of_isBigO_rpow (hcK.locallyIntegrableOn measurableSet_Ioi) htK hw2 hzK (by linarith)
  have hiK : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hmK
  have hiE : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * E x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hmE
  have hiD : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((x : ℂ) * E' x)) (Ioi 0) := by
    apply (hiK.sub (hiE.const_mul (1 / 2 : ℂ))).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only [E, E', T, thetaMellinKernel540]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply, Pi.mul_apply]
    ring
  have hmD : MellinConvergent (fun x : ℝ => (x : ℂ) * E' x) w := by
    simpa only [MellinConvergent, smul_eq_mul] using hiD
  have hBG := theta_weighted_boundary540b540 G theta_raw_bounds540'.1 theta_raw_bounds540'.2 w hw1 hw2
  have hBE := theta_weighted_boundary540b540 E theta_euler_top540b540 theta_euler_zero540b540 w hw1 hw2
  have hP0 := mellin_euler_derivative540 G (fun x : ℝ => deriv T (x : ℂ)) w hw0 hfG hmG hmE hBG.2 hBG.1
  have hP1 := mellin_euler_derivative540 E E' w hw0 hfE hmE hmD hBE.2 hBE.1
  have hlin : mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      mellin (fun x : ℝ => (x : ℂ) * E' x) w + (1 / 2 : ℂ) * mellin E w := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [← integral_const_mul, ← integral_add hiD (hiE.const_mul (1 / 2 : ℂ))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [E, E', T, thetaMellinKernel540]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply, Pi.mul_apply]
    ring
  have hM0 : completedRiemannZeta (2 * w) = mellin G w / 2 := completedZeta_theta_mellin540 w hw1
  rw [hlin, hP1, hP0, hM0]
  ring

private theorem theta_kernel_mellin_strip540b540 (w : ℂ) (hw0 : -1 < w.re) (hw2 : w.re < 2) :
    mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      2 * w * (w - 1 / 2) * completedRiemannZeta₀ (2 * w) + 1 / 2 := by
  let U : Set ℂ := {z | -1 < z.re ∧ z.re < 2}
  let M : ℂ → ℂ := mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ))
  let F : ℂ → ℂ := fun z => 2 * z * (z - 1 / 2) * completedRiemannZeta₀ (2 * z) + 1 / 2
  have hangle : |(0 : ℝ)| < Real.pi / 2 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 2)
  have hcK : ContinuousOn (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa using continuousOn_theta_ray540 0 hangle
  have htK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    simpa using theta_ray_top540 0 hangle
  have hzK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    simpa using theta_ray_zero540 0 hangle
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hcv : Convex ℝ U := (convex_Ioo (-1 : ℝ) 2).linear_preimage Complex.reCLM.toLinearMap
  have hM : DifferentiableOn ℂ M U := by
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow
      (hcK.locallyIntegrableOn measurableSet_Ioi) htK hz.2 hzK hz.1).differentiableWithinAt
  have hcomp : Differentiable ℂ (fun z : ℂ => completedRiemannZeta₀ (2 * z)) :=
    differentiable_completedZeta₀.comp (by fun_prop)
  have hF : Differentiable ℂ F := by
    dsimp [F]
    fun_prop
  have hright (z : ℂ) (hz1 : 1 / 2 < z.re) (hz2 : z.re < 2) : M z = F z := by
    have hs0 : 2 * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    have hs1 : 1 - 2 * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    change mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) z = _
    rw [theta_kernel_mellin_right540b540 z hz1 hz2, completedRiemannZeta_eq]
    dsimp [F]
    have hz0 : z ≠ 0 := by intro h; simp [h] at hs0
    field_simp [hs0, hs1, hz0] <;> ring
  have hnear : M =ᶠ[𝓝 (1 : ℂ)] F := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re),
      (isOpen_lt continuous_re continuous_const).mem_nhds
        (by norm_num : (1 : ℂ).re < (2 : ℝ))] with z hz1 hz2
    exact hright z hz1 hz2
  exact (hM.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hF.differentiableOn.analyticOnNhd hU) hcv.isPreconnected (show (1 : ℂ) ∈ U by norm_num [U]) hnear ⟨hw0, hw2⟩

private theorem theta_xi_mellin540b540 (t : ℝ) :
    (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 (x : ℂ) := by
  let w : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  have hm := theta_kernel_mellin_strip540b540 w (by norm_num [w]) (by norm_num [w])
  have hw0 : w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [w] at hh
  have hw1 : 1 - 2 * w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [w] at hh
  have hs : (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I = 2 * w := by
    dsimp [w]
    push_cast
    ring
  have hp : (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) = 2 * w * (w - 1 / 2) := by
    dsimp [w]
    push_cast
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [hs, hp]
  calc
    _ = 2 * w * (w - 1 / 2) * completedRiemannZeta₀ (2 * w) + 1 / 2 := by
      rw [completedRiemannZeta_eq]
      field_simp [hw0, hw1] <;> ring
    _ = mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w := hm.symm
    _ = _ := rfl

private theorem theta_xi_decay540b540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤
    Real.exp (-φ * t) *
      ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
        ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖ := by
  rw [theta_xi_mellin540b540, theta_mellin_rotate540 φ t hφ, norm_mul,
    mellin_ray_phase_norm540]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
          thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, mellin_ray_power_norm540 x t hx]


/-! ## (E1) decay of `Λ` on the critical line `Re = 1/2` -/

private theorem completedZeta_half_line_continuous_540 :
    Continuous fun t : ℝ =>
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hre : ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by simp
  have hne0 : ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [hre] at h'
    norm_num at h'
  have hne1 : ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    rw [hre] at h'
    norm_num at h'
  exact ContinuousAt.comp
    (f := fun s : ℝ => (1 / 2 : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I)
    (g := completedRiemannZeta) (x := t)
    ((differentiableAt_completedZeta hne0 hne1).continuousAt) (by fun_prop)

/-- `‖Λ(1/2+2it)‖` decays exponentially at rate `c < π/2` in both directions. -/
private theorem completedZeta_half_line_decay_540 (c : ℝ) (hc0 : 0 < c) (hc : c < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤
        K * Real.exp (-(c * |t|)) := by
  classical
  set A : ℝ → ℝ := fun ψ => ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
    ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))‖ with hA
  have hAnn : ∀ ψ : ℝ, 0 ≤ A ψ := by
    intro ψ
    exact setIntegral_nonneg measurableSet_Ioi (fun x hx =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (norm_nonneg _))
  have hcge : ∀ t : ℝ, (1 / 8 : ℝ) ≤ ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ)‖ := by
    intro t
    have h1 : (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) =
        -(((((1 / 4 : ℝ) + (2 * t) ^ 2) / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (2 * t)]
  have hkey : ∀ ψ t : ℝ, |ψ| < Real.pi / 2 →
      ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤
        8 * (Real.exp (-(ψ * t)) * A ψ) := by
    intro ψ t hψ
    have h := theta_xi_decay540b540 ψ t hψ
    have h' : ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
        completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤
          Real.exp (-(ψ * t)) * A ψ := by
      simpa only [hA, neg_mul] using h
    have hsplit : ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ)‖ *
        ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤
          Real.exp (-(ψ * t)) * A ψ := by
      rw [← norm_mul]
      exact h'
    have h3 : (1 / 8 : ℝ) *
        ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤
          Real.exp (-(ψ * t)) * A ψ :=
      le_trans (mul_le_mul_of_nonneg_right (hcge t) (norm_nonneg _)) hsplit
    have hA0 := hAnn ψ
    nlinarith [h3]
  have hc1 : |c| < Real.pi / 2 := by rw [abs_of_pos hc0]; exact hc
  have hc2 : |-c| < Real.pi / 2 := by rw [abs_neg, abs_of_pos hc0]; exact hc
  have hKpos : (0:ℝ) < 8 * (A c + A (-c)) + 1 := by
    have h1 := hAnn c
    have h2 := hAnn (-c)
    linarith
  refine ⟨8 * (A c + A (-c)) + 1, hKpos, fun t => ?_⟩
  have hA0 := hAnn c
  have hA1 := hAnn (-c)
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h := hkey c t hc1
    have he : (0:ℝ) < Real.exp (-(c * t)) := Real.exp_pos _
    nlinarith [h]
  · rw [abs_of_neg ht]
    have h := hkey (-c) t hc2
    rw [show -(-c * t) = -(c * -t) by ring] at h
    have he : (0:ℝ) < Real.exp (-(c * -t)) := Real.exp_pos _
    nlinarith [h]

/-- `t ↦ e^{αt} Λ(1/2+2it)` is integrable for `|α| < π/2`. -/
private theorem integrable_exp_mul_half_line_540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    Integrable (fun t : ℝ => Complex.exp ((α : ℂ) * (t : ℂ)) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) := by
  set c : ℝ := (|α| + Real.pi / 2) / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith [abs_nonneg α, Real.pi_pos]
  have hclt : c < Real.pi / 2 := by rw [hcdef]; linarith [abs_lt.mp hα |>.2]
  have hcgt : |α| < c := by rw [hcdef]; linarith [abs_lt.mp hα |>.2]
  obtain ⟨K, hKpos, hK⟩ := completedZeta_half_line_decay_540 c hc0 hclt
  have hgap : (0:ℝ) < c - |α| := by linarith
  have hmaj : Integrable (fun t : ℝ => K * (Real.exp (-((c - |α|) * |t|)) * (1 + |t|) ^ 0)) :=
    (exp_abs_pow_integrable_540 (c - |α|) hgap 0).const_mul K
  refine Integrable.mono' hmaj ?_ ?_
  · have hcont : Continuous fun t : ℝ => Complex.exp ((α : ℂ) * (t : ℂ)) *
        completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) :=
      (by fun_prop : Continuous fun t : ℝ => Complex.exp ((α : ℂ) * (t : ℂ))).mul
        completedZeta_half_line_continuous_540
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with t
    have h1 : ‖Complex.exp ((α : ℂ) * (t : ℂ))‖ = Real.exp (α * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [norm_mul, h1]
    have hΛ := hK t
    have hexp_le : Real.exp (α * t) ≤ Real.exp (|α| * |t|) := by
      apply Real.exp_le_exp.mpr
      calc α * t ≤ |α * t| := le_abs_self _
        _ = |α| * |t| := abs_mul α t
    have he1 : (0:ℝ) < Real.exp (|α| * |t|) := Real.exp_pos _
    have hstep : Real.exp (α * t) *
        ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖
        ≤ Real.exp (|α| * |t|) * (K * Real.exp (-(c * |t|))) :=
      mul_le_mul hexp_le hΛ (norm_nonneg _) he1.le
    refine le_trans hstep ?_
    have hcomb : Real.exp (|α| * |t|) * Real.exp (-(c * |t|)) =
        Real.exp (-((c - |α|) * |t|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfinal : Real.exp (|α| * |t|) * (K * Real.exp (-(c * |t|))) =
        K * (Real.exp (-((c - |α|) * |t|)) * (1 + |t|) ^ 0) := by
      rw [show Real.exp (|α| * |t|) * (K * Real.exp (-(c * |t|)))
          = K * (Real.exp (|α| * |t|) * Real.exp (-(c * |t|))) by ring, hcomb, pow_zero,
        mul_one]
    rw [hfinal]

/-! ## (E2) evenness of `hardyAmplitude540` and the `expMoment` identification -/

/-- Conjugation symmetry of the completed zeta function in the right half plane. -/
theorem completedRiemannZeta_conj_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    completedRiemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hcre : 0 < (starRingEnd ℂ s).re := by simpa using hs
  have hGc : Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Gammaℝ s) := by
    unfold Gammaℝ
    rw [map_mul, ← Complex.Gamma_conj, map_div₀, map_ofNat]
    congr 1
    have hπ : ((Real.pi : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
    have := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) hπ
    rw [Complex.conj_ofReal] at this
    rw [map_div₀, map_neg, map_ofNat] at this
    exact this
  have h1 := riemannZeta_def_of_ne_zero hs0
  have h2 := riemannZeta_def_of_ne_zero hc0
  have g1 := Gammaℝ_ne_zero_of_re_pos hs
  have g2 := Gammaℝ_ne_zero_of_re_pos hcre
  have e1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [h1, div_mul_cancel₀ _ g1]
  have e2 : completedRiemannZeta (starRingEnd ℂ s) =
      riemannZeta (starRingEnd ℂ s) * Gammaℝ (starRingEnd ℂ s) := by
    rw [h2, div_mul_cancel₀ _ g2]
  rw [e2, e1, riemannZeta_conj, hGc, map_mul]

/-- The completed zeta function is real on the critical line. -/
theorem conj_completedRiemannZeta_half_add_mul_I (t : ℝ) :
    starRingEnd ℂ (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  rw [← completedRiemannZeta_conj_of_re_pos _ (by simp)]
  rw [← completedRiemannZeta_one_sub]
  congr 1
  apply Complex.ext <;> norm_num

private theorem completedZeta_half_conj_540 (t : ℝ) :
    completedRiemannZeta ((1 / 2 : ℂ) + ((2 * (-t) : ℝ) : ℂ) * Complex.I) =
      starRingEnd ℂ (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) := by
  have harg : starRingEnd ℂ ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) =
      (1 / 2 : ℂ) + ((2 * (-t) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
  rw [← harg]
  exact completedRiemannZeta_conj_of_re_pos _ (by norm_num)

private theorem hardyAmplitude_even_540 (t : ℝ) : hardyAmplitude540 (-t) = hardyAmplitude540 t := by
  unfold hardyAmplitude540
  rw [completedZeta_half_conj_540 t]
  simp

private theorem reLambdaLine_integrable_540 (β : ℝ) (hβ : |β| < Real.pi / 2) :
    Integrable (fun t : ℝ => Real.exp (β * t) *
      (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) := by
  have hre : Continuous fun t : ℝ =>
      (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re :=
    Complex.continuous_re.comp completedZeta_half_line_continuous_540
  refine Integrable.mono' (integrable_exp_mul_half_line_540 β hβ).norm ?_ ?_
  · exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (β * t)).mul hre).aestronglyMeasurable
  · filter_upwards [] with t
    have hpos : (0:ℝ) ≤ Real.exp (β * t) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h2 := Complex.abs_re_le_norm
      (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))
    calc Real.exp (β * t) *
          |(completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re|
        ≤ Real.exp (β * t) *
          ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left h2 hpos
      _ = ‖Complex.exp ((β : ℂ) * (t : ℂ)) *
          completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ := by
          rw [norm_mul, Complex.norm_exp]
          congr 2
          simp

/-- `2 * expMoment f 0 α` for `f = hardyAmplitude540` as a real integral of `e^{αt} Re Λ(1/2+2it)`. -/
private theorem two_expMoment_eq_540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    2 * expMoment540 hardyAmplitude540 0 α =
      -(∫ t : ℝ, Real.exp (α * t) *
        (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) := by
  classical
  have hInt := reLambdaLine_integrable_540 α hα
  have hInt2 := reLambdaLine_integrable_540 (-α) (by simpa using hα)
  have hf : ∀ t : ℝ, hardyAmplitude540 t =
      -(1 / 2) *
        (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := fun t => rfl
  have hgInt : Integrable (fun x : ℝ => Real.exp (α * x) * hardyAmplitude540 x) := by
    have h := hInt.const_mul (-(1 / 2))
    refine h.congr ?_
    filter_upwards [] with x
    rw [hf x]
    ring
  have hg2Int : Integrable (fun x : ℝ => Real.exp (-(α * x)) * hardyAmplitude540 x) := by
    have h := hInt2.const_mul (-(1 / 2))
    refine h.congr ?_
    filter_upwards [] with x
    rw [hf x]
    ring
  have hsubst : (∫ x : ℝ in Iic 0, Real.exp (α * x) * hardyAmplitude540 x) =
      ∫ x : ℝ in Ioi 0, Real.exp (-(α * x)) * hardyAmplitude540 x := by
    have key := integral_comp_neg_Iic (c := 0)
      (f := fun y : ℝ => Real.exp (-(α * y)) * hardyAmplitude540 y)
    rw [neg_zero] at key
    rw [← key]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x _
    show Real.exp (α * x) * hardyAmplitude540 x =
      Real.exp (-(α * -x)) * hardyAmplitude540 (-x)
    rw [hardyAmplitude_even_540 x]
    ring_nf
  have hsplit : (∫ x : ℝ in Ioi 0,
        (Real.exp (α * x) + Real.exp (-(α * x))) * hardyAmplitude540 x) =
      ∫ x : ℝ, Real.exp (α * x) * hardyAmplitude540 x := by
    have hadd : (∫ x : ℝ in Ioi 0,
          (Real.exp (α * x) + Real.exp (-(α * x))) * hardyAmplitude540 x) =
        (∫ x : ℝ in Ioi 0, Real.exp (α * x) * hardyAmplitude540 x) +
          ∫ x : ℝ in Ioi 0, Real.exp (-(α * x)) * hardyAmplitude540 x := by
      rw [← integral_add hgInt.integrableOn hg2Int.integrableOn]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    rw [hadd, ← hsubst]
    have hcompl := integral_add_compl
      (f := fun x : ℝ => Real.exp (α * x) * hardyAmplitude540 x)
      (s := Set.Ioi 0) measurableSet_Ioi hgInt
    rw [Set.compl_Ioi] at hcompl
    exact hcompl
  have hexpm : expMoment540 hardyAmplitude540 0 α =
      ∫ x : ℝ in Ioi 0, (Real.exp (α * x) + Real.exp (-(α * x))) * hardyAmplitude540 x := by
    unfold expMoment540 expMomentIntegrand540
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    norm_num
  rw [hexpm, hsplit]
  have hre : (∫ x : ℝ, Real.exp (α * x) * hardyAmplitude540 x) =
      -(1 / 2) * ∫ x : ℝ, Real.exp (α * x) *
        (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * x : ℝ) : ℂ) * Complex.I)).re := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hf x]
    ring
  rw [hre]
  ring


/-! ## (E3) residue at `w = 1/2`, integrability on the critical line, and the reduction of leaf 2 -/

/-- The residue of `Λ(2w)` at `w = 1/2` is `1/2`. -/
private theorem residue_half_540 :
    Tendsto (fun w : ℂ => (w - 1 / 2) * completedRiemannZeta (2 * w))
      (𝓝[≠] (1 / 2)) (𝓝 (1 / 2)) := by
  have hres := completedRiemannZeta_residue_one
  have h2 : Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] (1 / 2)) (𝓝[≠] (1 : ℂ)) := by
    have hbase : Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] (1 / 2)) (𝓝 (1 : ℂ)) := by
      have h : Tendsto (fun w : ℂ => 2 * w) (𝓝 (1 / 2)) (𝓝 (2 * (1 / 2))) :=
        tendsto_const_nhds.mul tendsto_id
      have h2 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
      rw [h2] at h
      have hle : 𝓝[≠] (1 / 2 : ℂ) ≤ 𝓝 (1 / 2) := nhdsWithin_le_nhds
      exact h.mono_left hle
    refine tendsto_nhdsWithin_iff.mpr ⟨hbase, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw h
    apply hw
    have h'' : (2 : ℂ) * w = 2 * (1 / 2) := by
      rw [show (2 : ℂ) * w = 1 from h]
      norm_num
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h''
  have hcomp : Tendsto (fun w : ℂ => (2 * w - 1) * completedRiemannZeta (2 * w))
      (𝓝[≠] (1 / 2)) (𝓝 1) := hres.comp h2
  have hstep := hcomp.const_mul (1 / 2 : ℂ)
  have hfun : (fun w : ℂ => (1 / 2 : ℂ) * ((2 * w - 1) * completedRiemannZeta (2 * w))) =
      (fun w : ℂ => (w - 1 / 2) * completedRiemannZeta (2 * w)) := by
    funext w
    ring
  rw [hfun] at hstep
  simpa using hstep

/-- `Λ(1/2+2it)` is integrable on `ℝ`. -/
private theorem integrable_half_line_540 :
    Integrable (fun t : ℝ =>
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) := by
  have hpi : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨K, hKpos, hK⟩ := completedZeta_half_line_decay_540 1 one_pos hpi
  have hmaj : Integrable (fun t : ℝ => K * (Real.exp (-((1:ℝ) * |t|)) * (1 + |t|) ^ 0)) :=
    (exp_abs_pow_integrable_540 1 one_pos 0).const_mul K
  refine Integrable.mono' hmaj completedZeta_half_line_continuous_540.aestronglyMeasurable ?_
  filter_upwards [] with t
  have h := hK t
  have heq : Real.exp (-((1:ℝ) * |t|)) = Real.exp (-(1 * |t|)) := rfl
  calc ‖completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖
      ≤ K * Real.exp (-(1 * |t|)) := h
    _ = K * (Real.exp (-((1:ℝ) * |t|)) * (1 + |t|) ^ 0) := by rw [pow_zero, mul_one]

/-- Leaf 2 reduced to the contour-shift identity: the shift alone closes `hardy_shifted_contour540`. -/
private theorem leaf2_of_shift_540 (α : ℝ) (hα : |α| < Real.pi / 2)
    (hshift : Complex.exp ((α : ℂ) * Complex.I / 4) * hardyUnshifted540 α =
      (∫ t : ℝ, Complex.exp ((α : ℂ) * (t : ℂ)) *
        completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) +
      (Real.pi : ℂ) * Complex.exp (-((α : ℂ) * Complex.I / 4))) :
    (Complex.exp ((α : ℂ) * Complex.I / 4) * hardyUnshifted540 α).re =
      Real.pi * Real.cos (α / 4) - 2 * expMoment540 hardyAmplitude540 0 α := by
  have hmom := two_expMoment_eq_540 α hα
  have hInt : Integrable (fun t : ℝ => Complex.exp ((α : ℂ) * (t : ℂ)) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) :=
    integrable_exp_mul_half_line_540 α hα
  have hre1 : (∫ t : ℝ, Complex.exp ((α : ℂ) * (t : ℂ)) *
        completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re =
      ∫ t : ℝ, Real.exp (α * t) *
        (completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
    rw [show (∫ t : ℝ, Complex.exp ((α : ℂ) * (t : ℂ)) *
          completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re =
        ∫ t : ℝ, (Complex.exp ((α : ℂ) * (t : ℂ)) *
          completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
        from (integral_re hInt).symm]
    apply integral_congr_ae
    filter_upwards [] with t
    have hexp : (Complex.exp ((α : ℂ) * (t : ℂ))).re = Real.exp (α * t) := by
      rw [Complex.exp_re]
      congr 1
      simp
    have him : (Complex.exp ((α : ℂ) * (t : ℂ))).im = 0 := by
      rw [Complex.exp_im]
      simp
    rw [Complex.mul_re, hexp, him, zero_mul, sub_zero]
  have hre2 : ((Real.pi : ℂ) * Complex.exp (-((α : ℂ) * Complex.I / 4))).re =
      Real.pi * Real.cos (α / 4) := by
    have him : (-((α : ℂ) * Complex.I / 4)).im = -(α / 4) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
      try ring
    have hre0 : (-((α : ℂ) * Complex.I / 4)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
      try ring
    have hexp : (Complex.exp (-((α : ℂ) * Complex.I / 4))).re = Real.cos (α / 4) := by
      rw [Complex.exp_re, hre0, him, Real.exp_zero, one_mul, Real.cos_neg]
    rw [Complex.mul_re, hexp, Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero]
  rw [hshift, Complex.add_re, hre1, hre2]
  linarith


/-! ## (E4) the pole split at `w = 1/2`, and vanishing of the horizontal segments -/

/-- `Λ(2w) = Λ₀(2w) - 1/(2w) + 1/(2w-1)`: the pole at `w = 1/2` split off. -/
private theorem completedZeta_pole_split_540 (w : ℂ) :
    completedRiemannZeta (2 * w) =
      completedRiemannZeta₀ (2 * w) - 1 / (2 * w) + 1 / (2 * w - 1) := by
  rw [completedRiemannZeta_eq,
    show (1 : ℂ) - 2 * w = -(2 * w - 1) by ring, one_div, one_div, one_div, inv_neg]
  ring

/-- Given exponential decay of `Λ(2w)` in the closed strip `1/4 ≤ Re w ≤ 1`, the horizontal
segments of the contour integral `∫_{1/4}^{1} e^{-iαw} Λ(2w) dσ` tend to zero at `±∞`. -/
private theorem horizontal_segments_540 (α c K : ℝ) (hc : |α| < c) (hK : 0 ≤ K)
    (hdec : ∀ w : ℂ, 1 / 4 ≤ w.re → w.re ≤ 1 →
      ‖completedRiemannZeta (2 * w)‖ ≤ K * Real.exp (-(c * |w.im|))) :
    Tendsto (fun T : ℝ => ∫ σ : ℝ in (1 / 4)..1,
        Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
          completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ σ : ℝ in (1 / 4)..1,
        Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
          completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))) atBot (𝓝 0) := by
  have hgap : (0:ℝ) < c - |α| := by linarith
  have hpoint : ∀ (T σ : ℝ), σ ∈ Set.uIcc (1/4) 1 →
      ‖Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
        completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
      K * Real.exp (-(c - |α|) * |T|) := by
    intro T σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1)] at hσ
    have hσ1 : (1/4:ℝ) ≤ σ := hσ.1
    have hσ2 : σ ≤ 1 := hσ.2
    have hexp : ‖Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I))‖
        = Real.exp (α * T) := by
      rw [Complex.norm_exp]
      congr 1
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.ofReal_mul]
      ring
    have hwre : ((σ : ℂ) + (T : ℂ) * Complex.I).re = σ := by simp
    have hwim : ((σ : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
    have hdir := hdec ((σ : ℂ) + (T : ℂ) * Complex.I) (by rw [hwre]; linarith)
      (by rw [hwre]; linarith)
    have hdir' : ‖completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
        K * Real.exp (-(c * |T|)) := by
      simpa [hwim] using hdir
    rw [norm_mul, hexp]
    have h2 : Real.exp (α * T) ≤ Real.exp (|α| * |T|) := by
      apply Real.exp_le_exp.mpr
      calc α * T ≤ |α * T| := le_abs_self _
        _ = |α| * |T| := abs_mul α T
    have hpos : (0:ℝ) < Real.exp (|α| * |T|) := Real.exp_pos _
    refine le_trans (mul_le_mul h2 hdir' (norm_nonneg _) hpos.le) ?_
    have hcomb : Real.exp (|α| * |T|) * Real.exp (-(c * |T|)) = Real.exp (-(c - |α|) * |T|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show Real.exp (|α| * |T|) * (K * Real.exp (-(c * |T|)))
        = K * (Real.exp (|α| * |T|) * Real.exp (-(c * |T|))) by ring, hcomb]
  have hint : ∀ T : ℝ, ‖∫ σ : ℝ in (1/4)..1,
        Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
          completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
      (K * Real.exp (-(c - |α|) * |T|)) * |1 - 1/4| :=
    fun T => intervalIntegral.norm_integral_le_of_norm_le_const
      (C := K * Real.exp (-(c - |α|) * |T|)) (fun σ hσ => hpoint T σ (Set.uIoc_subset_uIcc hσ))
  have hconst : (0:ℝ) ≤ |1 - 1/4| := abs_nonneg _
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (f := fun T : ℝ => ‖∫ σ : ℝ in (1/4)..1,
        Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
          completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖)
      (g := fun T : ℝ => K * (Real.exp (-(c - |α|) * T) * |1 - 1/4|)) ?_ ?_ ?_
    · exact Eventually.of_forall fun T => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
      have h := hint T
      rw [abs_of_nonneg hT] at h
      calc ‖∫ σ : ℝ in (1/4)..1,
            Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
              completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖
          ≤ (K * Real.exp (-(c - |α|) * T)) * |1 - 1/4| := h
        _ = K * (Real.exp (-(c - |α|) * T) * |1 - 1/4|) := by ring
    · have h1 : Tendsto (fun T : ℝ => Real.exp (-(c - |α|) * T)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by linarith : -(c - |α|) < 0))
      have h2 : Tendsto (fun T : ℝ => K * (Real.exp (-(c - |α|) * T) * |1 - 1/4|))
          atTop (𝓝 (K * (0 * |1 - 1/4|))) :=
        tendsto_const_nhds.mul (h1.mul tendsto_const_nhds)
      simpa using h2
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (f := fun T : ℝ => ‖∫ σ : ℝ in (1/4)..1,
        Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
          completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖)
      (g := fun T : ℝ => K * (Real.exp ((c - |α|) * T) * |1 - 1/4|)) ?_ ?_ ?_
    · exact Eventually.of_forall fun T => norm_nonneg _
    · filter_upwards [eventually_le_atBot (0:ℝ)] with T hT
      have h := hint T
      rw [abs_of_nonpos hT] at h
      calc ‖∫ σ : ℝ in (1/4)..1,
            Complex.exp (-(α : ℂ) * Complex.I * ((σ : ℂ) + (T : ℂ) * Complex.I)) *
              completedRiemannZeta (2 * ((σ : ℂ) + (T : ℂ) * Complex.I))‖
          ≤ (K * Real.exp (-(c - |α|) * (-T))) * |1 - 1/4| := h
        _ = K * (Real.exp ((c - |α|) * T) * |1 - 1/4|) := by ring
    · have h1 : Tendsto (fun T : ℝ => Real.exp ((c - |α|) * T)) atBot (𝓝 0) := by
        have h2 : Tendsto (fun T : ℝ => (c - |α|) * T) atBot atBot :=
          (tendsto_const_mul_atBot_of_pos hgap).mpr tendsto_id
        have h3 := Real.tendsto_exp_atBot.comp h2
        simpa only [Function.comp_def] using h3
      have h2 : Tendsto (fun T : ℝ => K * (Real.exp ((c - |α|) * T) * |1 - 1/4|))
          atBot (𝓝 (K * (0 * |1 - 1/4|))) :=
        tendsto_const_nhds.mul (h1.mul tendsto_const_nhds)
      simpa using h2

/-! ## (G1) vertical-strip bounds for `Γ`, from the Beta integral -/

private theorem gamma_prod_eq_540 (σ T : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I) * Complex.Gamma (((1 - σ : ℝ)) : ℂ) =
      Complex.Gamma (1 + (T : ℂ) * Complex.I) *
        Complex.betaIntegral ((σ : ℂ) + (T : ℂ) * Complex.I) (((1 - σ : ℝ)) : ℂ) := by
  have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (σ : ℂ) + (T : ℂ) * Complex.I)
    (t := (((1 - σ : ℝ)) : ℂ)) (by simpa using h0) (by simpa using (by linarith : (0:ℝ) < 1 - σ))
  have hsum : (σ : ℂ) + (T : ℂ) * Complex.I + (((1 - σ : ℝ)) : ℂ) = 1 + (T : ℂ) * Complex.I := by
    push_cast; ring
  rwa [hsum] at hb

private theorem betaIntegral_norm_le_540 (σ T : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    ‖Complex.betaIntegral ((σ : ℂ) + (T : ℂ) * Complex.I) (((1 - σ : ℝ)) : ℂ)‖ ≤
      Real.Gamma σ * Real.Gamma (1 - σ) := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs
  have h1σ : (0:ℝ) < 1 - σ := by linarith
  -- step 1: triangle inequality
  have hstep : ‖Complex.betaIntegral s (((1 - σ : ℝ)) : ℂ)‖ ≤
      ∫ x : ℝ in (0:ℝ)..1,
        ‖(x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((((1 - σ : ℝ)) : ℂ) - 1)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num)
  -- step 2: pointwise identification of the modulus integrand on (0,1]
  have hpt : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      ‖(x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((((1 - σ : ℝ)) : ℂ) - 1)‖ =
        x ^ (σ - 1) * (1 - x) ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h
      have hz : (1 : ℂ) - ((1:ℝ) : ℂ) = 0 := by norm_num
      rw [hz, zero_cpow (by
        intro hc
        have hc' := congrArg Complex.re hc
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hc'
        linarith)]
      simp [Real.zero_rpow (show (-σ : ℝ) ≠ 0 by linarith), sub_self]
    · have hx1 : 0 < 1 - x := by linarith
      have hcast : (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) := by push_cast; ring
      rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        Complex.norm_cpow_eq_rpow_re_of_pos hx1]
      have h3 : (s - 1).re = σ - 1 := by simp [hs]
      have h4 : (((((1 - σ : ℝ)) : ℂ) - 1)).re = -σ := by simp
      rw [h3, h4]
  have hstep2 : ∫ x : ℝ in (0:ℝ)..1,
        ‖(x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((((1 - σ : ℝ)) : ℂ) - 1)‖ =
      ∫ x : ℝ in (0:ℝ)..1, x ^ (σ - 1) * (1 - x) ^ (-σ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    exact hpt x (by rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx)
  -- step 3: the real integral is the complex Beta integral at real arguments
  have hreal : Complex.betaIntegral (σ : ℂ) (((1 - σ : ℝ)) : ℂ) =
      ((∫ x : ℝ in (0:ℝ)..1, x ^ (σ - 1) * (1 - x) ^ (-σ) : ℝ) : ℂ) := by
    rw [show Complex.betaIntegral (σ : ℂ) (((1 - σ : ℝ)) : ℂ) =
      ∫ x : ℝ in (0:ℝ)..1,
        ((x : ℂ) ^ ((σ : ℂ) - 1) * (1 - (x : ℂ)) ^ ((((1 - σ : ℝ)) : ℂ) - 1)) from rfl]
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h
      have hz : (1 : ℂ) - ((1:ℝ) : ℂ) = 0 := by norm_num
      rw [hz, zero_cpow (by
        intro hc
        have hc' := congrArg Complex.re hc
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hc'
        linarith)]
      simp [Real.zero_rpow (show (-σ : ℝ) ≠ 0 by linarith), sub_self]
    · have hx1 : 0 < 1 - x := by linarith
      have hcast : (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) := by push_cast; ring
      have e1 : ((x : ℂ) ^ ((σ : ℂ) - 1)) = ((x ^ (σ - 1) : ℝ) : ℂ) := by
        rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow hx0.le (σ - 1)]
      have e2 : ((1 : ℂ) - (x : ℂ)) ^ ((((1 - σ : ℝ)) : ℂ) - 1) =
          (((1 - x) ^ (-σ) : ℝ) : ℂ) := by
        rw [hcast,
          show ((((1 - σ : ℝ)) : ℂ) - 1) = ((-σ : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow hx1.le (-σ)]
      rw [e1, e2, ← Complex.ofReal_mul]
  -- step 4: Gamma value of the real Beta integral
  have hkey : (∫ x : ℝ in (0:ℝ)..1, x ^ (σ - 1) * (1 - x) ^ (-σ)) =
      Real.Gamma σ * Real.Gamma (1 - σ) := by
    have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (σ : ℂ)) (t := (((1 - σ : ℝ)) : ℂ))
      (by simpa using h0) (by simpa using h1σ)
    have hsum : (σ : ℂ) + (((1 - σ : ℝ)) : ℂ) = 1 := by push_cast; ring
    rw [hsum, hreal, Complex.Gamma_one, one_mul] at hb
    have hre := congrArg Complex.re hb
    simp only [Complex.mul_re, Complex.Gamma_ofReal, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hre
    linarith [hre]
  rw [hstep2, hkey] at hstep
  exact hstep

private theorem gamma_strip_bound_540 (σ T : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      Real.Gamma σ * (8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := by
  have h1σ : (0:ℝ) < 1 - σ := by linarith
  have hg : (0:ℝ) < Real.Gamma (1 - σ) := Real.Gamma_pos_of_pos h1σ
  have hprod := gamma_prod_eq_540 σ T h0 h1
  have hnorm : ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I)‖ * Real.Gamma (1 - σ) =
      ‖Complex.Gamma (1 + (T : ℂ) * Complex.I)‖ *
        ‖Complex.betaIntegral ((σ : ℂ) + (T : ℂ) * Complex.I) (((1 - σ : ℝ)) : ℂ)‖ := by
    have h' := congrArg norm hprod
    rw [norm_mul, norm_mul, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hg] at h'
    exact h'
  have hb := betaIntegral_norm_le_540 σ T h0 h1
  have hG := gamma_norm_bound_540 T
  have hBb : (0:ℝ) ≤ ‖Complex.betaIntegral ((σ : ℂ) + (T : ℂ) * Complex.I) (((1 - σ : ℝ)) : ℂ)‖ :=
    norm_nonneg _
  have hA : (0:ℝ) ≤ 8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|) := by positivity
  have hstep : ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I)‖ * Real.Gamma (1 - σ) ≤
      (8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) * (Real.Gamma σ * Real.Gamma (1 - σ)) := by
    rw [hnorm]
    exact mul_le_mul hG hb hBb hA
  have hstep' : ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I)‖ * Real.Gamma (1 - σ) ≤
      8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|) * Real.Gamma σ * Real.Gamma (1 - σ) := by
    rw [show (8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) *
        (Real.Gamma σ * Real.Gamma (1 - σ)) =
        8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|) * Real.Gamma σ * Real.Gamma (1 - σ)
        by ring] at hstep
    exact hstep
  have hfin : ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|) * Real.Gamma σ :=
    (mul_le_mul_iff_of_pos_right hg).mp hstep'
  calc ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ 8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|) * Real.Gamma σ := hfin
    _ = Real.Gamma σ * (8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := by ring

/-- `Γ(-1/4+iT) = Γ(3/4+iT)/(-1/4+iT)`. -/
private theorem gamma_neg_quarter_recur_540 (T : ℝ) :
    Complex.Gamma (((-(1/4) : ℝ)) + (T : ℂ) * Complex.I) =
      Complex.Gamma (((3/4 : ℝ)) + (T : ℂ) * Complex.I) /
        ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I) := by
  have hs : ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at h'
    norm_num at h'
  have h := Complex.Gamma_add_one ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I) hs
  rw [show ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I) + 1
      = (((3/4 : ℝ)) : ℂ) + (T : ℂ) * Complex.I by push_cast; ring] at h
  rw [h, eq_div_iff hs]
  ring

/-- `‖Γ(-1/4+iT)‖` decays like `(1+|T|) e^{-π|T|/2}`. -/
private theorem gamma_neg_quarter_bound_540 (T : ℝ) :
    ‖Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      32 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := by
  have hnum := gamma_strip_bound_540 (3/4) T (by norm_num) (by norm_num)
  have hden : (1/4 : ℝ) ≤ ‖(((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I‖ := by
    have h1 : ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I).re = -(1/4) := by simp
    calc (1/4 : ℝ) = |(-(1/4) : ℝ)| := by
          rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
      _ = |((((- (1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I).re| := by rw [h1]
      _ ≤ ‖(((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _
  have hpos : (0:ℝ) < ‖(((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I‖ := by linarith
  rw [gamma_neg_quarter_recur_540 T, norm_div]
  refine (div_le_iff₀ hpos).mpr ?_
  have h1 : ‖Complex.Gamma (((3/4 : ℝ)) + (T : ℂ) * Complex.I)‖ ≤
      Real.Gamma (3/4) * (8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := hnum
  have h2 : (32 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|))) *
      (1/4 : ℝ) = 8 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := by
    ring
  have h3 : ‖Complex.Gamma (((3/4 : ℝ)) + (T : ℂ) * Complex.I)‖ ≤
      (32 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|))) * (1/4 : ℝ) := by
    rw [h2]
    calc ‖Complex.Gamma (((3/4 : ℝ)) + (T : ℂ) * Complex.I)‖
        ≤ Real.Gamma (3/4) * (8 * (1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := h1
      _ = 8 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|)) := by ring
  calc ‖Complex.Gamma (((3/4 : ℝ)) + (T : ℂ) * Complex.I)‖
      ≤ (32 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|))) * (1/4 : ℝ) := h3
    _ ≤ (32 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|))) *
        ‖(((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I‖ := by
        apply mul_le_mul_of_nonneg_left hden
        positivity

private theorem integrable_gamma_neg_quarter_540 :
    Integrable (fun T : ℝ => Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I)) := by
  have hbase := exp_abs_pow_integrable_540 (Real.pi / 2) (by positivity) 1
  have hC : (0:ℝ) ≤ 32 * Real.Gamma (3/4) := by positivity
  refine Integrable.mono' (hbase.const_mul (32 * Real.Gamma (3/4))) ?_ ?_
  · have hcont : Continuous fun T : ℝ => Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (T : ℂ) * Complex.I) := by
      rw [continuous_iff_continuousAt]
      intro T
      refine ContinuousAt.comp ?_ (by fun_prop)
      apply Complex.continuousAt_Gamma
      intro m hm
      have h' := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.natCast_re, Complex.natCast_im] at h'
      have hm1 : (m : ℝ) = 1/4 := by linarith
      have h4 : ((4 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
      have h5 : 4 * m = 1 := by exact_mod_cast h4
      omega
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with T
    have h := gamma_neg_quarter_bound_540 T
    have h1 : 32 * Real.Gamma (3/4) * ((1 + |T|) * Real.exp (-(Real.pi / 2) * |T|))
        = 32 * Real.Gamma (3/4) * (Real.exp (-((Real.pi / 2) * |T|)) * (1 + |T|) ^ 1) := by
      rw [pow_one,
        show -(Real.pi / 2) * |T| = -((Real.pi / 2) * |T|) by ring]
      ring
    rw [h1] at h
    exact h

/-! ## (G3) the inverse Mellin transform of `Γ` on a line `Re s = c > 0` -/

private theorem mellin_exp_neg_eq_gamma_540 (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Complex.Gamma s := by
  rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral hs]

private theorem integrable_gamma_vertical_540 (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    Integrable (fun y : ℝ => Complex.Gamma ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hbase := exp_abs_pow_integrable_540 (Real.pi / 2) (by positivity) 1
  have hC : (0:ℝ) ≤ 8 * Real.Gamma σ := by positivity
  refine Integrable.mono' (hbase.const_mul (8 * Real.Gamma σ)) ?_ ?_
  · have hcont : Continuous fun y : ℝ => Complex.Gamma ((σ : ℂ) + (y : ℂ) * Complex.I) := by
      rw [continuous_iff_continuousAt]
      intro y
      refine ContinuousAt.comp ?_ (by fun_prop)
      apply Complex.continuousAt_Gamma
      intro m hm
      have h' := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.neg_re, Complex.neg_im, zero_mul,
        add_zero] at h'
      have hm1 : (m : ℝ) = 1/4 := by linarith
      have h4 : ((4 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
      have h5 : 4 * m = 1 := by exact_mod_cast h4
      omega
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with y
    have h := gamma_strip_bound_540 σ y h0 h1
    have heq : Real.Gamma σ * (8 * (1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)) =
        8 * Real.Gamma σ * (Real.exp (-((Real.pi / 2) * |y|)) * (1 + |y|) ^ 1) := by
      rw [pow_one,
        show -(Real.pi / 2) * |y| = -((Real.pi / 2) * |y|) by ring]
      ring
    rw [heq] at h
    exact h

private theorem verticalIntegrable_mellin_exp_neg_540 :
    Complex.VerticalIntegrable (mellin fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) (3 / 4) := by
  have hfun : (fun y : ℝ => mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) ((3 / 4 : ℝ) + y * Complex.I))
      = fun y : ℝ => Complex.Gamma (((3 / 4 : ℝ)) + y * Complex.I) := by
    funext y
    exact mellin_exp_neg_eq_gamma_540 _ (by simp)
  show Integrable (fun y : ℝ =>
    mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) ((3 / 4 : ℝ) + y * Complex.I))
  rw [hfun]
  exact integrable_gamma_vertical_540 (3 / 4) (by norm_num) (by norm_num)

/-- `(1/2π) ∫_ℝ x^{-(c+iy)} Γ(c+iy) dy = e^{-x}` for `0 < c < 1`. -/
private theorem mellinInv_gamma_pos_540 (x : ℝ) (hx : 0 < x) :
    mellinInv (3 / 4) Complex.Gamma x = ((Real.exp (-x) : ℝ) : ℂ) := by
  have hf : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) ((3 / 4 : ℝ) : ℂ) := by
    have h := Complex.GammaIntegral_convergent (s := ((3 / 4 : ℝ) : ℂ)) (by norm_num)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul]
    rw [mul_comm]
  have hV : Complex.VerticalIntegrable (mellin fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) (3 / 4) :=
    verticalIntegrable_mellin_exp_neg_540
  have hcont : ContinuousAt (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) x := by fun_prop
  have hm := mellinInv_mellin_eq (3 / 4) (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) hx hf hV hcont
  have hcongr : mellinInv (3 / 4) (mellin fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) x
      = mellinInv (3 / 4) Complex.Gamma x := by
    simp only [mellinInv]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    rw [mellin_exp_neg_eq_gamma_540 _ (by simp)]
  rw [← hcongr, hm]


/-! ## (G4) the inverse Mellin transform of `Γ` on the shifted line `Re s = -1/4` -/

private theorem mellinInv_neg_quarter_asIntegral_540 (z : ℝ) :
    mellinInv (-(1 / 4)) Complex.Gamma z =
      (1 / (2 * Real.pi)) • ∫ y : ℝ, (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I) := by
  simp only [mellinInv]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul]
  rw [show -((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) =
      (((1 / 4 : ℝ)) : ℂ) - (y : ℂ) * Complex.I by push_cast; ring]

private theorem continuous_mellinInv_integrand_540 (z : ℝ) (hz : 0 < z) :
    Continuous fun y : ℝ => (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
      Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I) := by
  have hzne : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  rw [continuous_iff_continuousAt]
  intro y
  have h1 : ContinuousAt (fun y : ℝ => (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I)) y :=
    (continuousAt_const_cpow hzne).comp (by fun_prop)
  have h2 : ContinuousAt (fun y : ℝ =>
      Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I)) y := by
    refine ContinuousAt.comp ?_ (by fun_prop)
    refine Complex.continuousAt_Gamma _ (by
      intro m hm
      have h' := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.neg_re, zero_mul, add_zero] at h'
      have hm1 : (m : ℝ) = 1/4 := by linarith
      have h4 : ((4 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
      have h5 : 4 * m = 1 := by exact_mod_cast h4
      omega)
  exact h1.mul h2

private theorem hasDerivAt_mellinInv_gamma_neg_aux_540 (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => (1 / (2 * Real.pi)) • ∫ y : ℝ,
        (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
          Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I))
      (-(((Real.exp (-x) : ℝ)) : ℂ)) x := by
  have hx2 : (0:ℝ) < x / 2 := by linarith
  have hx3 : (0:ℝ) < 3 * x / 2 := by linarith
  set A : ℝ := 32 * Real.Gamma (3/4) with hA
  set S : ℝ := (x / 2) ^ (-(3/4) : ℝ) + (3 * x / 2) ^ ((1/4) : ℝ) + 1 with hS
  set C : ℝ := A * S with hC
  have hApos : 0 < A := by rw [hA]; positivity
  have hPC : (0:ℝ) < (x / 2) ^ (-(3/4) : ℝ) := Real.rpow_pos_of_pos hx2 _
  have hTC : (0:ℝ) < (3 * x / 2) ^ ((1/4) : ℝ) := Real.rpow_pos_of_pos hx3 _
  have hSpos : 0 < S := by rw [hS]; linarith
  have hCpos : 0 < C := by rw [hC]; positivity
  set bd : ℝ → ℝ := fun y : ℝ => C * (Real.exp (-(Real.pi / 2) * |y|) * (1 + |y|) ^ 2) with hbd
  have hbd_int : Integrable bd := by
    rw [hbd]
    have h0 : Integrable (fun y : ℝ => Real.exp (-((Real.pi / 2) * |y|)) * (1 + |y|) ^ 2) :=
      exp_abs_pow_integrable_540 (Real.pi / 2) (by positivity) 2
    refine (h0.const_mul C).congr ?_
    filter_upwards [] with y
    rw [show -(Real.pi / 2) * |y| = -((Real.pi / 2) * |y|) by ring]
  have hmem : ∀ z ∈ Metric.ball x (x / 2), x / 2 < z ∧ z < 3 * x / 2 := by
    intro z hz
    have hz1 : |z - x| < x / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hz
    rw [abs_lt] at hz1
    constructor <;> linarith [hz1.1, hz1.2]
  have hTS : (3 * x / 2) ^ ((1/4) : ℝ) ≤ S := by rw [hS]; linarith
  have hPS : (x / 2) ^ (-(3/4) : ℝ) ≤ S := by rw [hS]; linarith
  -- bound for the integrand itself
  have hbdF : ∀ y : ℝ, ∀ z ∈ Metric.ball x (x / 2),
      ‖(z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I)‖ ≤ bd y := by
    intro y z hz
    obtain ⟨hz1, hz2⟩ := hmem z hz
    have hzpos : 0 < z := by linarith
    have hnorm : ‖(z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I)‖
        = z ^ ((1/4) : ℝ) * ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hzpos]
      congr 1
      simp
    rw [hnorm]
    have hG := gamma_neg_quarter_bound_540 y
    have hG' : ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        A * ((1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)) := by
      rw [hA]; exact hG
    have hz4 : z ^ ((1/4) : ℝ) ≤ (3 * x / 2) ^ ((1/4) : ℝ) :=
      Real.rpow_le_rpow hzpos.le hz2.le (by norm_num)
    have hG0 : (0:ℝ) ≤ ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ :=
      norm_nonneg _
    have hstep : z ^ ((1/4) : ℝ) *
          ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        (3 * x / 2) ^ ((1/4) : ℝ) * (A * ((1 + |y|) * Real.exp (-(Real.pi / 2) * |y|))) :=
      mul_le_mul hz4 hG' hG0 hTC.le
    have h1y : (0:ℝ) < 1 + |y| := by positivity
    have h1yle : (1 + |y|) ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y]
    have he : (0:ℝ) < Real.exp (-(Real.pi / 2) * |y|) := Real.exp_pos _
    have hstep2 : (3 * x / 2) ^ ((1/4) : ℝ) * (A * ((1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)))
        ≤ S * (A * ((1 + |y|) ^ 2 * Real.exp (-(Real.pi / 2) * |y|))) := by
      have h1 : (3 * x / 2) ^ ((1/4) : ℝ) * (1 + |y|) ≤ S * (1 + |y|) ^ 2 :=
        mul_le_mul hTS h1yle (by positivity) hSpos.le
      have h2 : A * Real.exp (-(Real.pi / 2) * |y|) * ((3 * x / 2) ^ ((1/4) : ℝ) * (1 + |y|))
          ≤ A * Real.exp (-(Real.pi / 2) * |y|) * (S * (1 + |y|) ^ 2) := by
        apply mul_le_mul_of_nonneg_left h1
        positivity
      calc (3 * x / 2) ^ ((1/4) : ℝ) * (A * ((1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)))
          = A * Real.exp (-(Real.pi / 2) * |y|) * ((3 * x / 2) ^ ((1/4) : ℝ) * (1 + |y|)) := by
            ring
        _ ≤ A * Real.exp (-(Real.pi / 2) * |y|) * (S * (1 + |y|) ^ 2) := h2
        _ = S * (A * ((1 + |y|) ^ 2 * Real.exp (-(Real.pi / 2) * |y|))) := by ring
    refine hstep.trans (hstep2.trans_eq ?_)
    rw [hbd, hC]
    ring
  -- bound for the derivative integrand
  have hbdF' : ∀ y : ℝ, ∀ z ∈ Metric.ball x (x / 2),
      ‖-(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
        (z : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)))‖ ≤ bd y := by
    intro y z hz
    obtain ⟨hz1, hz2⟩ := hmem z hz
    have hzpos : 0 < z := by linarith
    have hnorm : ‖-(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
        (z : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)))‖
        = ‖Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)‖ * z ^ (-(3/4) : ℝ) := by
      rw [norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hzpos]
      congr 1
      simp
    rw [hnorm]
    have hG := gamma_strip_bound_540 (3/4) y (by norm_num) (by norm_num)
    have hG0 : (0:ℝ) ≤ ‖Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)‖ := norm_nonneg _
    have hz4 : z ^ (-(3/4) : ℝ) ≤ (x / 2) ^ (-(3/4) : ℝ) := by
      have h1 : (x / 2) ^ ((3/4) : ℝ) ≤ z ^ ((3/4) : ℝ) :=
        Real.rpow_le_rpow hx2.le hz1.le (by norm_num)
      have h2 : z ^ (-(3/4) : ℝ) = (z ^ ((3/4) : ℝ))⁻¹ := by
        rw [← Real.rpow_neg hzpos.le]
      have h3 : (x / 2) ^ (-(3/4) : ℝ) = ((x / 2) ^ ((3/4) : ℝ))⁻¹ := by
        rw [← Real.rpow_neg hx2.le]
      rw [h2, h3]
      exact ((inv_le_inv₀ (Real.rpow_pos_of_pos hzpos _)
        (Real.rpow_pos_of_pos hx2 _)).mpr h1)
    have hz40 : (0:ℝ) ≤ z ^ (-(3/4) : ℝ) := Real.rpow_nonneg hzpos.le _
    have hstep : ‖Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)‖ * z ^ (-(3/4) : ℝ) ≤
        (Real.Gamma (3/4) * (8 * (1 + |y|) * Real.exp (-(Real.pi / 2) * |y|))) *
          (x / 2) ^ (-(3/4) : ℝ) :=
      mul_le_mul hG hz4 hz40 (by positivity)
    have hΓ4 : Real.Gamma (3/4) * 8 ≤ A := by rw [hA]; nlinarith [Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)]
    have hΓ40 : (0:ℝ) ≤ Real.Gamma (3/4) * 8 := by positivity
    have h1y : (0:ℝ) < 1 + |y| := by positivity
    have h1yle : (1 + |y|) ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y]
    have he : (0:ℝ) < Real.exp (-(Real.pi / 2) * |y|) := Real.exp_pos _
    have hstep2 : (Real.Gamma (3/4) * (8 * (1 + |y|) * Real.exp (-(Real.pi / 2) * |y|))) *
          (x / 2) ^ (-(3/4) : ℝ)
        ≤ C * (Real.exp (-(Real.pi / 2) * |y|) * (1 + |y|) ^ 2) := by
      rw [hC]
      have h1 : Real.Gamma (3/4) * 8 * (x / 2) ^ (-(3/4) : ℝ) ≤ A * S := by
        have : A * S = A * (x / 2) ^ (-(3/4) : ℝ) + A * ((3 * x / 2) ^ ((1/4) : ℝ)) + A * 1 := by
          rw [hS]; ring
        rw [this]
        have h1' : Real.Gamma (3/4) * 8 * (x / 2) ^ (-(3/4) : ℝ) ≤ A * (x / 2) ^ (-(3/4) : ℝ) := by
          apply mul_le_mul_of_nonneg_right hΓ4 hPC.le
        have h2' : (0:ℝ) ≤ A * ((3 * x / 2) ^ ((1/4) : ℝ)) := by positivity
        have h3' : (0:ℝ) ≤ A := hApos.le
        nlinarith [h1', h2', h3']
      calc Real.Gamma (3/4) * (8 * (1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)) * (x / 2) ^ (-(3/4) : ℝ)
          = (Real.Gamma (3/4) * 8 * (x / 2) ^ (-(3/4) : ℝ)) *
              ((1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)) := by ring
        _ ≤ (A * S) * ((1 + |y|) * Real.exp (-(Real.pi / 2) * |y|)) := by
            apply mul_le_mul_of_nonneg_right h1
            positivity
        _ ≤ (A * S) * ((1 + |y|) ^ 2 * Real.exp (-(Real.pi / 2) * |y|)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right h1yle he.le
        _ = A * S * (Real.exp (-(Real.pi / 2) * |y|) * (1 + |y|) ^ 2) := by ring
    exact hstep.trans hstep2
  -- differentiability in the parameter
  have hdiff : ∀ᵐ y : ℝ, ∀ z ∈ Metric.ball x (x / 2),
      HasDerivAt (fun z : ℝ => (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I))
        (-(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
          (z : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)))) z := by
    refine Filter.Eventually.of_forall fun y z hz => ?_
    obtain ⟨hz1, hz2⟩ := hmem z hz
    have hzpos : 0 < z := by linarith
    have hr : ((((1 / 4 : ℝ)) : ℂ) - (y : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
    have hder := hasDerivAt_ofReal_cpow_const (x := z) hzpos.ne'
      (r := (((1 / 4 : ℝ)) : ℂ) - (y : ℂ) * Complex.I) hr
    have hmul := hder.mul_const (Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I))
    have hd : ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, zero_mul, add_zero] at h'
      norm_num at h'
    have hrec := Complex.Gamma_add_one ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) hd
    rw [show ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) + 1
      = (((3 / 4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I by push_cast; ring] at hrec
    refine hmul.congr_deriv ?_
    rw [hrec]
    rw [show ((((1 / 4 : ℝ)) : ℂ) - (y : ℂ) * Complex.I) - 1
      = -((((3 / 4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I) by push_cast; ring]
    rw [show ((((1 / 4 : ℝ)) : ℂ) - (y : ℂ) * Complex.I)
      = -((((- (1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) by push_cast; ring]
    ring
  -- apply the parametric integral lemma
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ))
    (bound := bd)
    (s := Metric.ball x (x / 2))
    (F := fun z : ℝ => fun y : ℝ => (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
      Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I))
    (F' := fun z : ℝ => fun y : ℝ => -(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
      (z : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I))))
    (Metric.ball_mem_nhds x hx2)
    (by
      filter_upwards [Metric.ball_mem_nhds x hx2] with z hz
      obtain ⟨hz1, hz2⟩ := hmem z hz
      exact (continuous_mellinInv_integrand_540 z (by linarith)).aestronglyMeasurable)
    (by
      refine Integrable.mono' hbd_int
        (continuous_mellinInv_integrand_540 x hx).aestronglyMeasurable ?_
      filter_upwards [] with y
      exact hbdF y x (Metric.mem_ball_self hx2))
    (by
      have hc : Continuous fun y : ℝ => -(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
          (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I))) := by
        have hzne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
        rw [continuous_iff_continuousAt]
        intro y
        have h1 : ContinuousAt (fun y : ℝ =>
            (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I))) y :=
          (continuousAt_const_cpow hzne).comp (by fun_prop)
        have h2 : ContinuousAt (fun y : ℝ =>
            Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)) y := by
          refine ContinuousAt.comp ?_ (by fun_prop)
          exact Complex.continuousAt_Gamma _ (by
            intro m hm
            have h' := congrArg Complex.re hm
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.neg_re, zero_mul,
              add_zero] at h'
            have hm1 : (m : ℝ) = 1/4 := by linarith
            have h4 : ((4 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
            have h5 : 4 * m = 1 := by exact_mod_cast h4
            omega)
        exact (h2.mul h1).neg
      exact hc.aestronglyMeasurable)
    (Filter.Eventually.of_forall hbdF')
    hbd_int hdiff).2
  -- the value of the derivative integral
  have hIntneg : (∫ y : ℝ, -(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
      (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I))))
      = -(∫ y : ℝ, Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
        (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I))) := integral_neg _
  have h2 : (1 / (2 * Real.pi)) • (∫ y : ℝ, -(Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
      (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I))))
      = -(((Real.exp (-x) : ℝ)) : ℂ) := by
    have h1 : mellinInv (3 / 4) Complex.Gamma x = (1 / (2 * Real.pi)) • ∫ y : ℝ,
        (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
          Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) := rfl
    have hcongr : (∫ y : ℝ, Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) *
        (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)))
        = ∫ y : ℝ, (x : ℂ) ^ (-(((3 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
          Complex.Gamma (((3 / 4 : ℝ)) + (y : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [smul_eq_mul, mul_comm]
    rw [hIntneg, smul_neg, hcongr, ← h1, mellinInv_gamma_pos_540 x hx]
  have hfin : HasDerivAt (fun z : ℝ => (1 / (2 * Real.pi)) • ∫ y : ℝ,
      (z : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I))
      (-(((Real.exp (-x) : ℝ)) : ℂ)) x := by
    have hcs := hmain.const_smul (1 / (2 * Real.pi))
    rwa [h2] at hcs
  exact hfin

private theorem hasDerivAt_mellinInv_gamma_neg_540 (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => mellinInv (-(1 / 4)) Complex.Gamma z)
      (-(((Real.exp (-x) : ℝ)) : ℂ)) x := by
  have h := hasDerivAt_mellinInv_gamma_neg_aux_540 x hx
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [] with z
  exact mellinInv_neg_quarter_asIntegral_540 z

private theorem mellinInv_gamma_neg_540 (x : ℝ) (hx : 0 < x) :
    mellinInv (-(1 / 4)) Complex.Gamma x = ((Real.exp (-x) - 1 : ℝ) : ℂ) := by
  set Gw : ℝ → ℂ := fun z => mellinInv (-(1 / 4)) Complex.Gamma z - ((Real.exp (-z) : ℝ) : ℂ) with hGw
  have hGderiv : ∀ t : ℝ, 0 < t → HasDerivAt Gw 0 t := by
    intro t ht
    have h1 := hasDerivAt_mellinInv_gamma_neg_540 t ht
    have h3 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-(Real.exp (-t))) t := by
      simpa only [Function.comp_def, mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have h2 : HasDerivAt (fun z : ℝ => ((Real.exp (-z) : ℝ) : ℂ)) (((-(Real.exp (-t))) : ℝ) : ℂ) t :=
      h3.ofReal_comp
    have h4 := h1.sub h2
    have hzero : -(((Real.exp (-t) : ℝ)) : ℂ) - (((-(Real.exp (-t))) : ℝ) : ℂ) = 0 := by
      push_cast; ring
    rw [hzero] at h4
    exact h4
  have hconst : ∀ a : ℝ, 0 < a → a ≤ x → Gw x = Gw a := by
    intro a ha hax
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := Gw) (f' := fun _ => (0:ℂ))
      (fun t ht => hGderiv t (by
        rw [Set.uIcc_of_le hax] at ht
        exact lt_of_lt_of_le ha ht.1)) intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h
    exact sub_eq_zero.mp h.symm
  -- norm bound near 0
  set Cw : ℝ := (1 / (2 * Real.pi)) * (∫ y : ℝ,
    ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖) with hCw
  have hCw0 : (0:ℝ) ≤ Cw := by
    rw [hCw]
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun y => norm_nonneg _)
  have hFa : ∀ a : ℝ, 0 < a → ‖mellinInv (-(1 / 4)) Complex.Gamma a‖ ≤ Cw * a ^ ((1/4) : ℝ) := by
    intro a ha
    rw [mellinInv_neg_quarter_asIntegral_540 a]
    have hnorm : ∀ y : ℝ, ‖(a : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I)‖
        = a ^ ((1/4) : ℝ) * ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ := by
      intro y
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
      congr 1
      simp
    have h2 : ‖(1 / (2 * Real.pi)) • ∫ y : ℝ, (a : ℂ) ^ (((1 / 4 : ℝ)) - (y : ℂ) * Complex.I) *
        Complex.Gamma (((-(1 / 4) : ℝ)) + (y : ℂ) * Complex.I)‖ ≤
        (1 / (2 * Real.pi)) * ∫ y : ℝ, a ^ ((1/4) : ℝ) *
          ‖Complex.Gamma ((((-(1 / 4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      exact integral_congr_ae (Filter.Eventually.of_forall hnorm)
    refine h2.trans_eq ?_
    rw [integral_const_mul, hCw]
    ring
  have hF0 : Tendsto (fun a : ℝ => mellinInv (-(1 / 4)) Complex.Gamma a) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun a : ℝ => Cw * a ^ ((1/4) : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun a : ℝ => a ^ ((1/4) : ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
        have := (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/4)).tendsto (0:ℝ)
        simpa [Real.zero_rpow (by norm_num : (1/4 : ℝ) ≠ 0)] using this
      simpa using (h1.const_mul Cw).mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact hFa a ha
  have hexp0 : Tendsto (fun a : ℝ => ((Real.exp (-a) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((1:ℝ) : ℂ)) := by
    have h0 : ContinuousAt (fun a : ℝ => Real.exp (-a)) 0 :=
      Real.continuous_exp.continuousAt.comp (by fun_prop)
    have h1 : Tendsto (fun a : ℝ => Real.exp (-a)) (𝓝 (0:ℝ)) (𝓝 1) := by
      simpa using h0.tendsto
    exact (Complex.continuous_ofReal.tendsto _).comp (h1.mono_left nhdsWithin_le_nhds)
  have hGw0 : Tendsto Gw (𝓝[>] 0) (𝓝 (-1)) := by
    have h1 : Tendsto (fun a : ℝ => mellinInv (-(1 / 4)) Complex.Gamma a - ((Real.exp (-a) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (0 - ((1:ℝ) : ℂ))) := hF0.sub hexp0
    have h2 : (0 : ℂ) - ((1:ℝ) : ℂ) = -1 := by norm_num
    rw [h2] at h1
    exact h1
  have hev : ∀ᶠ a : ℝ in 𝓝[>] 0, Gw a = Gw x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with a ha hax
    exact (hconst a ha hax.le).symm
  have h2 : Tendsto Gw (𝓝[>] 0) (𝓝 (Gw x)) := tendsto_const_nhds.congr' (hev.mono fun a h => h.symm)
  have hx1 : Gw x = -1 := tendsto_nhds_unique h2 hGw0
  have hfin : mellinInv (-(1 / 4)) Complex.Gamma x = ((Real.exp (-x) : ℝ) : ℂ) - 1 := by
    have h' := hx1
    rw [hGw] at h'
    have h2 := sub_eq_iff_eq_add.mp h'
    rw [h2]
    ring
  rw [hfin]
  push_cast
  ring

/-! ## (M1) the subtracted theta function `g(x) = θ(ix) - 1 - x^{-(1 / 2)} e^{-x}` -/

private theorem theta_sub_one_inv540 (x : ℝ) (hx : 0 < x) :
    jacobiTheta (I * (x : ℂ)) - 1 =
      ((x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) * (jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1) +
        ((x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) - 1 := by
  have h := theta_modular540 (x : ℂ) (by simpa using hx)
  have hinv : ((x : ℂ))⁻¹ = ((x⁻¹ : ℝ) : ℂ) := (Complex.ofReal_inv x).symm
  rw [hinv] at h
  rw [h]; ring

private theorem continuousAt_g_540 (x : ℝ) (hx : 0 < x) :
    ContinuousAt (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) x := by
  have him : (Complex.I * (x : ℂ)).im = x := by simp
  have hd : DifferentiableAt ℂ jacobiTheta (Complex.I * (x : ℂ)) :=
    differentiableAt_jacobiTheta (by rw [him]; exact hx)
  have h1 : ContinuousAt (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ))) x :=
    (hd.comp (x : ℂ) (by fun_prop)).continuousAt.comp (by fun_prop)
  have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) x :=
    (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hx)).comp
      (Complex.continuous_ofReal.continuousAt)
  have h3 : ContinuousAt (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) x := by fun_prop
  exact ((h1.sub continuousAt_const).sub (h2.mul h3))


/-- `g` is bounded near `0⁺`. -/
private theorem g_bounded_zero_540 :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ)‖ ≤ 3 := by
  obtain ⟨C, hC, htop⟩ := Asymptotics.isBigO_iff'.mp theta_raw_bounds540'.1
  have hCpos : (0:ℝ) < C := hC
  have hC1 : (0:ℝ) < C + 1 := by linarith
  have hinv := tendsto_inv_nhdsGT_zero.eventually htop
  filter_upwards [hinv, self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ) < min 1 (1 / (C + 1)) by positivity)).filter_mono
      nhdsWithin_le_nhds] with t ht hx hx2
  have htp : 0 < t := hx
  have hx1 : t < 1 := lt_of_lt_of_le hx2 (min_le_left _ _)
  have hx3 : t < 1 / (C + 1) := lt_of_lt_of_le hx2 (min_le_right _ _)
  have hCt : C * t ≤ 1 := by
    have h3 : t * (C + 1) < 1 := (lt_div_iff₀ hC1).mp hx3
    nlinarith
  have ht12 : t ^ ((1/2) : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_ge htp hx1.le (show (0:ℝ) ≤ (1/2) by norm_num)
    rwa [Real.rpow_zero] at h
  -- the modular term
  have hb' : ‖jacobiTheta (Complex.I * ((t⁻¹ : ℝ) : ℂ)) - 1‖ ≤ C * t ^ (2 : ℝ) := by
    have h1 := ht
    have hnorm : ‖((t⁻¹ : ℝ) ^ (-(2 : ℝ)))‖ = t ^ (2 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr htp.le) _),
        Real.inv_rpow htp.le, ← Real.rpow_neg htp.le, neg_neg]
    rwa [hnorm] at h1
  have hdec : ‖((t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) *
      (jacobiTheta (I * ((t⁻¹ : ℝ) : ℂ)) - 1)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re]
    have h1 : t ^ (-(1/2) : ℝ) * t ^ (2 : ℝ) = t ^ ((3/2) : ℝ) := by
      rw [← Real.rpow_add htp]; norm_num
    have h1' : t ^ ((3/2) : ℝ) = t * t ^ ((1/2) : ℝ) := by
      calc t ^ ((3/2) : ℝ) = t ^ ((1:ℝ) + (1/2)) := by norm_num
        _ = t ^ (1:ℝ) * t ^ ((1/2) : ℝ) := Real.rpow_add htp 1 (1/2)
        _ = t * t ^ ((1/2) : ℝ) := by rw [Real.rpow_one]
    have hkey : t ^ (-(1/2) : ℝ) * (C * t ^ (2 : ℝ)) = (C * t) * t ^ ((1/2) : ℝ) := by
      have h2 : t ^ (-(1/2) : ℝ) * (C * t ^ (2 : ℝ))
          = C * (t ^ (-(1/2) : ℝ) * t ^ (2 : ℝ)) := by ring
      rw [h2, h1, h1']; ring
    calc t ^ (-(1/2) : ℝ) * ‖jacobiTheta (I * ((t⁻¹ : ℝ) : ℂ)) - 1‖
        ≤ t ^ (-(1/2) : ℝ) * (C * t ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg htp.le _)
      _ = (C * t) * t ^ ((1/2) : ℝ) := hkey
      _ ≤ 1 * 1 := mul_le_mul hCt ht12 (Real.rpow_nonneg htp.le _) (by norm_num)
      _ = 1 := by norm_num
  -- the remaining terms
  have hrest : ‖((t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)‖ ≤ 2 := by
    have hcast : (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)
        = (((t ^ (-(1 / 2) : ℝ) * Real.exp (-t) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_mul, ← Complex.ofReal_cpow htp.le]
    have hre : ((t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) = (((t ^ (-(1 / 2) : ℝ) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_cpow htp.le]
    rw [hcast, hre, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hone : 1 - Real.exp (-t) ≤ t := by
      have h := Real.add_one_le_exp (-t)
      linarith
    have hone0 : 0 ≤ 1 - Real.exp (-t) := by
      have h := Real.exp_le_one_iff.mpr (by linarith : -t ≤ 0)
      linarith
    have hs0 : 0 ≤ t ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-t)) :=
      mul_nonneg (Real.rpow_nonneg htp.le _) hone0
    have hs1 : t ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-t)) ≤ 1 := by
      have h1 : t ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-t)) ≤ t ^ (-(1 / 2) : ℝ) * t :=
        mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg htp.le _)
      have h2 : t ^ (-(1 / 2) : ℝ) * t = t ^ ((1/2) : ℝ) := by
        calc t ^ (-(1 / 2) : ℝ) * t = t ^ (-(1 / 2) : ℝ) * t ^ (1:ℝ) := by
              rw [Real.rpow_one]
          _ = t ^ (-(1 / 2) + 1 : ℝ) := by rw [Real.rpow_add htp]
          _ = t ^ ((1/2) : ℝ) := by norm_num
      rw [h2] at h1; linarith
    have heq : t ^ (-(1 / 2) : ℝ) - 1 - t ^ (-(1 / 2) : ℝ) * Real.exp (-t)
        = -(1 - t ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-t))) := by ring
    rw [heq, abs_neg]
    have hnn : (0:ℝ) ≤ 1 - t ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-t)) := by linarith
    rw [abs_of_nonneg hnn]
    linarith
  have hsplit : jacobiTheta (I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ)
      = ((t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) * (jacobiTheta (I * ((t⁻¹ : ℝ) : ℂ)) - 1) +
        (((t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) - 1 -
          (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) := by
    rw [theta_sub_one_inv540 t htp]; ring
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (by linarith)

/-- `g` is `O(x^{-(1 / 2)})` at infinity. -/
private theorem g_isBigO_top_540 :
    (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) =O[atTop] (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC, htop⟩ := Asymptotics.isBigO_iff'.mp theta_raw_bounds540'.1
  have hCpos : (0:ℝ) < C := hC
  refine Asymptotics.isBigO_iff.mpr ⟨C + 1, ?_⟩
  filter_upwards [htop, eventually_ge_atTop (1:ℝ)] with t ht hx
  have htp : 0 < t := by linarith
  have hle : t ^ (-(2 : ℝ)) ≤ t ^ (-(1/2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hnorm : ‖t ^ (-(2 : ℝ))‖ = t ^ (-(2 : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htp.le _)]
  have h1 : ‖jacobiTheta (I * (t : ℂ)) - 1‖ ≤ C * t ^ (-(2 : ℝ)) := by
    rw [hnorm] at ht; exact ht
  have h2 : ‖(t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)‖ ≤ t ^ (-(1/2 : ℝ)) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [Complex.ofReal_re]
    have h4 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h5 : t ^ (-(1/2) : ℝ) * Real.exp (-t) ≤ t ^ (-(1/2) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg htp.le _)
    linarith
  have hsplit : jacobiTheta (I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ)
      = (jacobiTheta (I * (t : ℂ)) - 1) -
        (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) := rfl
  rw [hsplit]
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htp.le _)]
  calc ‖(jacobiTheta (I * (t : ℂ)) - 1) - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ)‖
      ≤ ‖jacobiTheta (I * (t : ℂ)) - 1‖ + ‖(t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ C * t ^ (-(2 : ℝ)) + t ^ (-(1/2 : ℝ)) := by linarith
    _ ≤ C * t ^ (-(1/2 : ℝ)) + 1 * t ^ (-(1/2 : ℝ)) := by
        have h5 : C * t ^ (-(2 : ℝ)) ≤ C * t ^ (-(1/2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hle hCpos.le
        linarith
    _ = (C + 1) * t ^ (-(1/2 : ℝ)) := by ring

/-- The Mellin transform of `g` converges at `1/4`. -/
private theorem mellinConvergent_g_540 :
    MellinConvergent (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) ((1/4 : ℝ) : ℂ) := by
  have hcont : ContinuousOn (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) (Set.Ioi 0) :=
    fun x hx => (continuousAt_g_540 x hx).continuousWithinAt
  have hbot : (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 3 ?_
    filter_upwards [g_bounded_zero_540] with t ht
    simpa using ht
  exact mellinConvergent_of_isBigO_rpow (s := ((1/4 : ℝ) : ℂ)) (a := 1/2) (b := 0)
    (hcont.locallyIntegrableOn measurableSet_Ioi) g_isBigO_top_540 (by norm_num)
    hbot (by norm_num)

/-! ## (M2) `mellin g w = 2Λ(2w) - Γ(w-1/2)` on the strip, away from the pole -/

private theorem mellin_theta_sub_one_540 (w : ℂ) (hw : 1 / 2 < w.re) :
    mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1) w =
      2 * completedRiemannZeta (2 * w) := by
  have h := completedZeta_theta_mellin540 w hw
  rw [h]; ring

/-- `x ↦ x^{-1/2} e^{-x}` is continuous on `(0,∞)`. -/
private theorem continuousOn_rpow_exp_540 :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) (Set.Ioi 0) := by
  intro x hx
  have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ)) x :=
    (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hx)).comp
      (Complex.continuous_ofReal.continuousAt)
  exact (h2.mul (by fun_prop)).continuousWithinAt

private theorem isBigO_rpow_exp_bot_540 :
    (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htp : 0 < t := ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Complex.ofReal_re]
  have h4 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h5 : t ^ (-(1 / 2) : ℝ) * Real.exp (-t) ≤ t ^ (-(1 / 2) : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg htp.le _)
  have h6 : (1:ℝ) * t ^ (-(1 / 2) : ℝ) = t ^ (-(1 / 2) : ℝ) := one_mul _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htp.le _), h6]
  linarith

private theorem isBigO_rpow_exp_top_540 :
    (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
      =O[atTop] (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  have htp : 0 < t := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Complex.ofReal_re]
  have hexp : Real.exp (-t) ≤ t⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos t) htp).mpr (by linarith [Real.add_one_le_exp t])
  have hstep : t ^ (-(1 / 2) : ℝ) * Real.exp (-t) ≤ t ^ (-(1 / 2) : ℝ) * t⁻¹ :=
    mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg htp.le _)
  have heq : t ^ (-(1 / 2) : ℝ) * t⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add htp]; norm_num
  have hfin : t ^ (-(1 / 2) : ℝ) * Real.exp (-t) ≤ t ^ (-(3 / 2) : ℝ) :=
    hstep.trans_eq heq
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htp.le _)]
  calc t ^ (-(1 / 2) : ℝ) * Real.exp (-t) ≤ t ^ (-(3 / 2) : ℝ) := hfin
    _ = 1 * t ^ (-(3 / 2) : ℝ) := by ring

/-- `mellin (x ↦ x^{-1/2} e^{-x}) w = Γ (w - 1/2)` for `Re w > 1/2`. -/
private theorem mellin_rpow_exp_540 (w : ℂ) (hw : 1 / 2 < w.re) :
    mellin (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) w =
      Complex.Gamma (w - 1 / 2) := by
  have h1 : (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
      = (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) • ((Real.exp (-t) : ℝ) : ℂ)) := rfl
  rw [h1, mellin_cpow_smul]
  have hre : (w + ((-(1 / 2) : ℝ) : ℂ)).re = w.re - 1/2 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  rw [mellin_exp_neg_eq_gamma_540 _ (by rw [hre]; linarith)]
  congr 1
  push_cast
  ring

private theorem mellin_g_right_540 (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 3 / 2) :
    mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) w = 2 * completedRiemannZeta (2 * w) - Complex.Gamma (w - 1/2) := by
  have hcont : ContinuousOn (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1) (Set.Ioi 0) := by
    intro x hx
    have him : (Complex.I * (x : ℂ)).im = x := by simp
    have hd : DifferentiableAt ℂ jacobiTheta (Complex.I * (x : ℂ)) :=
      differentiableAt_jacobiTheta (by rw [him]; exact hx)
    exact (((hd.comp (x : ℂ) (by fun_prop)).continuousAt.comp (by fun_prop)).sub
      continuousAt_const).continuousWithinAt
  have hi1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) •
      (jacobiTheta (Complex.I * (t : ℂ)) - 1)) (Set.Ioi 0) :=
    mellinConvergent_of_isBigO_rpow (s := w) (a := 2) (b := 1/2)
      (hcont.locallyIntegrableOn measurableSet_Ioi) theta_raw_bounds540'.1
      (by linarith : w.re < 2) theta_raw_bounds540'.2 hw1
  have hconv : MellinConvergent (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) w :=
    mellinConvergent_of_isBigO_rpow (s := w) (a := 3/2) (b := 1/2)
      (continuousOn_rpow_exp_540.locallyIntegrableOn measurableSet_Ioi)
      isBigO_rpow_exp_top_540 hw2 isBigO_rpow_exp_bot_540 hw1
  have hi2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) *
      ((t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))) (Set.Ioi 0) := by
    have h := hconv
    simp only [MellinConvergent, smul_eq_mul] at h
    exact h
  have hsub : mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) w
      = mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1) w -
        mellin (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) w := by
    rw [mellin, mellin, mellin, ← integral_sub]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [smul_eq_mul, Pi.sub_apply]
      ring
    · exact hi1
    · exact hi2
  rw [hsub, mellin_theta_sub_one_540 w hw1, mellin_rpow_exp_540 w hw1]

/-! ## (M2b) the identity at `Re w = 1/4`, for `Im w ≠ 0` -/

/-- `g` is `O(x^{-3/2})` at infinity. -/
private theorem g_isBigO_top_three_halves_540 :
    (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) =O[atTop] (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) := by
  have h1 : (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1)
      =O[atTop] (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) := by
    obtain ⟨C, hC, htop⟩ := Asymptotics.isBigO_iff'.mp theta_raw_bounds540'.1
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [htop, eventually_ge_atTop (1:ℝ)] with t ht hx
    have htp : 0 < t := by linarith
    have hn2 : ‖t ^ (-(2:ℝ))‖ = t ^ (-(2:ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htp.le _)]
    have hn3 : ‖t ^ (-(3/2):ℝ)‖ = t ^ (-(3/2):ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htp.le _)]
    rw [hn2] at ht
    rw [hn3]
    calc ‖jacobiTheta (Complex.I * (t : ℂ)) - 1‖ ≤ C * t ^ (-(2:ℝ)) := ht
      _ ≤ C * t ^ (-(3/2) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (-2:ℝ) ≤ -(3/2))
  have h2 : (fun t : ℝ => (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
      =O[atTop] (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) := isBigO_rpow_exp_top_540
  have hsplit : (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ))
      = (fun t : ℝ => (jacobiTheta (Complex.I * (t : ℂ)) - 1) -
        (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) := rfl
  rw [hsplit]
  exact h1.sub h2

private theorem g_isBigO_bot_zero_540 :
    (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [g_bounded_zero_540] with t ht
  simpa using ht

/-- `g` is continuous on `(0,∞)`. -/
private theorem continuousOn_g_540 :
    ContinuousOn (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) (Set.Ioi 0) :=
  fun x hx => (continuousAt_g_540 x hx).continuousWithinAt

/-- The Mellin identity of `g` on the line `Re w = 1/4`, away from the real axis. -/
private theorem mellin_g_quarter_540 (y : ℝ) (hy : y ≠ 0) :
    mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 - (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
      ((Real.exp (-t) : ℝ) : ℂ)) (((1/4 : ℝ)) + (y : ℂ) * Complex.I)
      = 2 * completedRiemannZeta (2 * ((((1/4 : ℝ)) + (y : ℂ) * Complex.I))) -
        Complex.Gamma (((((1/4 : ℝ)) + (y : ℂ) * Complex.I)) - 1/2) := by
  set r : ℝ := |y| / 2 with hr
  have hrpos : 0 < r := by
    rw [hr]; exact half_pos (abs_pos.mpr hy)
  set Ω : Set ℂ := Complex.reCLM ⁻¹' Set.Ioo ((1/8 : ℝ)) ((5/4 : ℝ)) ∩
    Complex.imCLM ⁻¹' Metric.ball y r with hΩ
  have hΩopen : IsOpen Ω := (isOpen_Ioo.preimage Complex.continuous_re).inter
    (Metric.isOpen_ball.preimage Complex.continuous_im)
  have hΩconv : Convex ℝ Ω :=
    ((convex_Ioo _ _).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_ball y r).linear_preimage Complex.imCLM.toLinearMap)
  have hval : ∀ z ∈ Ω, (1/8 : ℝ) < z.re ∧ z.re < 5/4 ∧ |z.im - y| < r := by
    intro z hz
    rw [hΩ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Complex.reCLM_apply,
      Complex.imCLM_apply, Set.mem_Ioo, Metric.mem_ball, Real.dist_eq] at hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  have hzene : ∀ z ∈ Ω, z.im ≠ 0 := by
    intro z hz h0
    obtain ⟨-, -, hb⟩ := hval z hz
    rw [h0, zero_sub, abs_neg] at hb
    rw [hr] at hb
    linarith [abs_pos.mpr hy]
  have hw : (((1/4 : ℝ)) + (y : ℂ) * Complex.I) ∈ Ω := by
    rw [hΩ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Complex.reCLM_apply,
      Complex.imCLM_apply, Set.mem_Ioo, Metric.mem_ball, Real.dist_eq]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    have him : (((1/4 : ℝ)) + (y : ℂ) * Complex.I).im = y := by simp
    rw [him, hr, sub_self, abs_zero]
    exact hrpos
  have hw₁ : (((1:ℝ)) + (y : ℂ) * Complex.I) ∈ Ω := by
    rw [hΩ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Complex.reCLM_apply,
      Complex.imCLM_apply, Set.mem_Ioo, Metric.mem_ball, Real.dist_eq]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    have him : (((1:ℝ)) + (y : ℂ) * Complex.I).im = y := by simp
    rw [him, hr, sub_self, abs_zero]
    exact hrpos
  have hM : DifferentiableOn ℂ (mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))) Ω := by
    intro z hz
    obtain ⟨hz1, hz2, -⟩ := hval z hz
    exact (mellin_differentiableAt_of_isBigO_rpow
      (continuousOn_g_540.locallyIntegrableOn measurableSet_Ioi)
      g_isBigO_top_three_halves_540 (by linarith : z.re < 3/2) g_isBigO_bot_zero_540
      (by linarith : 0 < z.re)).differentiableWithinAt
  have hF : DifferentiableOn ℂ (fun z : ℂ => 2 * completedRiemannZeta (2 * z) -
      Complex.Gamma (z - 1/2)) Ω := by
    intro z hz
    obtain ⟨hz1, hz2, -⟩ := hval z hz
    have hzne : z.im ≠ 0 := hzene z hz
    have hz0 : z ≠ 0 := by intro h; exact hzne (by rw [h]; simp)
    have hs : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz0
    have hs1 : 2 * z ≠ 1 := by
      intro h
      have hz : z = 1/2 := by
        have h2 : (2:ℂ) * z = 2 * (1/2) := by rw [h]; norm_num
        exact mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0) h2
      exact hzne (by rw [hz]; norm_num)
    have hΛ : DifferentiableAt ℂ (fun z : ℂ => 2 * completedRiemannZeta (2 * z)) z := by
      have h0 : DifferentiableAt ℂ completedRiemannZeta (2 * z) :=
        differentiableAt_completedZeta hs hs1
      exact (h0.comp z (by fun_prop)).const_mul 2
    have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z - 1/2)) z := by
      refine (Complex.differentiableAt_Gamma _ ?_).comp z (by fun_prop)
      intro m hm
      have h' := congrArg Complex.im hm
      simp only [Complex.sub_im, Complex.neg_im, Complex.natCast_im] at h'
      have h2 : ((1/2 : ℂ)).im = 0 := by norm_num
      exact hzne (by linarith)
    exact (hΛ.sub hΓ).differentiableWithinAt
  have hnear : mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
      =ᶠ[𝓝 (((1:ℝ)) + (y : ℂ) * Complex.I)]
      (fun z : ℂ => 2 * completedRiemannZeta (2 * z) - Complex.Gamma (z - 1/2)) := by
    have hre1 : ((((1:ℝ)) + (y : ℂ) * Complex.I)).re = 1 := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show ((1/2 : ℝ)) < ((((1:ℝ)) + (y : ℂ) * Complex.I)).re by rw [hre1]; norm_num),
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show ((((1:ℝ)) + (y : ℂ) * Complex.I)).re < ((3/2 : ℝ)) by rw [hre1]; norm_num)]
      with z hz1 hz2
    exact mellin_g_right_540 z hz1 hz2
  exact (hM.analyticOnNhd hΩopen).eqOn_of_preconnected_of_eventuallyEq
    (hF.analyticOnNhd hΩopen) hΩconv.isPreconnected hw₁ hnear hw

/-! ## (M3) `VerticalIntegrable (mellin g) (1/4)` -/

private theorem continuous_lambda_half_540 (y : ℝ) :
    ContinuousAt (fun s : ℝ =>
      completedRiemannZeta ((1/2 : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I)) y := by
  have hpt : (1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
  have hpt1 : (1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
  have hΛ : ContinuousAt completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I) :=
    (differentiableAt_completedZeta hpt hpt1).continuousAt
  have h2 : ContinuousAt (fun s : ℝ => (1/2 : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I) y := by
    fun_prop
  exact hΛ.tendsto.comp h2.tendsto

private theorem continuous_gamma_neg_quarter_540 (y : ℝ) :
    ContinuousAt (fun s : ℝ =>
      Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (s : ℂ) * Complex.I)) y := by
  have hΓ : ContinuousAt Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) := by
    refine Complex.continuousAt_Gamma _ (by
      intro m hm
      have h' := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.neg_re, zero_mul, add_zero] at h'
      have hm1 : (m : ℝ) = 1/4 := by linarith
      have h4 : ((4 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
      have h5 : 4 * m = 1 := by exact_mod_cast h4
      omega)
  have h2 : ContinuousAt (fun s : ℝ => ((((-(1/4) : ℝ)) : ℂ) + (s : ℂ) * Complex.I)) y := by
    fun_prop
  exact hΓ.tendsto.comp h2.tendsto

private theorem continuous_cpow_quarter_540 (x : ℝ) (hx : 0 < x) :
    Continuous fun y : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [continuous_iff_continuousAt]
  intro y
  exact (continuousAt_const_cpow hxne).comp (by fun_prop)

private theorem norm_cpow_quarter_540 (x : ℝ) (hx : 0 < x) (y : ℝ) :
    ‖(x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I))‖ = x ^ (-(1/4) : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp

private theorem integrable_weighted_lambda_540 (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) := by
  have hbase : Integrable (fun y : ℝ =>
      2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) :=
    integrable_half_line_540.const_mul (2:ℂ)
  refine Integrable.congr (hbase.bdd_mul (continuous_cpow_quarter_540 x hx).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => le_of_eq (norm_cpow_quarter_540 x hx y))) ?_
  filter_upwards [] with y
  exact (smul_eq_mul _ _).symm

private theorem integrable_weighted_gamma_540 (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) :=
  Integrable.congr (integrable_gamma_neg_quarter_540.bdd_mul
    (continuous_cpow_quarter_540 x hx).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => le_of_eq (norm_cpow_quarter_540 x hx y)))
    (Filter.Eventually.of_forall fun y => (smul_eq_mul _ _).symm)

set_option maxHeartbeats 1000000 in
private theorem verticalIntegrable_mellin_g_540 :
    Complex.VerticalIntegrable (mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))) (1/4) := by
  have hne : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have h1 : Integrable (fun y : ℝ => 2 * completedRiemannZeta
      (2 * (((1/4 : ℝ)) + (y : ℂ) * Complex.I))) := by
    have h0 : Integrable (fun y : ℝ =>
        2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) :=
      integrable_half_line_540.const_mul (2:ℂ)
    refine h0.congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [show 2 * (((1/4 : ℝ)) + (y : ℂ) * Complex.I) =
      (1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  have h2 : Integrable (fun y : ℝ =>
      Complex.Gamma ((((1/4 : ℝ)) + (y : ℂ) * Complex.I) - 1/2)) := by
    refine integrable_gamma_neg_quarter_540.congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [show ((((1/4 : ℝ)) + (y : ℂ) * Complex.I) - 1/2) =
      ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) by push_cast; ring]
  have hRHS : Integrable (fun y : ℝ => 2 * completedRiemannZeta
      (2 * (((1/4 : ℝ)) + (y : ℂ) * Complex.I)) -
      Complex.Gamma ((((1/4 : ℝ)) + (y : ℂ) * Complex.I) - 1/2)) := h1.sub h2
  show Integrable (fun y : ℝ => mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
    (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) ((1/4 : ℝ) + y * Complex.I))
  refine hRHS.congr ?_
  filter_upwards [hne] with y hy
  exact (mellin_g_quarter_540 y hy).symm

/-! ## (M4) the inversion at `σ = 1/4` -/

set_option maxHeartbeats 1000000 in
private theorem star_eq_540 (x : ℝ) (hx : 0 < x) :
    (1 / (2 * Real.pi)) • (∫ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      = (jacobiTheta (Complex.I * (x : ℂ)) - 1) - (x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) := by
  have hne : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hWs : Integrable (fun y : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) :=
    integrable_weighted_lambda_540 x hx
  have hWg : Integrable (fun y : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) :=
    integrable_weighted_gamma_540 x hx
  have hpt : ∀ᵐ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
        mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
          (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) ((1/4 : ℝ) + y * Complex.I)
      = (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) -
        (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
          Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) := by
    filter_upwards [hne] with y hy
    rw [mellin_g_quarter_540 y hy]
    rw [show 2 * (((1/4 : ℝ)) + (y : ℂ) * Complex.I) =
        (1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show ((((1/4 : ℝ)) + (y : ℂ) * Complex.I) - 1/2) =
        ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) by push_cast; ring,
      smul_sub]
  have hinv := mellinInv_mellin_eq (1/4) (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) hx
      mellinConvergent_g_540 verticalIntegrable_mellin_g_540 (continuousAt_g_540 x hx)
  have hexp : mellinInv (1/4) (mellin (fun t : ℝ => jacobiTheta (Complex.I * (t : ℂ)) - 1 -
      (t : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))) x
      = (1 / (2 * Real.pi)) • ((∫ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) -
        ∫ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
          Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) := by
    simp only [mellinInv]
    rw [integral_congr_ae hpt, integral_sub hWs hWg]
  rw [hexp, smul_sub] at hinv
  have hfac : ∀ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I))
      = (x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        (x : ℂ) ^ (-(((-(1/4) : ℝ)) + (y : ℂ) * Complex.I)) := by
    intro y
    rw [← Complex.cpow_add _ _ hxne]
    congr 1
    push_cast
    ring
  have hv : mellinInv (-(1/4)) Complex.Gamma x = (1 / (2 * Real.pi)) •
      ∫ y : ℝ, (x : ℂ) ^ (-(((-(1/4) : ℝ)) + (y : ℂ) * Complex.I)) •
        Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I) := rfl
  have hI : (∫ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
        Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I))
      = (x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) *
        (∫ y : ℝ, (x : ℂ) ^ (-(((-(1/4) : ℝ)) + (y : ℂ) * Complex.I)) •
          Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hfac y, smul_eq_mul]
    ring
  have hB : (1 / (2 * Real.pi)) • (∫ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      Complex.Gamma ((((-(1/4) : ℝ)) : ℂ) + (y : ℂ) * Complex.I))
      = (x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * mellinInv (-(1/4)) Complex.Gamma x := by
    rw [hI, hv, Complex.real_smul, Complex.real_smul]
    ring
  rw [hB, mellinInv_gamma_neg_540 x hx] at hinv
  have hgoal : (1 / (2 * Real.pi)) • (∫ y : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ)) + (y : ℂ) * Complex.I)) •
      (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      = (jacobiTheta (Complex.I * (x : ℂ)) - 1 -
          (x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-x) : ℝ) : ℂ)) +
        (x : ℂ) ^ ((-(1 / 2) : ℝ) : ℂ) * ((Real.exp (-x) - 1 : ℝ) : ℂ) := by
    rw [← hinv]
    ring
  rw [hgoal]
  push_cast
  ring

/-! ## (M5) the `α`-parametrised contour integral is holomorphic on `|Re α| < π/2` -/

private theorem continuous_P_integrand_540 (β : ℂ) :
    Continuous fun y : ℝ => Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
      (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact ((by fun_prop : ContinuousAt (fun y : ℝ =>
    Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))) y)).mul
    ((continuous_lambda_half_540 y).const_mul 2)

private theorem continuous_P_deriv_integrand_540 (β : ℂ) :
    Continuous fun y : ℝ => (-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
      Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
      (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact ((by fun_prop : ContinuousAt (fun y : ℝ =>
    (-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
      Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))) y)).mul
    ((continuous_lambda_half_540 y).const_mul 2)

set_option maxHeartbeats 2000000 in
private theorem hasDerivAt_P_540 (α : ℂ) (hα : |α.re| < Real.pi / 2) :
    HasDerivAt (fun β : ℂ => (1 / (2 * Real.pi)) • ∫ y : ℝ,
        Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      ((1 / (2 * Real.pi)) • ∫ y : ℝ,
        (-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          Complex.exp (-(Complex.I) * α * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) α := by
  have ha0 : (0:ℝ) ≤ |α.re| := abs_nonneg _
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set c : ℝ := (|α.re| + Real.pi / 2) / 2 with hc
  set r : ℝ := (Real.pi / 2 - |α.re|) / 4 with hrr
  have hrpos : 0 < r := by rw [hrr]; linarith
  have hca : |α.re| < c := by rw [hc]; linarith
  have hc2 : c < Real.pi / 2 := by rw [hc]; linarith
  have hcpos : 0 < c := by linarith
  have hgap : 0 < c - (|α.re| + r) := by rw [hrr, hc]; linarith
  obtain ⟨K, hKpos, hK⟩ := completedZeta_half_line_decay_540 c hcpos hc2
  set Cst : ℝ := 2 * K * Real.exp ((|α.im| + r) / 4) with hCst
  have hCst0 : 0 < Cst := by rw [hCst]; positivity
  -- integrability of the two majorants
  have hbndF_int : Integrable (fun y : ℝ => Cst * Real.exp (-((c - (|α.re| + r)) * |y|))) := by
    have h1 := exp_abs_pow_integrable_540 (c - (|α.re| + r)) hgap 0
    refine (h1.const_mul Cst).congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [pow_zero, mul_one]
  have hbndF'_int : Integrable (fun y : ℝ =>
      Cst * ((1 + |y|) * Real.exp (-((c - (|α.re| + r)) * |y|)))) := by
    have h1 := exp_abs_pow_integrable_540 (c - (|α.re| + r)) hgap 1
    refine (h1.const_mul Cst).congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [pow_one]
    ring
  -- membership estimates
  have hball : ∀ β ∈ Metric.ball α r, |β.re| ≤ |α.re| + r := by
    intro β hβ
    have hd : ‖β - α‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hβ
    have h1 : |β.re - α.re| ≤ ‖β - α‖ := by simpa using Complex.abs_re_le_norm (β - α)
    calc |β.re| = |α.re + (β.re - α.re)| := by ring_nf
      _ ≤ |α.re| + |β.re - α.re| := abs_add_le _ _
      _ ≤ |α.re| + r := by linarith
  have hball_im : ∀ β ∈ Metric.ball α r, |β.im| ≤ |α.im| + r := by
    intro β hβ
    have hd : ‖β - α‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hβ
    have h1 : |β.im - α.im| ≤ ‖β - α‖ := by
      have h := Complex.abs_im_le_norm (β - α)
      simpa using h
    calc |β.im| = |α.im + (β.im - α.im)| := by ring_nf
      _ ≤ |α.im| + |β.im - α.im| := abs_add_le _ _
      _ ≤ |α.im| + r := by linarith
  -- the exponential bound
  have hexp_bound : ∀ (β : ℂ) (y : ℝ), |β.re| ≤ |α.re| + r → |β.im| ≤ |α.im| + r →
      ‖Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        Real.exp ((|α.im| + r) / 4) * Real.exp ((|α.re| + r) * |y|) := by
    intro β y h1 h2
    rw [Complex.norm_exp]
    have hre : (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re = β.im / 4 + β.re * y := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, Real.exp_add]
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg β.im, le_abs_self β.im]
    · apply Real.exp_le_exp.mpr
      calc β.re * y ≤ |β.re * y| := le_abs_self _
        _ = |β.re| * |y| := abs_mul _ _
        _ ≤ (|α.re| + r) * |y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg y)
    · positivity
    · positivity
  have hexp2 : ∀ y : ℝ, Real.exp ((|α.re| + r) * |y|) * Real.exp (-(c * |y|)) =
      Real.exp (-((c - (|α.re| + r)) * |y|)) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    ring
  -- bound for the integrand itself
  have hF_bound : ∀ᵐ y : ℝ, ∀ β ∈ Metric.ball α r,
      ‖Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))‖ ≤
      Cst * Real.exp (-((c - (|α.re| + r)) * |y|)) := by
    filter_upwards [] with y
    intro β hβ
    have he := hexp_bound β y (hball β hβ) (hball_im β hβ)
    have hΛ := hK y
    simp only [norm_mul, Complex.norm_ofNat]
    calc ‖Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖ *
          (2 * ‖completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)‖)
        ≤ ‖Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖ *
            (2 * (K * Real.exp (-(c * |y|)))) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hΛ (by norm_num)
      _ ≤ (Real.exp ((|α.im| + r) / 4) * Real.exp ((|α.re| + r) * |y|)) *
            (2 * (K * Real.exp (-(c * |y|)))) := by
          apply mul_le_mul_of_nonneg_right he (by positivity)
      _ = Cst * Real.exp (-((c - (|α.re| + r)) * |y|)) := by
          rw [hCst, ← hexp2 y]
          ring
  -- bound for the derivative integrand
  have hF'_bound : ∀ᵐ y : ℝ, ∀ β ∈ Metric.ball α r,
      ‖(-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))‖ ≤
      Cst * ((1 + |y|) * Real.exp (-((c - (|α.re| + r)) * |y|))) := by
    filter_upwards [] with y
    intro β hβ
    have he := hexp_bound β y (hball β hβ) (hball_im β hβ)
    have hΛ := hK y
    have hcoef : ‖-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 1 + |y| := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      calc ‖((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ ‖((((1/4 : ℝ)) : ℂ))‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 1/4 + |y| := by simp
        _ ≤ 1 + |y| := by linarith [abs_nonneg y]
    calc ‖(-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))‖
        = ‖-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖ *
            ‖Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖ *
            (2 * ‖completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)‖) := by
          simp only [norm_mul, Complex.norm_ofNat]
      _ ≤ (1 + |y|) * (Real.exp ((|α.im| + r) / 4) * Real.exp ((|α.re| + r) * |y|)) *
            (2 * (K * Real.exp (-(c * |y|)))) := by
          apply mul_le_mul
          · exact mul_le_mul hcoef he (norm_nonneg _) (by positivity)
          · linarith
          · positivity
          · positivity
      _ = Cst * ((1 + |y|) * Real.exp (-((c - (|α.re| + r)) * |y|))) := by
          rw [hCst, ← hexp2 y]
          ring
  -- differentiability in the parameter
  have hdiff : ∀ᵐ y : ℝ, ∀ β ∈ Metric.ball α r,
      HasDerivAt (fun β : ℂ => Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
        ((-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) β := by
    refine Filter.Eventually.of_forall fun y β _ => ?_
    have h1 : HasDerivAt (fun β : ℂ => -(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))
        (-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) β := by
      have h0 := ((hasDerivAt_id β).const_mul (-(Complex.I))).mul_const
        ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)
      simpa using h0
    have h2 := (Complex.hasDerivAt_exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))).comp β h1
    have h3 := h2.mul_const (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))
    refine h3.congr_deriv ?_
    ring
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ))
    (bound := fun y : ℝ => Cst * ((1 + |y|) * Real.exp (-((c - (|α.re| + r)) * |y|))))
    (s := Metric.ball α r)
    (F := fun β : ℂ => fun y : ℝ =>
      Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
    (F' := fun β : ℂ => fun y : ℝ =>
      (-(Complex.I) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        Complex.exp (-(Complex.I) * β * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
    (Metric.ball_mem_nhds α hrpos)
    (Filter.Eventually.of_forall fun β => (continuous_P_integrand_540 β).aestronglyMeasurable)
    (by
      refine Integrable.mono' hbndF_int (continuous_P_integrand_540 α).aestronglyMeasurable ?_
      filter_upwards [hF_bound] with y hy
      exact hy α (Metric.mem_ball_self hrpos))
    (continuous_P_deriv_integrand_540 α).aestronglyMeasurable
    hF'_bound hbndF'_int hdiff).2
  exact hmain.const_smul (1 / (2 * Real.pi))

/-! ## (M5b) the identity in `α` -/

private theorem strip_open_540 : IsOpen {α : ℂ | |α.re| < Real.pi / 2} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

private theorem strip_convex_540 : Convex ℝ {α : ℂ | |α.re| < Real.pi / 2} := by
  have h : {α : ℂ | |α.re| < Real.pi / 2} =
      Complex.reCLM ⁻¹' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext α
    simp [Complex.reCLM_apply, abs_lt, and_comm]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.reCLM.toLinearMap

private theorem exp_I_re_pos_540 (α : ℂ) (hα : |α.re| < Real.pi / 2) :
    0 < (Complex.exp (Complex.I * α)).re := by
  rw [Complex.exp_re]
  have hre : (Complex.I * α).re = -α.im := by simp [Complex.mul_re]
  have him : (Complex.I * α).im = α.re := by simp [Complex.mul_im]
  rw [hre, him]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hα))

private theorem differentiableOn_P_540 :
    DifferentiableOn ℂ (fun α : ℂ => (1 / (2 * Real.pi)) • ∫ y : ℝ,
        Complex.exp (-(Complex.I) * α * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      {α : ℂ | |α.re| < Real.pi / 2} := by
  intro α hα
  exact (hasDerivAt_P_540 α hα).differentiableAt.differentiableWithinAt

private theorem differentiableOn_theta_540 :
    DifferentiableOn ℂ (fun α : ℂ => jacobiTheta (Complex.I * Complex.exp (Complex.I * α)) - 1 -
      Complex.exp (-(Complex.I * α / 2))) {α : ℂ | |α.re| < Real.pi / 2} := by
  intro α hα
  have hpos := exp_I_re_pos_540 α hα
  have hd : DifferentiableAt ℂ jacobiTheta (Complex.I * Complex.exp (Complex.I * α)) :=
    differentiableAt_jacobiTheta (by simpa using hpos)
  have hg : DifferentiableAt ℂ (fun α : ℂ => Complex.I * Complex.exp (Complex.I * α)) α := by
    fun_prop
  have h1 : DifferentiableAt ℂ (fun α : ℂ => jacobiTheta
      (Complex.I * Complex.exp (Complex.I * α))) α := by
    simpa only [Function.comp_def] using hd.comp α hg
  have h2 : DifferentiableAt ℂ (fun α : ℂ => Complex.exp (-(Complex.I * α / 2))) α := by
    fun_prop
  exact ((h1.sub (differentiableAt_const (1:ℂ))).sub h2).differentiableWithinAt

private theorem log_exp_neg_540 (β : ℝ) :
    Complex.log ((((Real.exp (-β) : ℝ)) : ℂ)) = ((-β : ℝ) : ℂ) := by
  rw [show ((((Real.exp (-β) : ℝ)) : ℂ)) = Complex.exp ((-β : ℝ) : ℂ) by
    rw [Complex.ofReal_exp]]
  exact Complex.log_exp (by simp only [Complex.ofReal_im]; linarith [Real.pi_pos])
    (by simp only [Complex.ofReal_im]; linarith [Real.pi_pos])

/-- On the imaginary axis the parametrised integral equals the theta expression. -/
private theorem P_imaginary_540 (β : ℝ) :
    (1 / (2 * Real.pi)) • (∫ y : ℝ,
        Complex.exp (-(Complex.I) * ((Complex.I) * (β : ℂ)) *
          ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      = jacobiTheta (Complex.I * Complex.exp (Complex.I * ((Complex.I) * (β : ℂ)))) - 1 -
        Complex.exp (-(Complex.I * ((Complex.I) * (β : ℂ)) / 2)) := by
  have hx : (0:ℝ) < Real.exp (-β) := Real.exp_pos _
  have hxne : (((Real.exp (-β) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpt : ∀ y : ℝ,
      Complex.exp (-(Complex.I) * ((Complex.I) * (β : ℂ)) * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) =
      ((((Real.exp (-β) : ℝ)) : ℂ)) ^ (-(((1/4 : ℝ)) + (y : ℂ) * Complex.I)) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero hxne, log_exp_neg_540 β]
    congr 1
    have h1 : -(Complex.I * ((Complex.I) * (β : ℂ))) = (β : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im] <;> ring
    rw [show -(Complex.I) * ((Complex.I) * (β : ℂ)) =
      -(Complex.I * ((Complex.I) * (β : ℂ))) by ring, h1]
    push_cast
    ring
  have htheta : Complex.exp (Complex.I * ((Complex.I) * (β : ℂ))) = (((Real.exp (-β) : ℝ)) : ℂ) := by
    have h1 : Complex.I * ((Complex.I) * (β : ℂ)) = ((-β : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im] <;> ring
    rw [h1, Complex.ofReal_exp]
  have hsqrt : Complex.exp (-(Complex.I * ((Complex.I) * (β : ℂ)) / 2)) =
      ((((Real.exp (-β) : ℝ)) : ℂ)) ^ ((-(1 / 2) : ℝ) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hxne, log_exp_neg_540 β]
    congr 1
    have h1 : Complex.I * ((Complex.I) * (β : ℂ)) = -(β : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im] <;> ring
    rw [show -(Complex.I * ((Complex.I) * (β : ℂ)) / 2) =
      -(Complex.I * ((Complex.I) * (β : ℂ))) / 2 by ring, h1]
    push_cast
    ring
  have hL : (∫ y : ℝ,
        Complex.exp (-(Complex.I) * ((Complex.I) * (β : ℂ)) *
          ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      = ∫ y : ℝ, ((((Real.exp (-β) : ℝ)) : ℂ)) ^ (-(((1/4 : ℝ)) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hpt y]
  rw [hL, htheta, hsqrt]
  exact star_eq_540 (Real.exp (-β)) hx

set_option maxHeartbeats 1000000 in
private theorem P_eq_theta_540 (α : ℂ) (hα : |α.re| < Real.pi / 2) :
    (1 / (2 * Real.pi)) • (∫ y : ℝ,
        Complex.exp (-(Complex.I) * α * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))
      = jacobiTheta (Complex.I * Complex.exp (Complex.I * α)) - 1 -
        Complex.exp (-(Complex.I * α / 2)) := by
  set P : ℂ → ℂ := fun α : ℂ => (1 / (2 * Real.pi)) • (∫ y : ℝ,
        Complex.exp (-(Complex.I) * α * ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) with hP
  set Q : ℂ → ℂ := fun α : ℂ => jacobiTheta (Complex.I * Complex.exp (Complex.I * α)) - 1 -
        Complex.exp (-(Complex.I * α / 2)) with hQ
  have hdiffP : DifferentiableOn ℂ P {α : ℂ | |α.re| < Real.pi / 2} := differentiableOn_P_540
  have hdiffQ : DifferentiableOn ℂ Q {α : ℂ | |α.re| < Real.pi / 2} := differentiableOn_theta_540
  have hmem : (0:ℂ) ∈ closure (({z : ℂ | P z = Q z}) \ {(0:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hε2 : (0:ℝ) < ε / 2 := by linarith
    refine ⟨Complex.I * ((ε/2 : ℝ) : ℂ), ?_, ?_⟩
    · simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rw [hP, hQ]
        exact P_imaginary_540 (ε/2)
      · intro h
        have h' := congrArg Complex.im h
        simp at h'
        linarith
    · rw [dist_eq_norm, zero_sub, norm_neg]
      have hnorm : ‖Complex.I * ((ε/2 : ℝ) : ℂ)‖ = ε/2 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hε2]
      rw [hnorm]
      linarith
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
    (hdiffP.analyticOnNhd strip_open_540) (hdiffQ.analyticOnNhd strip_open_540)
    (strip_convex_540.isPreconnected)
    (show (0:ℂ) ∈ {α : ℂ | |α.re| < Real.pi / 2} by
      simp only [Set.mem_setOf_eq, Complex.zero_re, abs_zero]
      exact half_pos Real.pi_pos)
    hmem
  exact hEqOn hα

/-! ## (M6) the contour-shift identity `hshift` -/

set_option maxHeartbeats 2000000 in
private theorem hshift_540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    Complex.exp ((α : ℂ) * Complex.I / 4) * hardyUnshifted540 α =
      (∫ t : ℝ, Complex.exp ((α : ℂ) * (t : ℂ)) * completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) +
      (Real.pi : ℂ) * Complex.exp (-((α : ℂ) * Complex.I / 4)) := by
  have hα' : |((α : ℂ)).re| < Real.pi / 2 := by simpa using hα
  have hP := P_eq_theta_540 (α : ℂ) hα'
  rw [show Complex.exp (-(Complex.I * (α : ℂ) / 2)) = Complex.exp (-((α : ℂ) * Complex.I / 2)) by
      rw [show -(Complex.I * (α : ℂ) / 2) = -((α : ℂ) * Complex.I / 2) by ring],
    show Complex.I * Complex.exp (Complex.I * (α : ℂ)) =
      Complex.I * Complex.exp ((α : ℂ) * Complex.I) by
      rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring]] at hP
  have hexp1' : Complex.exp ((α : ℂ) * Complex.I / 4) * Complex.exp (-((α : ℂ) * Complex.I / 4)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have hexp3 : Complex.exp ((α : ℂ) * Complex.I / 4) * Complex.exp (-((α : ℂ) * Complex.I / 2)) =
      Complex.exp (-((α : ℂ) * Complex.I / 4)) := by
    rw [← Complex.exp_add]; ring_nf
  have hcpi : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  have hcpi' : (2 * (Real.pi : ℂ)) * (((1 / (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
    rw [mul_comm]; exact hcpi
  -- the pointwise factorisation of the integrand
  have hfac : ∀ y : ℝ, Complex.exp (-(Complex.I) * (α : ℂ) *
      ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) =
      Complex.exp (-((α : ℂ) * Complex.I / 4)) * Complex.exp ((α : ℂ) * (y : ℂ)) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im] <;> ring
  -- extract the constant from the integral
  have hL : (∫ y : ℝ, Complex.exp (-(Complex.I) * (α : ℂ) *
        ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) =
      Complex.exp (-((α : ℂ) * Complex.I / 4)) *
        (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) := by
    have hp : (∫ y : ℝ, Complex.exp (-(Complex.I) * (α : ℂ) *
          ((((1/4 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) =
        ∫ y : ℝ, Complex.exp (-((α : ℂ) * Complex.I / 4)) *
          (Complex.exp ((α : ℂ) * (y : ℂ)) *
            (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hfac y]
      ring
    rw [hp, integral_const_mul]
  -- pull the factor 2 out of the plain integral
  have hI2 : (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
        (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))) =
      2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
        completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hL] at hP
  have hP1 : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (Complex.exp (-((α : ℂ) * Complex.I / 4)) *
        (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
          (2 * completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))) =
      jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1 -
        Complex.exp (-((α : ℂ) * Complex.I / 2)) := by
    rw [← hP]
    simp only [Complex.real_smul]
  rw [hI2] at hP1
  -- multiply the identity by `2 * π * e^{iα/4}`
  have hide : (2 * (Real.pi : ℂ) * Complex.exp ((α : ℂ) * Complex.I / 4)) *
      ((((1 / (2 * Real.pi) : ℝ) : ℂ)) * (Complex.exp (-((α : ℂ) * Complex.I / 4)) *
        (2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
          completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I))))) =
      2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
        completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by
    calc (2 * (Real.pi : ℂ) * Complex.exp ((α : ℂ) * Complex.I / 4)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) * (Complex.exp (-((α : ℂ) * Complex.I / 4)) *
            (2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
              completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))))
        = ((2 * (Real.pi : ℂ)) * (((1 / (2 * Real.pi) : ℝ) : ℂ))) *
            ((Complex.exp ((α : ℂ) * Complex.I / 4) *
              Complex.exp (-((α : ℂ) * Complex.I / 4))) *
              (2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
                completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))) := by ring
      _ = 1 * (1 * (2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
            completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)))) := by
          rw [hcpi', hexp1']
      _ = 2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
            completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by ring
  have hstep : (2 * (Real.pi : ℂ) * Complex.exp ((α : ℂ) * Complex.I / 4)) *
      (jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1 -
        Complex.exp (-((α : ℂ) * Complex.I / 2))) =
      2 * (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
        completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) := by
    rw [← hide]
    exact (congrArg (fun z => (2 * (Real.pi : ℂ) * Complex.exp ((α : ℂ) * Complex.I / 4)) * z) hP1).symm
  -- conclude the value of the integral
  have hIt : (∫ y : ℝ, Complex.exp ((α : ℂ) * (y : ℂ)) *
        completedRiemannZeta ((1/2 : ℂ) + ((2 * y : ℝ) : ℂ) * Complex.I)) =
      (Real.pi : ℂ) * Complex.exp ((α : ℂ) * Complex.I / 4) *
        (jacobiTheta (Complex.I * Complex.exp ((α : ℂ) * Complex.I)) - 1 -
          Complex.exp (-((α : ℂ) * Complex.I / 2))) := by
    linear_combination (1/2) * hstep.symm
  rw [hardy_unshifted_theta540 α hα, hIt]
  linear_combination (Real.pi : ℂ) * hexp3

/-- LEAF Hardy 1914 page 1012 display 1 and page 1013 display 2.
Shift the completed zeta contour from real part one to one quarter.
The residue at one half gives pi cosine. Pair the two critical line half rays.
Uniform horizontal bounds for every intermediate real part remain required. -/
theorem hardy_shifted_contour540 (α : ℝ) (hα : |α| < Real.pi / 2) :
    (Complex.exp ((α : ℂ) * I / 4) * hardyUnshifted540 α).re =
      Real.pi * Real.cos (α / 4) - 2 * expMoment540 hardyAmplitude540 0 α := by
  exact leaf2_of_shift_540 α hα (hshift_540 α hα)

/-- Hardy 1914 page 1012 display 1, auxiliary obstruction to absolute termwise Mellin integration.
The critical line Gaussian power series has exponent one half and is not summable.
This is a bound obstruction and is not a question about the paper. -/
theorem not_summable_theta_half_power540 :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
  have he : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) =
      (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 / 2 : ℝ)) := by
    ext n
    rw [abs_of_nonneg (by positivity)]
  rw [he, Real.summable_one_div_nat_add_rpow]
  norm_num

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_raw_bounds540 :
    ((fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ)))) ∧
    ((fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))) := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hk (x : ℝ) : (HurwitzZeta.evenKernel 0 x : ℂ) = jacobiTheta (I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  have he : (fun x : ℝ => P.f x - P.f₀) = (fun x : ℝ => jacobiTheta (I * (x : ℂ)) - 1) := by
    ext x
    simp [P, HurwitzZeta.hurwitzEvenFEPair, hk]
  constructor
  · rw [← he]
    exact P.hf_top (-2)
  · rw [← he]
    exact P.hf_zero'

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_euler_top540 :
    (fun x : ℝ => (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
  let C : ℝ := 2 / (1 - Real.exp (-Real.pi / 2))
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi / 2 < 0)
    linarith
  have hlim : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-Real.pi * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℕ) Real.pi Real.pi_pos
  have he : ∀ᶠ x : ℝ in atTop, x ^ 3 * Real.exp (-Real.pi * x) ≤ 1 :=
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono fun x hx => hx.le
  have hd : deriv (fun w : ℂ => jacobiTheta (I * w) - 1) =
      deriv (fun w : ℂ => jacobiTheta (I * w)) := by
    ext w
    exact deriv_sub_const 1
  refine Asymptotics.isBigO_iff.mpr ⟨2 * C * Real.exp (Real.pi / 2), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with x hx hex
  have hxp : 0 < x := by linarith
  have hb := theta_cauchy_bound540 1 (x : ℂ) hx
  rw [iteratedDeriv_one, hd] at hb
  norm_num at hb
  have hbound : ‖deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ)‖ ≤
      2 * C * Real.exp (-Real.pi * (x - 1 / 2)) := by dsimp [C]; convert hb using 1 <;> ring
  have hfin : x * Real.exp (-Real.pi * x) ≤ x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two, ← one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).mpr
    nlinarith [hex]
  calc
    _ = x * ‖deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]
    _ ≤ x * (2 * C * Real.exp (-Real.pi * (x - 1 / 2))) :=
      mul_le_mul_of_nonneg_left hbound hxp.le
    _ = (2 * C * Real.exp (Real.pi / 2)) * (x * Real.exp (-Real.pi * x)) := by
      rw [show -Real.pi * (x - 1 / 2) = Real.pi / 2 + -Real.pi * x by ring, Real.exp_add]
      ring
    _ ≤ (2 * C * Real.exp (Real.pi / 2)) * x ^ (-(2 : ℝ)) := by gcongr
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_euler_zero540 :
    (fun x : ℝ => (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Cf, hCf, hf⟩ := Asymptotics.isBigO_iff'.mp theta_raw_bounds540.1
  obtain ⟨Cd, hCd, hd⟩ := Asymptotics.isBigO_iff'.mp theta_euler_top540
  have hfi := tendsto_inv_nhdsGT_zero.eventually hf
  have hdi := tendsto_inv_nhdsGT_zero.eventually hd
  have hy := tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop (1 : ℝ))
  refine Asymptotics.isBigO_iff.mpr ⟨(Cf + 1) / 2 + Cd, ?_⟩
  filter_upwards [hfi, hdi, hy, self_mem_nhdsWithin] with x hfx hdx hyx hx
  have hxp : 0 < x := hx
  have hp : (x⁻¹) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hyx (by norm_num)
  have hpn : ‖(x⁻¹) ^ (-(2 : ℝ))‖ ≤ 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hxp.le) _)]
  have hfb : ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1‖ ≤ Cf := by
    simpa only [mul_one] using hfx.trans (mul_le_mul_of_nonneg_left hpn hCf.le)
  have hdb : ‖((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)‖ ≤ Cd := by
    simpa only [mul_one] using hdx.trans (mul_le_mul_of_nonneg_left hpn hCd.le)
  have htheta : ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))‖ ≤ Cf + 1 := by
    calc
      _ = ‖(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by simpa using add_le_add_right hfb 1
  have hform : (x : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) (x : ℂ) =
      (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) *
        (-(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))) / 2 -
          ((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)) := by
    rw [(hasDerivAt_theta_modular540 (x : ℂ) hxp).deriv]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hxp.ne'] <;> ring
  have hrest : ‖-(jacobiTheta (I * ((x⁻¹ : ℝ) : ℂ))) / 2 -
      ((x⁻¹ : ℝ) : ℂ) * deriv (fun w : ℂ => jacobiTheta (I * w)) ((x⁻¹ : ℝ) : ℂ)‖ ≤ (Cf + 1) / 2 + Cd := by
    apply (norm_sub_le _ _).trans
    rw [norm_div, norm_neg]
    norm_num only [Complex.norm_ofNat]
    exact add_le_add (div_le_div_of_nonneg_right htheta (by norm_num)) hdb
  rw [hform, norm_mul, Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hxp, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
  simpa only [neg_div, mul_comm] using
    mul_le_mul_of_nonneg_left hrest (Real.rpow_nonneg hxp.le (-1 / 2))

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_weighted_boundary540 (f : ℝ → ℂ)
    (htop : f =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))))
    (hzero : f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1 / 2 : ℝ))))
    (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 2) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) (𝓝[>] 0) (𝓝 0) := by
  have general (l : Filter ℝ) (r : ℝ) (hpos : ∀ᶠ x : ℝ in l, 0 < x)
      (hf : f =O[l] (fun x : ℝ => x ^ r))
      (hr : Tendsto (fun x : ℝ => x ^ (w.re + r)) l (𝓝 0)) :
      Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) l (𝓝 0) := by
    obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp hf
    have he : ∀ᶠ x : ℝ in l, ‖(x : ℂ) ^ w * f x‖ ≤ C * x ^ (w.re + r) := by
      filter_upwards [hb, hpos] with x hx hxp
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      calc
        _ ≤ x ^ w.re * (C * ‖x ^ r‖) :=
          mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hxp.le _)
        _ = C * x ^ (w.re + r) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _), Real.rpow_add hxp]
          ring
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) he
        (by simpa only [mul_zero] using hr.const_mul C))
  constructor
  · apply general atTop (-2) (eventually_gt_atTop 0) htop
    rw [show w.re + -(2 : ℝ) = -(2 - w.re) by ring]
    exact tendsto_rpow_neg_atTop (show 0 < 2 - w.re by linarith)
  · apply general (𝓝[>] 0) (-(1 / 2)) self_mem_nhdsWithin hzero
    have hp : 0 < w.re + -(1 / 2 : ℝ) := by linarith
    have hh0 : Tendsto (fun x : ℝ => x ^ (w.re + -(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.zero_rpow hp.ne'] using (Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)
    exact hh0.mono_left nhdsWithin_le_nhds

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_kernel_mellin_right540 (w : ℂ) (hw1 : 1 / 2 < w.re) (hw2 : w.re < 2) :
    mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      2 * w * (w - 1 / 2) * completedRiemannZeta (2 * w) := by
  let T : ℂ → ℂ := fun z => jacobiTheta (I * z)
  let G : ℝ → ℂ := fun x => T (x : ℂ) - 1
  let E : ℝ → ℂ := fun x => (x : ℂ) * deriv T (x : ℂ)
  let E' : ℝ → ℂ := fun x => deriv T (x : ℂ) + (x : ℂ) * deriv (deriv T) (x : ℂ)
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw1; linarith
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hT : DifferentiableOn ℂ T {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_jacobiTheta (by simpa using hz)).comp z (by fun_prop)).differentiableWithinAt
  have hfG (x : ℝ) (hx : 0 < x) : HasDerivAt G (deriv T (x : ℂ)) x := by
    exact ((hT.differentiableAt (ho.mem_nhds hx)).hasDerivAt.sub_const 1).comp_ofReal
  have hfE (x : ℝ) (hx : 0 < x) : HasDerivAt E (E' x) x := by
    have hh := ((hasDerivAt_id (x : ℂ)).mul
      ((hT.deriv ho).differentiableAt (ho.mem_nhds hx)).hasDerivAt).comp_ofReal
    simpa only [E, E', Pi.mul_apply, id_eq, one_mul] using hh
  have hmG : MellinConvergent G w := mellinConvergent_of_isBigO_rpow
    ((continuousOn_of_forall_continuousAt fun x hx => (hfG x hx).continuousAt).locallyIntegrableOn measurableSet_Ioi)
    theta_raw_bounds540.1 hw2 theta_raw_bounds540.2 hw1
  have hmE : MellinConvergent E w := mellinConvergent_of_isBigO_rpow
    ((continuousOn_of_forall_continuousAt fun x hx => (hfE x hx).continuousAt).locallyIntegrableOn measurableSet_Ioi)
    theta_euler_top540 hw2 theta_euler_zero540 hw1
  have hangle : |(0 : ℝ)| < Real.pi / 2 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 2)
  have hcK : ContinuousOn (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa using continuousOn_theta_ray540 0 hangle
  have htK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    simpa using theta_ray_top540 0 hangle
  have hzK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    simpa using theta_ray_zero540 0 hangle
  have hmK : MellinConvergent (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w :=
    mellinConvergent_of_isBigO_rpow (hcK.locallyIntegrableOn measurableSet_Ioi) htK hw2 hzK (by linarith)
  have hiK : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hmK
  have hiE : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * E x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hmE
  have hiD : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((x : ℂ) * E' x)) (Ioi 0) := by
    apply (hiK.sub (hiE.const_mul (1 / 2 : ℂ))).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only [E, E', T, thetaMellinKernel540]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply, Pi.mul_apply]
    ring
  have hmD : MellinConvergent (fun x : ℝ => (x : ℂ) * E' x) w := by
    simpa only [MellinConvergent, smul_eq_mul] using hiD
  have hBG := theta_weighted_boundary540 G theta_raw_bounds540.1 theta_raw_bounds540.2 w hw1 hw2
  have hBE := theta_weighted_boundary540 E theta_euler_top540 theta_euler_zero540 w hw1 hw2
  have hP0 := mellin_euler_derivative540 G (fun x : ℝ => deriv T (x : ℂ)) w hw0 hfG hmG hmE hBG.2 hBG.1
  have hP1 := mellin_euler_derivative540 E E' w hw0 hfE hmE hmD hBE.2 hBE.1
  have hlin : mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      mellin (fun x : ℝ => (x : ℂ) * E' x) w + (1 / 2 : ℂ) * mellin E w := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [← integral_const_mul, ← integral_add hiD (hiE.const_mul (1 / 2 : ℂ))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [E, E', T, thetaMellinKernel540]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply, Pi.mul_apply]
    ring
  have hM0 : completedRiemannZeta (2 * w) = mellin G w / 2 := completedZeta_theta_mellin540 w hw1
  rw [hlin, hP1, hP0, hM0]
  ring

/-- Hardy 1914 page 1012 display 1, auxiliary theta Mellin endpoint and continuation identity. -/
theorem theta_kernel_mellin_strip540 (w : ℂ) (hw0 : -1 < w.re) (hw2 : w.re < 2) :
    mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w =
      2 * w * (w - 1 / 2) * completedRiemannZeta₀ (2 * w) + 1 / 2 := by
  let U : Set ℂ := {z | -1 < z.re ∧ z.re < 2}
  let M : ℂ → ℂ := mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ))
  let F : ℂ → ℂ := fun z => 2 * z * (z - 1 / 2) * completedRiemannZeta₀ (2 * z) + 1 / 2
  have hangle : |(0 : ℝ)| < Real.pi / 2 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 2)
  have hcK : ContinuousOn (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) (Ioi 0) := by
    simpa using continuousOn_theta_ray540 0 hangle
  have htK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    simpa using theta_ray_top540 0 hangle
  have hzK : (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    simpa using theta_ray_zero540 0 hangle
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hcv : Convex ℝ U := (convex_Ioo (-1 : ℝ) 2).linear_preimage Complex.reCLM.toLinearMap
  have hM : DifferentiableOn ℂ M U := by
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow
      (hcK.locallyIntegrableOn measurableSet_Ioi) htK hz.2 hzK hz.1).differentiableWithinAt
  have hcomp : Differentiable ℂ (fun z : ℂ => completedRiemannZeta₀ (2 * z)) :=
    differentiable_completedZeta₀.comp (by fun_prop)
  have hF : Differentiable ℂ F := by
    dsimp [F]
    fun_prop
  have hright (z : ℂ) (hz1 : 1 / 2 < z.re) (hz2 : z.re < 2) : M z = F z := by
    have hs0 : 2 * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    have hs1 : 1 - 2 * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    change mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) z = _
    rw [theta_kernel_mellin_right540 z hz1 hz2, completedRiemannZeta_eq]
    dsimp [F]
    have hz0 : z ≠ 0 := by intro h; simp [h] at hs0
    field_simp [hs0, hs1, hz0] <;> ring
  have hnear : M =ᶠ[𝓝 (1 : ℂ)] F := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re),
      (isOpen_lt continuous_re continuous_const).mem_nhds
        (by norm_num : (1 : ℂ).re < (2 : ℝ))] with z hz1 hz2
    exact hright z hz1 hz2
  exact (hM.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hF.differentiableOn.analyticOnNhd hU) hcv.isPreconnected (show (1 : ℂ) ∈ U by norm_num [U]) hnear ⟨hw0, hw2⟩

/-- Hardy 1914 page 1012 display 1, the corrected theta Mellin representation of Xi.
Two integrations by parts and analytic uniqueness prove the critical exponent identity. -/
theorem theta_xi_mellin540 (t : ℝ) :
    (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
      thetaMellinKernel540 (x : ℂ) := by
  let w : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  have hm := theta_kernel_mellin_strip540 w (by norm_num [w]) (by norm_num [w])
  have hw0 : w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [w] at hh
  have hw1 : 1 - 2 * w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [w] at hh
  have hs : (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I = 2 * w := by
    dsimp [w]
    push_cast
    ring
  have hp : (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) = 2 * w * (w - 1 / 2) := by
    dsimp [w]
    push_cast
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [hs, hp]
  calc
    _ = 2 * w * (w - 1 / 2) * completedRiemannZeta₀ (2 * w) + 1 / 2 := by
      rw [completedRiemannZeta_eq]
      field_simp [hw0, hw1] <;> ring
    _ = mellin (fun x : ℝ => thetaMellinKernel540 (x : ℂ)) w := hm.symm
    _ = _ := rfl


/-- Hardy 1914 page 1012 display 1, proved exponential decay from the theta Mellin sector. -/
theorem theta_xi_decay540 (φ t : ℝ) (hφ : |φ| < Real.pi / 2) :
    ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤
    Real.exp (-φ * t) *
      ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
        ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖ := by
  rw [theta_xi_mellin540, theta_mellin_rotate540 φ t hφ, norm_mul,
    mellin_ray_phase_norm540]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ ((1 / 4 : ℂ) + (t : ℂ) * I - 1) *
          thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, mellin_ray_power_norm540 x t hx]

/-- Hardy 1914 page 1012 display 1, proved exponential decay from the theta Mellin sector. -/
theorem hardyAmplitude_decay540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |hardyAmplitude540 t| ≤ C * Real.exp (-φ * t) := by
  let A : ℝ := ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
    ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖
  have hA : 0 ≤ A := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)
  refine ⟨4 * (A + 1), by linarith, ?_⟩
  intro t ht
  let L : ℂ := completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)
  have hD : (1 / 8 : ℝ) * ‖L‖ ≤ ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) * L‖ := by
    rw [norm_mul]
    have hnorm : ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ)‖ =
        ((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 := by
      norm_cast
      rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [sq_nonneg (2 * t)])]
      ring
    rw [hnorm]
    nlinarith [sq_nonneg (2 * t), norm_nonneg L]
  have hreal : |hardyAmplitude540 t| ≤ (1 / 2 : ℝ) * ‖L‖ := by
    change |-(1 / 2 : ℝ) * L.re| ≤ _
    calc
      _ = (1 / 2 : ℝ) * |L.re| := by rw [abs_mul]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm L) (by norm_num)
  have hd := theta_xi_decay540 φ t hφ
  change ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) * L‖ ≤ Real.exp (-φ * t) * A at hd
  have he : 0 < Real.exp (-φ * t) := Real.exp_pos _
  nlinarith

/-- Hardy 1914 page 1012 display 1, proved exponential decay from the theta Mellin sector. -/
theorem hardyXi_decay540 (φ : ℝ) (hφ : |φ| < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |hardyXi515 (2 * t)| ≤ C * Real.exp (-φ * t) := by
  let A : ℝ := ∫ x : ℝ in Ioi 0, x ^ (-3 / 4 : ℝ) *
    ‖thetaMellinKernel540 ((x : ℂ) * Complex.exp ((φ : ℂ) * I))‖
  have hA : 0 ≤ A := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)
  refine ⟨A + 1, by linarith, ?_⟩
  intro t ht
  have hp : (((-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℝ)) : ℂ) =
      (-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) := by push_cast; rfl
  have hr : |hardyXi515 (2 * t)| ≤ ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
      completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ := by
    rw [hardyXi515, abs_mul, norm_mul, ← hp, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
  have hd := theta_xi_decay540 φ t hφ
  change ‖(-((1 / 4 : ℝ) + (2 * t) ^ 2) / 2 : ℂ) *
    completedRiemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ Real.exp (-φ * t) * A at hd
  have he := Real.exp_pos (-φ * t)
  exact hr.trans (hd.trans (by nlinarith))

end LeanLab.BhowmikGrimmelt2026
