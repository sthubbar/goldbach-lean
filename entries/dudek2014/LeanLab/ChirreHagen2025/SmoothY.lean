module

public import Mathlib
public import LeanLab.ChirreHagen2025.SmoothKernel

/-!
P0075 line, T2, unit U-6354, I-5170, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
SmoothKernel.lean in the paper's own variable: for finitely many ordinates `γ_i` and
coefficients `c_i`, with `P(y) = Σ_i c_i y^{1/2 + iγ_i}` and the weight
`W(u) = 1` for `u ≤ 1`, `u^-4` for `u > 1`,
`∫_0^∞ |P(y)|² W(y/x) dy = x² ∫_ℝ |Σ_i c_i x^{iγ_i} e^{iγ_i v}|² e^{-2|v|} dv`
by `y = x e^v`, hence `∫_1^x |P(y)|² dy ≤ x² Σ_i |c_i|² Σ_j 4/(4 + (γ_i - γ_j)²)`.
This is the finite form of steps (a) to (c) of I-5170, with `P = -A_δ` truncated to finitely
many zeros on the critical line. The passage to all zeros stays cited.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.SmoothKernel
open Complex MeasureTheory Set

/-- The weight `W(u) = min(1, u^-4)` on `u > 0`. -/
noncomputable def W (u : ℝ) : ℝ := if u ≤ 1 then 1 else (u ^ 4)⁻¹

theorem W_nonneg (u : ℝ) : 0 ≤ W u := by
  unfold W; split_ifs
  · norm_num
  · have : 0 < u := by linarith
    positivity

theorem exp_W (v : ℝ) : Real.exp v * Real.exp v * W (Real.exp v) = w v := by
  unfold W w
  split_ifs with h
  · have hv : v ≤ 0 := Real.exp_le_one_iff.mp h
    rw [abs_of_nonpos hv, mul_one, ← Real.exp_add]; congr 1; ring
  · have hv : 0 < v := Real.one_lt_exp_iff.mp (lt_of_not_ge h)
    rw [abs_of_pos hv, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1; push_cast; ring

/-- `P(y) = Σ_i c_i y^{1/2 + iγ_i}`. -/
noncomputable def P {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) (y : ℝ) : ℂ :=
  ∑ i ∈ s, c i * (y : ℂ) ^ ((1 / 2 : ℂ) + (γ i : ℂ) * I)

/-- The rotated coefficients `c_i x^{iγ_i}`. -/
noncomputable def cx {ι : Type*} (c : ι → ℂ) (γ : ι → ℝ) (x : ℝ) (i : ι) : ℂ :=
  c i * (x : ℂ) ^ ((γ i : ℂ) * I)

theorem norm_cx {ι : Type*} (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ} (hx : 0 < x) (i : ι) :
    ‖cx c γ x i‖ = ‖c i‖ := by
  unfold cx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem normSq_P_exp {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ} (hx : 0 < x)
    (v : ℝ) :
    ‖P s c γ (x * Real.exp v)‖ ^ 2 = x * Real.exp v * ‖F s (cx c γ x) γ v‖ ^ 2 := by
  set r := x * Real.exp v with hr
  have hr0 : 0 < r := by positivity
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  have e1 : ∀ i, (r : ℂ) ^ ((γ i : ℂ) * I)
      = (x : ℂ) ^ ((γ i : ℂ) * I) * Complex.exp ((γ i : ℂ) * v * I) := by
    intro i
    rw [hr, ofReal_mul, mul_cpow_ofReal_nonneg hx.le (Real.exp_pos v).le]
    congr 1
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
      ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
    congr 1; ring
  have key : P s c γ r = (r : ℂ) ^ (1 / 2 : ℂ) * F s (cx c γ x) γ v := by
    unfold P F cx
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cpow_add _ _ hrC, e1]; ring
  rw [key, norm_mul, mul_pow, norm_cpow_eq_rpow_re_of_pos hr0]
  have : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  rw [this, ← Real.sqrt_eq_rpow, Real.sq_sqrt hr0.le]

theorem continuous_F {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    Continuous (F s a γ) := by
  unfold F; fun_prop

theorem continuous_w : Continuous w := by unfold w; fun_prop

theorem integrable_Fw {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    Integrable (fun v => ‖F s a γ v‖ ^ 2 * w v) := by
  set B := ∑ i ∈ s, ‖a i‖
  have hb : ∀ v, ‖F s a γ v‖ ≤ B := by
    intro v; unfold F
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_exp]; simp
  refine (integrable_w.const_mul (B ^ 2)).mono'
    (((continuous_F s a γ).norm.pow 2).mul continuous_w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have hw : 0 ≤ w v := by unfold w; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := pow_le_pow_left₀ (norm_nonneg _) (hb v) 2
  nlinarith

/-- The substitution `y = x e^v`. -/
theorem integral_P_W {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * W (y / x)
      = x ^ 2 * ∫ v, ‖F s (cx c γ x) γ v‖ ^ 2 * w v := by
  have h1 := integral_comp_mul_left_Ioi (fun y => ‖P s c γ y‖ ^ 2 * W (y / x)) 0 hx
  rw [mul_zero] at h1
  have h2 := integral_comp_exp (fun u => ‖P s c γ (x * u)‖ ^ 2 * W (x * u / x))
  rw [← h2, smul_eq_mul] at h1
  have e : (fun v => Real.exp v • (‖P s c γ (x * Real.exp v)‖ ^ 2 * W (x * Real.exp v / x)))
      = fun v => x * (‖F s (cx c γ x) γ v‖ ^ 2 * w v) := by
    funext v
    rw [smul_eq_mul, normSq_P_exp s c γ hx, mul_div_cancel_left₀ _ hx.ne', ← exp_W v]
    ring
  rw [e, integral_const_mul] at h1
  have : ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * W (y / x)
      = x * (x⁻¹ * ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * W (y / x)) := by
    field_simp
  rw [this, ← h1]; ring

theorem integrableOn_P_W {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 0 < x) : IntegrableOn (fun y => ‖P s c γ y‖ ^ 2 * W (y / x)) (Ioi 0) := by
  have hF := (integrable_Fw s (cx c γ x) γ).const_mul x
  have e : (fun v => x * (‖F s (cx c γ x) γ v‖ ^ 2 * w v))
      = fun v => Real.exp v • (‖P s c γ (x * Real.exp v)‖ ^ 2 * W (x * Real.exp v / x)) := by
    funext v
    rw [smul_eq_mul, normSq_P_exp s c γ hx, mul_div_cancel_left₀ _ hx.ne', ← exp_W v]
    ring
  rw [e, integrable_comp_exp (fun u => ‖P s c γ (x * u)‖ ^ 2 * W (x * u / x))] at hF
  have := (integrableOn_Ioi_comp_mul_left_iff (fun y => ‖P s c γ y‖ ^ 2 * W (y / x)) 0 hx).mp hF
  rwa [mul_zero] at this

/-- The smoothed mean square for finitely many critical line terms:
`∫_0^∞ |P(y)|² W(y/x) dy ≤ x² Σ_i |c_i|² Σ_j 4/(4 + (γ_i - γ_j)²)`. -/
theorem integral_P_W_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 0 < x) :
    ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * W (y / x)
      ≤ x ^ 2 * ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j) := by
  rw [integral_P_W s c γ hx]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := integral_normSq_le s (cx c γ x) γ
  simpa [norm_cx c γ hx] using this

/-- Step (a) of I-5170 in finite form: `∫_1^x |P(y)|² dy ≤ x² Σ_i |c_i|² Σ_j K(γ_i - γ_j)`. -/
theorem interval_P_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 1 ≤ x) :
    ∫ y in (1 : ℝ)..x, ‖P s c γ y‖ ^ 2
      ≤ x ^ 2 * ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j) := by
  have hx0 : 0 < x := by linarith
  refine le_trans ?_ (integral_P_W_le s c γ hx0)
  rw [intervalIntegral.integral_of_le hx]
  have hsub : Ioc 1 x ⊆ Ioi (0 : ℝ) := fun y hy => lt_trans one_pos hy.1
  have hI := integrableOn_P_W s c γ hx0
  calc ∫ y in Ioc 1 x, ‖P s c γ y‖ ^ 2
      = ∫ y in Ioc 1 x, ‖P s c γ y‖ ^ 2 * W (y / x) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
        have : y / x ≤ 1 := (div_le_one hx0).mpr hy.2
        simp [W, this]
    _ ≤ ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * W (y / x) :=
        setIntegral_mono_set hI
          (Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (W_nonneg _))
          (Filter.Eventually.of_forall hsub)

end LeanLab.ChirreHagen2025.SmoothKernel

