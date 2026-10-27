module

public import Mathlib

/-!
P0075 line, T2, unit U-6353, I-5170, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
The finite core of the smoothed mean square: with the positive definite weight `e^{-2|v|}`,
whose Fourier transform is `4/(4 + t²)`,
`∫_ℝ |Σ_i a_i e^{i γ_i v}|² e^{-2|v|} dv ≤ Σ_i |a_i|² Σ_j 4/(4 + (γ_i - γ_j)²)`.
After `y = x e^v`, this is step (b) and (c) of I-5170 for finitely many zeros: the weight
`W(u) = min(1, u^-4)` gives `G(v) = e^{2v} W(e^v) = e^{-2|v|}`. The passage to all zeros,
the explicit formula and the zero sums stay cited, as in the paper.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.SmoothKernel
open Complex MeasureTheory Set

/-- The kernel `4/(4 + t²)`. -/
noncomputable def K (t : ℝ) : ℝ := 4 / (4 + t ^ 2)

theorem K_nonneg (t : ℝ) : 0 ≤ K t := by unfold K; positivity

theorem K_symm (s t : ℝ) : K (s - t) = K (t - s) := by
  unfold K; congr 1; ring

/-- `e^{-2|v|} e^{itv}`. -/
noncomputable def g (t v : ℝ) : ℂ := Complex.exp (((-2 * |v| : ℝ) : ℂ) + (t : ℂ) * v * I)

theorem g_Iic {t v : ℝ} (hv : v ≤ 0) : g t v = Complex.exp ((2 + t * I) * v) := by
  unfold g; congr 1; rw [abs_of_nonpos hv]; push_cast; ring

theorem g_Ioi {t v : ℝ} (hv : 0 < v) : g t v = Complex.exp ((-2 + t * I) * v) := by
  unfold g; congr 1; rw [abs_of_pos hv]; push_cast; ring

theorem int_Iic (t : ℝ) : IntegrableOn (g t) (Iic 0) := by
  have h := integrableOn_exp_mul_complex_Iic (a := 2 + t * I) (by simp) 0
  refine h.congr_fun (fun v hv => (g_Iic hv).symm) measurableSet_Iic

theorem int_Ioi (t : ℝ) : IntegrableOn (g t) (Ioi 0) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := -2 + t * I) (by simp) 0
  refine h.congr_fun (fun v hv => (g_Ioi hv).symm) measurableSet_Ioi

theorem integrable_g (t : ℝ) : Integrable (g t) := by
  have := (int_Iic t).union (int_Ioi t)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- The Fourier transform of `e^{-2|v|}`: `∫ e^{-2|v|} e^{itv} dv = 4/(4 + t²)`. -/
theorem integral_g (t : ℝ) : ∫ v, g t v = (K t : ℂ) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (int_Iic t) (int_Ioi t)]
  rw [setIntegral_congr_fun measurableSet_Iic (fun v hv => g_Iic hv),
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => g_Ioi hv)]
  rw [integral_exp_mul_complex_Iic (by simp), integral_exp_mul_complex_Ioi (by simp)]
  have h1 : (2 + (t : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : (-2 + (t : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h4 : ((4 : ℂ) + (t : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 4 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  unfold K
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `e^{-2|v|}` as a real function. -/
noncomputable def w (v : ℝ) : ℝ := Real.exp (-2 * |v|)

theorem w_eq (v : ℝ) : (w v : ℂ) = g 0 v := by
  unfold w g; push_cast; simp

theorem integrable_w : Integrable w := by
  have h := (integrable_g 0).norm
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  show ‖g 0 v‖ = w v
  rw [← w_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by unfold w; positivity)]

/-- The trigonometric sum `F(v) = Σ_i a_i e^{i γ_i v}`. -/
noncomputable def F {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) (v : ℝ) : ℂ :=
  ∑ i ∈ s, a i * Complex.exp ((γ i : ℂ) * v * I)

theorem normSq_F {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) (v : ℝ) :
    ((‖F s a γ v‖ ^ 2 : ℝ) : ℂ) * (w v : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, a i * starRingEnd ℂ (a j) * g (γ i - γ j) v := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', w_eq]
  unfold F
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  unfold g
  have e : starRingEnd ℂ ((γ j : ℂ) * v * I) = -((γ j : ℂ) * v * I) := by
    simp [Complex.conj_ofReal]
  rw [e]
  have : Complex.exp ((γ i : ℂ) * v * I) * Complex.exp (-((γ j : ℂ) * v * I))
      * Complex.exp (((-2 * |v| : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * v * I)
      = Complex.exp (((-2 * |v| : ℝ) : ℂ) + ((γ i - γ j : ℝ) : ℂ) * v * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  calc a i * Complex.exp ((γ i : ℂ) * v * I) * (starRingEnd ℂ (a j) *
        Complex.exp (-((γ j : ℂ) * v * I))) *
        Complex.exp (((-2 * |v| : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * v * I)
      = a i * starRingEnd ℂ (a j) * (Complex.exp ((γ i : ℂ) * v * I) *
        Complex.exp (-((γ j : ℂ) * v * I)) *
        Complex.exp (((-2 * |v| : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * v * I)) := by ring
    _ = _ := by rw [this]

/-- The exact identity: `∫ |F|² e^{-2|v|} = Σ_{i,j} a_i conj(a_j) 4/(4 + (γ_i - γ_j)²)`. -/
theorem integral_normSq {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    (((∫ v, ‖F s a γ v‖ ^ 2 * w v : ℝ)) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ) := by
  rw [← integral_complex_ofReal]
  have e : (fun v => (((‖F s a γ v‖ ^ 2 * w v : ℝ)) : ℂ))
      = fun v => ∑ i ∈ s, ∑ j ∈ s, a i * starRingEnd ℂ (a j) * g (γ i - γ j) v := by
    funext v; push_cast; rw [← normSq_F]; push_cast; ring
  rw [e, integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integrable_g _).const_mul _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (integrable_g _).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_g]

/-- The diagonal bound: `∫ |F|² e^{-2|v|} ≤ Σ_i |a_i|² Σ_j 4/(4 + (γ_i - γ_j)²)`. -/
theorem integral_normSq_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    ∫ v, ‖F s a γ v‖ ^ 2 * w v
      ≤ ∑ i ∈ s, ‖a i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j) := by
  have h := integral_normSq s a γ
  set I := ∫ v, ‖F s a γ v‖ ^ 2 * w v
  have hre : I = (∑ i ∈ s, ∑ j ∈ s, a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ)).re := by
    rw [← h]; simp
  have step : ∀ i j, (a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ)).re
      ≤ (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 * K (γ i - γ j) := by
    intro i j
    have h1 : (a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ)).re
        ≤ ‖a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ)‖ := Complex.re_le_norm _
    have h2 : ‖a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ)‖
        = ‖a i‖ * ‖a j‖ * K (γ i - γ j) := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (K_nonneg _)]
    have h3 : ‖a i‖ * ‖a j‖ ≤ (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖a i‖ - ‖a j‖)]
    have h4 := mul_le_mul_of_nonneg_right h3 (K_nonneg (γ i - γ j))
    linarith
  rw [hre, Complex.re_sum]
  calc ∑ i ∈ s, (∑ j ∈ s, a i * starRingEnd ℂ (a j) * (K (γ i - γ j) : ℂ)).re
      ≤ ∑ i ∈ s, ∑ j ∈ s, (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 * K (γ i - γ j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Complex.re_sum]
        exact Finset.sum_le_sum fun j _ => step i j
    _ = ∑ i ∈ s, ‖a i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j) := by
        have e1 : ∑ i ∈ s, ∑ j ∈ s, (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 * K (γ i - γ j)
            = (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ ^ 2 * K (γ i - γ j)) / 2
              + (∑ i ∈ s, ∑ j ∈ s, ‖a j‖ ^ 2 * K (γ i - γ j)) / 2 := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        have e2 : ∑ i ∈ s, ∑ j ∈ s, ‖a j‖ ^ 2 * K (γ i - γ j)
            = ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ ^ 2 * K (γ i - γ j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [K_symm]
        rw [e1, e2]
        simp_rw [Finset.mul_sum]
        ring

end LeanLab.ChirreHagen2025.SmoothKernel

