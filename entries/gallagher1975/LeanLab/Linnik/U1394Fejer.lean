module

public import LeanLab.Linnik.LiLiuDisplay37

/-!
Li-Liu, arXiv 2610.15784 v1, Section 4, proof of Lemma 4.3, second line of display (37):
  ∫_{-T}^{T} |∫_0^1 e(ut) dt|² du = 1 + O(T^{-1}),
with the paper's justification "together with Plancherel's theorem" and the tail bound
  ∫_{|u|>T} |∫_0^1 e(ut) dt|² du ≤ ∫_{|u|>T} du/(π²u²) = 2/(π²T).

This file proves, for `I T` of LiLiuDisplay37.lean, unit U-1379:
* `fourier_tri`: the Fourier transform of the triangle max(0, 1 - |x|) is G 1 (2πw);
* `fej_eq_G`: |∫_0^1 e(ut) dt|² = G 1 (2πu), the Fejér kernel;
* `integral_fej`: ∫_ℝ |∫_0^1 e(ut) dt|² du = 1, by Mathlib's Fourier inversion at 0
  in place of Plancherel;
* `one_sub_I_le`: 0 ≤ 1 - I(T) ≤ 2/(π²T) for T > 0, the paper's tail bound with its constant;
* `tendsto_I`: I(T) → 1 as T → ∞.

Unit U-1394, PC run 20261021T1003Z-20044. AI-written Lean code, Claude. KNOWN mathematics, a
textbook Fejér kernel fact. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1394Fejer

open MeasureTheory Set Real Filter FourierTransform
open LeanLab.Linnik.LiLiuDisplay37
open LeanLab.PNTPort.LargeSieve

/-! ## The triangle and its Fourier transform -/

/-- The triangle `max(0, 1 - |x|)`. -/
noncomputable def tri (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma continuous_tri : Continuous tri := by unfold tri; fun_prop

lemma tri_eq_zero {x : ℝ} (h : 1 ≤ |x|) : tri x = 0 := by
  unfold tri; exact max_eq_left (by linarith)

lemma tri_eq {x : ℝ} (h : |x| ≤ 1) : tri x = 1 - |x| := by
  unfold tri; exact max_eq_right (by linarith)

lemma hasCompactSupport_tri : HasCompactSupport (fun x => (tri x : ℂ)) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1))
  intro x hx
  have : 1 ≤ |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [tri_eq_zero this]

lemma integrable_tri : Integrable (fun x => (tri x : ℂ)) :=
  (Complex.continuous_ofReal.comp continuous_tri).integrable_of_hasCompactSupport
    hasCompactSupport_tri

/-- The Fourier transform of the triangle is the Fejér weight `G 1 (2πw)`. -/
theorem fourier_tri (w : ℝ) : 𝓕 (fun x => (tri x : ℂ)) w = ((LiLiuDisplay37.G 1 (2 * π * w) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set h : ℝ → ℂ := fun v => Complex.exp (↑(-2 * π * v * w) * Complex.I) * ((1 - |v| : ℝ) : ℂ)
    with hh
  have step1 : (∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • (tri v : ℂ)) =
      ∫ v in (-1 : ℝ)..1, h v := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-1 : ℝ) 1)]
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      have : |v| ≤ 1 := abs_le.mpr ⟨hv.1.le, hv.2⟩
      simp only [smul_eq_mul, hh, tri_eq this]
    · intro v hv
      have : 1 ≤ |v| := by
        rw [mem_Ioc, not_and_or, not_lt, not_le] at hv
        rcases hv with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp [tri_eq_zero this]
  rw [step1]
  have hc : Continuous h := by rw [hh]; fun_prop
  have hsym : ∫ v in (-1 : ℝ)..1, h v = ∫ v in (-1 : ℝ)..1, h (-v) := by
    rw [intervalIntegral.integral_comp_neg]; simp
  have hpt : ∀ v : ℝ, h v + h (-v) =
      2 * (((1 - |v| / 1) * Real.cos (2 * π * w * v) : ℝ) : ℂ) := by
    intro v
    simp only [hh, abs_neg, div_one]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [show -(2 : ℂ) * π * -v * w = -(-2 * π * v * w) by ring, Complex.cos_neg, Complex.sin_neg,
      show -(2 : ℂ) * π * v * w = -(2 * π * w * v) by ring, Complex.cos_neg]
    ring
  have hc' : Continuous (fun v => h (-v)) := hc.comp continuous_neg
  have key : 2 * (∫ v in (-1 : ℝ)..1, h v) = 2 * ((LiLiuDisplay37.G 1 (2 * π * w) : ℝ) : ℂ) := by
    rw [two_mul]
    nth_rewrite 2 [hsym]
    rw [← intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hc'.intervalIntegrable _ _)]
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    rfl
  exact mul_left_cancel₀ two_ne_zero key

/-! ## The Fejér kernel `|∫_0^1 e(ut) dt|²` -/

/-- `fej u = |∫_0^1 e(ut) dt|²`, the integrand of `I T`. -/
noncomputable def fej (u : ℝ) : ℝ := ‖∫ t in (0 : ℝ)..1, e (u * t)‖ ^ 2

lemma I_eq (T : ℝ) : I T = ∫ u in (-T)..T, fej u := rfl

lemma continuous_e' : Continuous e := by unfold e; fun_prop

lemma continuous_fej : Continuous fej := by
  unfold fej
  apply Continuous.pow
  apply Continuous.norm
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_e'.comp (by fun_prop)

lemma fej_le_one (u : ℝ) : fej u ≤ 1 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => e (u * t)) (C := 1) (fun t _ => le_of_eq (norm_e _))
  have h0 : 0 ≤ ‖∫ t in (0 : ℝ)..1, e (u * t)‖ := norm_nonneg _
  have h1 : ‖∫ t in (0 : ℝ)..1, e (u * t)‖ ≤ 1 := by simpa using this
  unfold fej; nlinarith

lemma fej_nonneg (u : ℝ) : 0 ≤ fej u := by unfold fej; positivity

/-- For `u ≠ 0`, `|∫_0^1 e(ut) dt|² = sin²(πu)/(πu)²`. -/
lemma fej_ne {u : ℝ} (hu : u ≠ 0) : fej u = Real.sin (π * u) ^ 2 / (π * u) ^ 2 := by
  have hc : (2 * π * u : ℂ) * Complex.I ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    simp_all
  have hint : ∫ t in (0 : ℝ)..1, e (u * t) =
      (Complex.exp (Complex.I * ((2 * π * u : ℝ) : ℂ)) - 1) / ((2 * π * u : ℂ) * Complex.I) := by
    have : (fun t : ℝ => e (u * t)) = fun t : ℝ => Complex.exp ((2 * π * u : ℂ) * Complex.I * t) := by
      funext t; unfold e; push_cast; ring_nf
    rw [this, integral_exp_mul_complex hc]
    push_cast
    simp only [mul_zero, mul_one, Complex.exp_zero]
    ring_nf
  unfold fej
  rw [hint, norm_div, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hn : ‖(2 * π * u : ℂ) * Complex.I‖ = 2 * π * |u| := by
    rw [norm_mul, Complex.norm_I, mul_one]
    rw [show (2 * π * u : ℂ) = ((2 * π * u : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  rw [hn, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs,
    mul_pow, sq_abs]
  rw [show 2 * π * u / 2 = π * u by ring]
  have hp : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- `|∫_0^1 e(ut) dt|² = G 1 (2πu)`. -/
theorem fej_eq_G (u : ℝ) : fej u = LiLiuDisplay37.G 1 (2 * π * u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [mul_zero, LiLiuDisplay37.G_zero one_pos]
    unfold fej
    simp [e]
  · have hc : 2 * π * u ≠ 0 := by positivity
    rw [fej_ne hu, LiLiuDisplay37.G_eq one_pos hc, mul_one, show 2 * π * u = 2 * (π * u) by ring,
      Real.cos_two_mul, Real.cos_sq']
    have : π * u ≠ 0 := by positivity
    field_simp
    ring

lemma fej_mul_sq_le (u : ℝ) : fej u * u ^ 2 ≤ 1 / π ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp; positivity
  · rw [fej_ne hu, mul_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := Real.sin_sq_le_one (π * u)
    have : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith [sq_nonneg π, sq_nonneg u, mul_nonneg (sq_nonneg π) (sq_nonneg u)]

lemma fej_le_inv_sq {u : ℝ} (hu : u ≠ 0) : fej u ≤ (π ^ 2)⁻¹ * (u ^ 2)⁻¹ := by
  have h := fej_mul_sq_le u
  have hu2 : 0 < u ^ 2 := by positivity
  have hp : 0 < π ^ 2 := by positivity
  rw [← mul_inv, ← one_div, le_div_iff₀ (by positivity)]
  calc fej u * (π ^ 2 * u ^ 2) = π ^ 2 * (fej u * u ^ 2) := by ring
    _ ≤ π ^ 2 * (1 / π ^ 2) := mul_le_mul_of_nonneg_left h hp.le
    _ = 1 := by field_simp

/-- `fej u ≤ 2 (1 + u²)⁻¹`. -/
lemma fej_le_two_div (u : ℝ) : fej u ≤ 2 * (1 + u ^ 2)⁻¹ := by
  have h1 := fej_le_one u
  have h2 := fej_mul_sq_le u
  have hpi : 1 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith

lemma integrable_fej : Integrable fej := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono' continuous_fej.aestronglyMeasurable ?_
  refine Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (fej_nonneg u)]
  exact fej_le_two_div u

/-! ## `∫_ℝ fej = 1` by Fourier inversion at 0 -/

theorem integral_fej : ∫ u, fej u = 1 := by
  have hF : 𝓕 (fun x => (tri x : ℂ)) = fun w => ((fej w : ℝ) : ℂ) := by
    funext w; rw [fourier_tri, fej_eq_G]
  have hFi : Integrable (𝓕 (fun x => (tri x : ℂ))) := by
    rw [hF]; exact integrable_fej.ofReal
  have hinv := integrable_tri.fourierInv_fourier_eq hFi
    ((Complex.continuous_ofReal.comp continuous_tri).continuousAt (x := (0 : ℝ)))
  rw [fourierInv_eq, hF] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at hinv
  rw [integral_complex_ofReal] at hinv
  have h0 : tri 0 = 1 := by simp [tri]
  rw [h0] at hinv
  exact_mod_cast hinv

/-! ## The tail bound `1 - I(T) ≤ 2/(π²T)` -/

lemma integral_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ u in Ioi T, (π ^ 2)⁻¹ * (u ^ 2)⁻¹ = (π ^ 2)⁻¹ * T⁻¹ := by
  rw [integral_const_mul]
  congr 1
  have := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at this
  rw [← setIntegral_congr_fun measurableSet_Ioi (f := fun u : ℝ => u ^ (-2 : ℝ))]
  · rw [this]; ring
  · intro u hu
    simp only
    rw [Real.rpow_neg (le_of_lt (lt_trans hT hu)), Real.rpow_two]

lemma integrableOn_inv_sq {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun u : ℝ => (π ^ 2)⁻¹ * (u ^ 2)⁻¹) (Ioi T) := by
  apply Integrable.const_mul
  have := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT
  refine this.congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp only
  rw [Real.rpow_neg (le_of_lt (lt_trans hT hu)), Real.rpow_two]

lemma tail_le {T : ℝ} (hT : 0 < T) : ∫ u in Ioi T, fej u ≤ (π ^ 2)⁻¹ * T⁻¹ := by
  rw [← integral_Ioi_inv_sq hT]
  apply setIntegral_mono_on integrable_fej.integrableOn (integrableOn_inv_sq hT) measurableSet_Ioi
  intro u hu
  exact fej_le_inv_sq (ne_of_gt (lt_trans hT hu))

lemma fej_neg (u : ℝ) : fej (-u) = fej u := by
  rw [fej_eq_G, fej_eq_G]
  unfold LiLiuDisplay37.G
  apply intervalIntegral.integral_congr
  intro β _
  simp only
  rw [show 2 * π * -u * β = -(2 * π * u * β) by ring, Real.cos_neg]

lemma tail_eq : ∀ T : ℝ, ∫ u in Iic (-T), fej u = ∫ u in Ioi T, fej u := by
  intro T
  have := integral_comp_neg_Iic (-T) fej
  simp only [fej_neg, neg_neg] at this
  exact this

/-- **The tail split.** `1 - I(T) = ∫_{u ≤ -T} fej + ∫_{u > T} fej` for `T ≥ 0`. -/
lemma one_sub_I_eq {T : ℝ} (hT : 0 ≤ T) :
    1 - I T = (∫ u in Iic (-T), fej u) + ∫ u in Ioi T, fej u := by
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := T) (μ := volume)
    integrable_fej.integrableOn integrable_fej.integrableOn
  have h2 := intervalIntegral.integral_Iic_sub_Iic (a := -T) (b := T) (μ := volume)
    integrable_fej.integrableOn integrable_fej.integrableOn
  rw [I_eq, ← h2, ← integral_fej, ← h1]
  abel

/-- **Li-Liu (37), second line, with the paper's constant.** `0 ≤ 1 - I(T) ≤ 2/(π²T)`. -/
theorem one_sub_I_le {T : ℝ} (hT : 0 < T) : 0 ≤ 1 - I T ∧ 1 - I T ≤ 2 / (π ^ 2 * T) := by
  rw [one_sub_I_eq hT.le, tail_eq]
  have h0 : 0 ≤ ∫ u in Ioi T, fej u := setIntegral_nonneg measurableSet_Ioi (fun u _ => fej_nonneg u)
  have h1 := tail_le hT
  constructor
  · linarith
  · rw [show 2 / (π ^ 2 * T) = 2 * ((π ^ 2)⁻¹ * T⁻¹) by field_simp]
    linarith

theorem I_le_one {T : ℝ} (hT : 0 < T) : I T ≤ 1 := by linarith [(one_sub_I_le hT).1]

/-- A cruder constant, `1 - I(T) ≤ 1/(4T)`, since `π² > 8`. -/
theorem one_sub_I_le' {T : ℝ} (hT : 0 < T) : 1 - I T ≤ 1 / (4 * T) := by
  refine le_trans (one_sub_I_le hT).2 ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h8 : 8 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_lt_mul_of_pos_right h8 hT]

/-- **`I(T) → 1` as `T → ∞`.** -/
theorem tendsto_I : Tendsto I atTop (nhds 1) := by
  have hlow : Tendsto (fun T : ℝ => 1 - 2 / π ^ 2 * T⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_inv_atTop_zero.const_mul (2 / π ^ 2)).const_sub (1 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have := (one_sub_I_le hT).2
    rw [show 2 / (π ^ 2 * T) = 2 / π ^ 2 * T⁻¹ by field_simp] at this
    linarith
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact I_le_one hT

/-- Vacuity: at T = 1 the bound reads `1 - 2/π² ≤ I(1) ≤ 1`, about `0.797 ≤ I(1)`. -/
theorem vacuity : 1 - 2 / π ^ 2 ≤ I 1 ∧ I 1 ≤ 1 := by
  have := one_sub_I_le (T := 1) one_pos
  rw [mul_one] at this
  constructor <;> linarith [this.1, this.2]

end LeanLab.Linnik.U1394Fejer
