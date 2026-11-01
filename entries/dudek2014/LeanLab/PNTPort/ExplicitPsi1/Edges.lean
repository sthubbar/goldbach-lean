module

public import LeanLab.PNTPort.ExplicitPsi1.ZeroSum
public import LeanLab.PNTPort.ZetaZeros.LeftLine
public import LeanLab.PNTPort.ZetaZeros.Perron1
public import LeanLab.PNTPort.StrongPNT.ZetaBounds

/-!
# The four edges of the rectangle `[-1/2, 2] × [-T, T]`

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input.

* `rect_decomp`: the rectangle integral as two vertical and two horizontal integrals.
* `norm_HInt_le`: at a good height `T'` of `ZetaZeros.good_height_full` the horizontal edges at
  `±T'` are `O(log² T · X/T²)`, `X = x² + x^{-1/2}`.
* `integrable_left`, `norm_integral_left_le`: on `Re s = -1/2` the integrand is integrable and
  its integral is `O(x^{-1/2})`, from `ZetaZeros.logDeriv_left_line`.
* `integrable_right`, `perron_F`: on `Re s = 2` the integrand is integrable and
  `(1/2π) ∫ F(2 + it) dt = Σ Λ(n) max(0, 1 - n/x)`, from `ZetaZeros.psi1_perron_zeta`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate Real

local notation "ζ" => riemannZeta

/-- The vertical integral `∫_{-T}^{T} F(σ + it) dt`. -/
noncomputable def VInt (x σ T : ℝ) : ℂ := ∫ t in -T..T, F x ((σ : ℂ) + t * I)

/-- The horizontal integral `∫_{-1/2}^{2} F(σ + iy) dσ`. -/
noncomputable def HInt (x y : ℝ) : ℂ := ∫ σ in (-1 / 2 : ℝ)..2, F x ((σ : ℂ) + y * I)

theorem rect_decomp (x T : ℝ) :
    RectangleIntegral' (F x) ⟨-1 / 2, -T⟩ ⟨2, T⟩ =
      (1 / (2 * π)) * (VInt x 2 T - VInt x (-1 / 2) T) +
        (1 / (2 * π * I)) * (HInt x (-T) - HInt x T) := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, VInt, HInt]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : I ≠ 0 := I_ne_zero
  rw [div_mul_eq_mul_div, one_mul]
  field_simp
  ring

/-- `X = x² + x^{-1/2}` bounds `x^σ` for `-1/2 ≤ σ ≤ 2`. -/
noncomputable def Xb (x : ℝ) : ℝ := x ^ (2 : ℝ) + x ^ (-1 / 2 : ℝ)

lemma rpow_le_Xb {x σ : ℝ} (hx : 0 < x) (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 2) : x ^ σ ≤ Xb x := by
  unfold Xb
  have a := Real.rpow_nonneg hx.le (2 : ℝ)
  have b := Real.rpow_nonneg hx.le (-1 / 2 : ℝ)
  rcases le_total 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 h2; linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 h1; linarith

lemma Xb_pos {x : ℝ} (hx : 0 < x) : 0 < Xb x := by
  unfold Xb; positivity

/-- `‖F x s‖ = ‖ζ'/ζ(s)‖ x^{Re s}/‖s(s + 1)‖`. -/
lemma norm_F {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖F x s‖ = ‖deriv ζ s / ζ s‖ * (x ^ s.re / ‖s * (s + 1)‖) := by
  simp only [F, norm_mul, norm_neg, norm_div, norm_cpow_eq_rpow_re_of_pos hx]

/-- On a horizontal line at height `y`, `|y| ≥ 1`: `‖F‖ ≤ ‖ζ'/ζ‖ X/y²`. -/
lemma norm_F_horiz_le {x : ℝ} (hx : 0 < x) {σ y : ℝ} (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 2)
    (hy : 1 ≤ |y|) :
    ‖F x ((σ : ℂ) + y * I)‖ ≤ ‖deriv ζ ((σ : ℂ) + y * I) / ζ ((σ : ℂ) + y * I)‖ * (Xb x / y ^ 2) := by
  rw [norm_F hx]
  have hre : ((σ : ℂ) + y * I).re = σ := by simp
  have hy2 : y ^ 2 ≤ ‖((σ : ℂ) + y * I) * ((σ : ℂ) + y * I + 1)‖ := by
    have := norm_mul_add_one_ge ((σ : ℂ) + y * I)
    simpa [sq_abs] using this
  have hy0 : 0 < y ^ 2 := by
    have : 0 < |y| := by linarith
    rw [← sq_abs]; positivity
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact div_le_div₀ (Xb_pos hx).le (rpow_le_Xb hx h1 h2) hy0 hy2

/-- **Good heights, both signs**: for `T ≥ 5` some `T' ∈ [T, T + 1]` has ζ nonzero and
`‖ζ'/ζ‖ ≤ C log² T` on both segments `[-1/2, 2] ± iT'`. -/
theorem good_height_pm : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
    ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T', -T'} : Set ℝ), ζ ((σ : ℂ) + y * I) ≠ 0 ∧
      ‖deriv ζ ((σ : ℂ) + y * I) / ζ ((σ : ℂ) + y * I)‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨C, hC, hg⟩ := ZetaZeros.good_height_full
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨T', hT'I, hgT⟩ := hg T hT
  refine ⟨T', hT'I, fun σ hσ y hy => ?_⟩
  obtain ⟨hne, hb⟩ := hgT σ hσ
  have e : (σ : ℂ) + I * T' = (σ : ℂ) + T' * I := by ring
  rw [e] at hne hb
  rcases hy with rfl | rfl
  · exact ⟨hne, hb⟩
  · have hc : (σ : ℂ) + ((-T' : ℝ) : ℂ) * I = conj ((σ : ℂ) + T' * I) := by
      apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj, deriv_riemannZeta_conj]
    refine ⟨fun h => hne (by simpa using h), ?_⟩
    rw [← map_div₀, RCLike.norm_conj]
    exact hb

/-- The horizontal edges at a good height are `O(log² T · X/T²)`. -/
theorem norm_HInt_le {x : ℝ} (hx : 0 < x) {C T T' y : ℝ} (hT : 5 ≤ T) (hTT : T ≤ T')
    (hy : |y| = T')
    (hb : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
      ‖deriv ζ ((σ : ℂ) + y * I) / ζ ((σ : ℂ) + y * I)‖ ≤ C * Real.log T ^ 2) :
    ‖HInt x y‖ ≤ C * Real.log T ^ 2 * (Xb x / T ^ 2) * (5 / 2) := by
  unfold HInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1 / 2) (b := 2) (C := C * Real.log T ^ 2 * (Xb x / T ^ 2))
    (f := fun σ : ℝ => F x ((σ : ℂ) + y * I)) ?_
  · rw [show |(2 : ℝ) - -1 / 2| = 5 / 2 by norm_num] at h
    exact h
  intro σ hσ
  rw [uIoc_of_le (by norm_num)] at hσ
  have hσ' : σ ∈ Icc (-1 / 2 : ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
  have hy1 : 1 ≤ |y| := by rw [hy]; linarith
  refine (norm_F_horiz_le hx hσ'.1 hσ'.2 hy1).trans ?_
  have hX := Xb_pos hx
  have hT0 : 0 < T := by linarith
  have hyT : T ^ 2 ≤ y ^ 2 := by
    rw [← sq_abs y, hy]; exact pow_le_pow_left₀ hT0.le hTT 2
  calc ‖deriv ζ ((σ : ℂ) + y * I) / ζ ((σ : ℂ) + y * I)‖ * (Xb x / y ^ 2)
      ≤ C * Real.log T ^ 2 * (Xb x / y ^ 2) := by gcongr; exact hb σ hσ'
    _ ≤ C * Real.log T ^ 2 * (Xb x / T ^ 2) := by
        have : 0 ≤ C * Real.log T ^ 2 := le_trans (norm_nonneg _) (hb σ hσ')
        gcongr

lemma continuous_F_line {x : ℝ} (hx : 0 < x) {σ : ℝ} (h0 : σ ≠ 0) (hm1 : σ ≠ -1) (h1 : σ ≠ 1)
    (hz : ∀ t : ℝ, ζ ((σ : ℂ) + t * I) ≠ 0) : Continuous (fun t : ℝ => F x ((σ : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : ∀ a : ℝ, σ ≠ a → (σ : ℂ) + t * I ≠ a := by
    intro a ha h; apply ha; have := congr_arg re h; simpa using this
  have hA := analyticAt_F hx (by simpa using hne 0 h0) (by simpa using hne (-1) hm1)
    (by simpa using hne 1 h1) (hz t)
  exact ContinuousAt.comp (g := F x) (f := fun t : ℝ => (σ : ℂ) + t * I) hA.continuousAt
    (by fun_prop)

lemma norm_left_ge (t : ℝ) :
    (1 + ‖t‖) ^ 2 / 16 ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I) * (((-1 / 2 : ℝ) : ℂ) + t * I + 1)‖ := by
  rw [norm_mul, Real.norm_eq_abs]
  have e1 : (1 + |t|) / 4 ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
    have a := abs_im_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I)
    have b := abs_re_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      add_re, mul_re, sub_self, add_zero] at a b
    rw [show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num [abs_of_neg]] at b
    linarith
  have e2 : (1 + |t|) / 4 ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I + 1)‖ := by
    have a := abs_im_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I + 1)
    have b := abs_re_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I + 1)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      add_re, mul_re, sub_self, add_zero, one_re, one_im] at a b
    rw [show |(-1 / 2 + 1 : ℝ)| = 1 / 2 by norm_num [abs_of_pos]] at b
    linarith
  have h0 : 0 ≤ (1 + |t|) / 4 := by positivity
  calc (1 + |t|) ^ 2 / 16 = ((1 + |t|) / 4) * ((1 + |t|) / 4) := by ring
    _ ≤ _ := mul_le_mul e1 e2 h0 (norm_nonneg _)

lemma log_le_sqrt (t : ℝ) : Real.log (‖t‖ + 3) ≤ 4 * (1 + ‖t‖) ^ (1 / 2 : ℝ) := by
  have hy : 0 ≤ ‖t‖ + 3 := by positivity
  have h1 := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (‖t‖ + 3) ^ (1 / 2 : ℝ) ≤ (4 * (1 + ‖t‖)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hy (by linarith [norm_nonneg t]) (by norm_num)
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [Real.mul_rpow (by norm_num) (by positivity), h4] at h2
  have : (‖t‖ + 3) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (‖t‖ + 3) ^ (1 / 2 : ℝ) := by ring
  linarith

/-- **Left line majorant**: `‖F(-1/2 + it)‖ ≤ A x^{-1/2} (1 + |t|)^{-3/2}`. -/
theorem left_bound : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ,
    ‖F x (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ A * x ^ (-1 / 2 : ℝ) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hL⟩ := ZetaZeros.logDeriv_left_line
  refine ⟨64 * C, by positivity, fun x hx t => ?_⟩
  rw [norm_F hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + t * I).re = -1 / 2 := by simp
  rw [hre]
  have hu : 0 < 1 + ‖t‖ := by positivity
  have hb := (hL t).2
  have hlog := log_le_sqrt t
  rw [Real.norm_eq_abs] at hlog
  have hden := norm_left_ge t
  have hxp : 0 < x ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hd0 : 0 < (1 + ‖t‖) ^ 2 / 16 := by positivity
  have hsplit : (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) = (1 + ‖t‖) ^ (1 / 2 : ℝ) / (1 + ‖t‖) ^ 2 := by
    rw [show -(3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hu]; norm_cast
  rw [hsplit]
  calc ‖deriv ζ (((-1 / 2 : ℝ) : ℂ) + t * I) / ζ (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
        (x ^ (-1 / 2 : ℝ) / ‖(((-1 / 2 : ℝ) : ℂ) + t * I) * (((-1 / 2 : ℝ) : ℂ) + t * I + 1)‖)
      ≤ (C * (4 * (1 + ‖t‖) ^ (1 / 2 : ℝ))) * (x ^ (-1 / 2 : ℝ) / ((1 + ‖t‖) ^ 2 / 16)) := by
        gcongr
        rw [Real.norm_eq_abs] at *
        exact hb.trans (by gcongr)
    _ = 64 * C * x ^ (-1 / 2 : ℝ) * ((1 + ‖t‖) ^ (1 / 2 : ℝ) / (1 + ‖t‖) ^ 2) := by
        field_simp; norm_num

theorem integrable_left {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => F x (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  obtain ⟨A, _, hA⟩ := left_bound
  have hg : Integrable (fun t : ℝ => A * x ^ (-1 / 2 : ℝ) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall (hA x hx))
  exact (continuous_F_line hx (by norm_num) (by norm_num) (by norm_num)
    (fun t => (ZetaZeros.logDeriv_left_line.choose_spec.2 t).1)).aestronglyMeasurable

/-- **The left line**: `‖∫ F(-1/2 + it) dt‖ ≤ K x^{-1/2}`. -/
theorem norm_integral_left_le : ∃ K : ℝ, ∀ x : ℝ, 0 < x →
    ‖∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K * x ^ (-1 / 2 : ℝ) := by
  obtain ⟨A, _, hA⟩ := left_bound
  refine ⟨A * ∫ t : ℝ, (1 + ‖t‖) ^ (-(3 / 2 : ℝ)), fun x hx => ?_⟩
  have hg : Integrable (fun t : ℝ => A * x ^ (-1 / 2 : ℝ) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine (norm_integral_le_of_norm_le hg (Eventually.of_forall (hA x hx))).trans (le_of_eq ?_)
  rw [integral_const_mul]; ring

/-- **The right line** is integrable: `‖F(2 + it)‖ ≤ ‖ζ'(2)/ζ(2)‖ x² (1 + t²)⁻¹`. -/
theorem integrable_right {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => F x (((2 : ℝ) : ℂ) + t * I)) := by
  set D := ‖deriv ζ ((2 : ℝ) : ℂ) / ζ ((2 : ℝ) : ℂ)‖
  have hg : Integrable (fun t : ℝ => D * x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hz : ∀ t : ℝ, ζ (((2 : ℝ) : ℂ) + t * I) ≠ 0 := fun t =>
    riemannZeta_ne_zero_of_one_le_re (by simp)
  refine hg.mono'
    (continuous_F_line hx (by norm_num) (by norm_num) (by norm_num) hz).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_F hx]
  have hre : (((2 : ℝ) : ℂ) + t * I).re = 2 := by simp
  rw [hre]
  have hdl := dlog_riemannZeta_bdd_on_vertical_lines_generalized 2 2 t (by norm_num) le_rfl
  rw [neg_div, norm_neg] at hdl
  have hk := ZetaZeros.norm_inv_kernel_le (σ := 2) (by norm_num) t
  rw [norm_div, norm_one] at hk
  have hxp : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx.le _
  calc ‖deriv ζ (((2 : ℝ) : ℂ) + t * I) / ζ (((2 : ℝ) : ℂ) + t * I)‖ *
        (x ^ (2 : ℝ) / ‖(((2 : ℝ) : ℂ) + t * I) * (((2 : ℝ) : ℂ) + t * I + 1)‖)
      ≤ D * (x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹) := by
        have hkx : x ^ (2 : ℝ) / ‖(((2 : ℝ) : ℂ) + t * I) * (((2 : ℝ) : ℂ) + t * I + 1)‖ ≤
            x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹ := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hk hxp
        exact mul_le_mul hdl hkx (by positivity) (norm_nonneg _)
    _ = D * x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹ := by ring

/-- **Perron on `Re s = 2`**: `Σ Λ(n) max(0, 1 - n/x) = (1/2π) ∫ F(2 + it) dt`. -/
theorem perron_F {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / x) =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, F x (((2 : ℝ) : ℂ) + t * I) := by
  rw [ZetaZeros.psi1_perron_zeta hx (σ := 2) (by norm_num)]
  congr 2
  funext t
  simp only [F, ZetaZeros.Kσ]
  ring

end LeanLab.PNTPort.ExplicitPsi1

