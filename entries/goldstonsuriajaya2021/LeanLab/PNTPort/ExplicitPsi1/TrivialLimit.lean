module

public import LeanLab.PNTPort.ExplicitPsi1.TrivialRect

/-!
# The explicit formula for `ψ₁` with the trivial zeros

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6551. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input.

The left edge `Re s = -1/2` of `Final.explicit_formula_psi1` is moved to `Re s = -2K - 1/2`: the
horizontal edges of `[-2K - 1/2, -1/2] × [-T, T]` vanish as `T → ∞`, `line_identity`, and for
`x > 1` the far line vanishes as `K → ∞`, `left_integral_eq`:

`(1/2π) ∫ F(-1/2 + it) dt = (ζ'/ζ)(-1) x⁻¹ - Σ_{n ≥ 0} x^{ρₙ}/(ρₙ(ρₙ + 1))`, `ρₙ = -2(n + 1)`.

`explicit_formula_psi1_trivial`: for `x > 1`,
`Σ Λ(n) w₁(n/x) = x/2 - ζ'(0)/ζ(0) - Σ_ρ m(ρ) x^ρ/(ρ(ρ + 1)) + (ζ'/ζ)(-1) x⁻¹ - Σₙ x^{ρₙ}/(ρₙ(ρₙ + 1))`,
Davenport's formula for `ψ₁(x)/x`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex Set Filter Metric Topology MeasureTheory
open scoped Real
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

/-- The trivial zero term `x^ρ/(ρ(ρ + 1))` at `ρ = -2(n + 1)`. -/
noncomputable def tterm (x : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / ((-2 * ((n : ℂ) + 1)) * (-2 * ((n : ℂ) + 1) + 1))

lemma norm_line_ge (K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    (1 + ‖t‖) ^ 2 / 4 ≤
      ‖((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) *
        ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I + 1)‖ := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rw [norm_mul, Real.norm_eq_abs]
  set s : ℂ := (((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I with hs
  have e1 : (1 + |t|) / 2 ≤ ‖s‖ := by
    have a := abs_im_le_norm s
    have b := abs_re_le_norm s
    have hre : s.re = -2 * (K : ℝ) - 1 / 2 := by simp [hs]
    have him : s.im = t := by simp [hs]
    rw [hre, abs_of_neg (by linarith)] at b
    rw [him] at a
    linarith
  have e2 : (1 + |t|) / 2 ≤ ‖s + 1‖ := by
    have a := abs_im_le_norm (s + 1)
    have b := abs_re_le_norm (s + 1)
    have hre : (s + 1).re = -2 * (K : ℝ) + 1 / 2 := by simp [hs]; ring
    have him : (s + 1).im = t := by simp [hs]
    rw [hre, abs_of_neg (by linarith)] at b
    rw [him] at a
    linarith
  have h0 : 0 ≤ (1 + |t|) / 2 := by positivity
  calc (1 + |t|) ^ 2 / 4 = ((1 + |t|) / 2) * ((1 + |t|) / 2) := by ring
    _ ≤ _ := mul_le_mul e1 e2 h0 (norm_nonneg _)

/-- **Far line majorant**: `‖F(-2K - 1/2 + it)‖ ≤ (A + 16K) x^{-2K-1/2} (1 + |t|)^{-3/2}`. -/
theorem line_bound : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → ∀ K : ℕ, 1 ≤ K → ∀ t : ℝ,
    ‖F x ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤
      (A + 16 * K) * x ^ (-2 * (K : ℝ) - 1 / 2) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨AL, hAL, hline⟩ := logDeriv_line
  refine ⟨20 * AL, by positivity, fun x hx K hK t => ?_⟩
  rw [norm_F hx]
  have hre : ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I).re = -2 * (K : ℝ) - 1 / 2 := by simp
  rw [hre]
  have hu : 0 < 1 + ‖t‖ := by positivity
  have hb := (hline K t).2
  have hlog := log_le_sqrt t
  rw [Real.norm_eq_abs] at hlog
  have hden := norm_line_ge K hK t
  have hxp : 0 < x ^ (-2 * (K : ℝ) - 1 / 2) := Real.rpow_pos_of_pos hx _
  have hsq1 : 1 ≤ (1 + ‖t‖) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg t]) (by norm_num)
  have hKp : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hd0 : 0 < (1 + ‖t‖) ^ 2 / 4 := by positivity
  have hsplit : (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) = (1 + ‖t‖) ^ (1 / 2 : ℝ) / (1 + ‖t‖) ^ 2 := by
    rw [show -(3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hu]; norm_cast
  rw [hsplit]
  have hnum : ‖deriv ζ ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) /
      ζ ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤
        (5 * AL + 4 * K) * (1 + ‖t‖) ^ (1 / 2 : ℝ) := by
    rw [Real.norm_eq_abs]
    calc _ ≤ AL * Real.log (|t| + 3) + 4 * K + AL := hb
      _ ≤ AL * (4 * (1 + |t|) ^ (1 / 2 : ℝ)) + (4 * K + AL) * (1 + |t|) ^ (1 / 2 : ℝ) := by
          rw [Real.norm_eq_abs] at hsq1
          nlinarith
      _ = _ := by ring
  calc ‖deriv ζ ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) /
        ζ ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ *
        (x ^ (-2 * (K : ℝ) - 1 / 2) / ‖((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) *
          ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I + 1)‖)
      ≤ ((5 * AL + 4 * K) * (1 + ‖t‖) ^ (1 / 2 : ℝ)) *
          (x ^ (-2 * (K : ℝ) - 1 / 2) / ((1 + ‖t‖) ^ 2 / 4)) := by
        gcongr
    _ ≤ (20 * AL + 16 * K) * x ^ (-2 * (K : ℝ) - 1 / 2) *
          ((1 + ‖t‖) ^ (1 / 2 : ℝ) / (1 + ‖t‖) ^ 2) := by
        rw [le_iff_eq_or_lt]; left
        field_simp; ring

lemma continuous_F_far {x : ℝ} (hx : 0 < x) (K : ℕ) (hK : 1 ≤ K) :
    Continuous (fun t : ℝ => F x ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)) := by
  obtain ⟨AL, _, hline⟩ := logDeriv_line
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  exact continuous_F_line hx (by linarith) (by intro h; linarith) (by linarith)
    (fun t => (hline K t).1)

theorem integrable_far {x : ℝ} (hx : 0 < x) (K : ℕ) (hK : 1 ≤ K) :
    Integrable (fun t : ℝ => F x ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)) := by
  obtain ⟨A, _, hA⟩ := line_bound
  have hg : Integrable (fun t : ℝ =>
      (A + 16 * K) * x ^ (-2 * (K : ℝ) - 1 / 2) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  exact hg.mono' (continuous_F_far hx K hK).aestronglyMeasurable
    (Eventually.of_forall (hA x hx K hK))

/-- `‖∫ F(-2K - 1/2 + it) dt‖ ≤ (A + 16K) x^{-2K-1/2} I₀`. -/
theorem norm_integral_far_le : ∃ A I0 : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 < x → ∀ K : ℕ, 1 ≤ K →
    ‖∫ t : ℝ, F x ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤
      (A + 16 * K) * x ^ (-2 * (K : ℝ) - 1 / 2) * I0 := by
  obtain ⟨A, hA0, hA⟩ := line_bound
  refine ⟨A, ∫ t : ℝ, (1 + ‖t‖) ^ (-(3 / 2 : ℝ)), hA0.le, fun x hx K hK => ?_⟩
  have hg : Integrable (fun t : ℝ =>
      (A + 16 * K) * x ^ (-2 * (K : ℝ) - 1 / 2) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine (norm_integral_le_of_norm_le hg (Eventually.of_forall (hA x hx K hK))).trans (le_of_eq ?_)
  rw [integral_const_mul]

/-- The horizontal edges: `‖∫_{σ}^{-1/2} F(u + iy) du‖ ≤ 2K (A log(T + 3) + 2K + 1 + A) X/T²`. -/
theorem horiz_bound : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → ∀ K : ℕ, 1 ≤ K → ∀ y : ℝ, 1 ≤ |y| →
    ‖HIntL x (-2 * (K : ℝ) - 1 / 2) y‖ ≤
      2 * K * ((A * Real.log (|y| + 3) + 2 * K + 1 + A) *
        (x ^ (-2 * (K : ℝ) - 1 / 2) + x ^ (-1 / 2 : ℝ)) / y ^ 2) := by
  obtain ⟨A, hA, hreg⟩ := logDeriv_left_region
  refine ⟨A, hA, fun x hx K hK y hy => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  have hσle : σ ≤ -1 / 2 := by rw [hσ]; linarith
  have hlen : |(-1 / 2 : ℝ) - σ| = 2 * K := by rw [hσ, abs_of_nonneg (by linarith)]; ring
  unfold HIntL
  suffices hk : ∀ u ∈ Set.uIoc σ (-1 / 2 : ℝ), ‖F x ((u : ℂ) + y * I)‖ ≤
      (A * Real.log (|y| + 3) + 2 * K + 1 + A) * ((x ^ σ + x ^ (-1 / 2 : ℝ)) / y ^ 2) by
    have key := intervalIntegral.norm_integral_le_of_norm_le_const hk
    rw [hlen] at key
    refine key.trans (le_of_eq ?_)
    ring
  intro u hu
  rw [uIoc_of_le hσle] at hu
  obtain ⟨hu1, hu2⟩ := hu
  rw [norm_F hx]
  have hre : ((u : ℂ) + y * I).re = u := by simp
  rw [hre]
  have hb := (hreg u y hu2 hy).2
  have hy2 : y ^ 2 ≤ ‖((u : ℂ) + y * I) * ((u : ℂ) + y * I + 1)‖ := by
    rw [norm_mul]
    have a := abs_im_le_norm ((u : ℂ) + y * I)
    have b := abs_im_le_norm ((u : ℂ) + y * I + 1)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      one_im, add_zero] at a b
    have hy0 : 0 ≤ |y| := abs_nonneg y
    calc y ^ 2 = |y| * |y| := by rw [← sq_abs]; ring
      _ ≤ _ := mul_le_mul a b hy0 (norm_nonneg _)
  have hy2p : 0 < y ^ 2 := by
    have : 0 < |y| := by linarith
    rw [← sq_abs]; positivity
  have hxu : x ^ u ≤ x ^ σ + x ^ (-1 / 2 : ℝ) := by
    have a := Real.rpow_nonneg hx.le σ
    have b := Real.rpow_nonneg hx.le (-1 / 2 : ℝ)
    rcases le_total 1 x with hx1 | hx1
    · have := Real.rpow_le_rpow_of_exponent_le hx1 hu2; linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 hu1.le; linarith
  have hlog0 : 0 ≤ Real.log (|y| + 3) := Real.log_nonneg (by linarith)
  have hnum : ‖deriv ζ ((u : ℂ) + y * I) / ζ ((u : ℂ) + y * I)‖ ≤
      A * Real.log (|y| + 3) + 2 * K + 1 + A := by
    calc _ ≤ A * Real.log (|y| + 3) - u + A := hb
      _ ≤ _ := by linarith
  have hnum0 : 0 ≤ A * Real.log (|y| + 3) + 2 * K + 1 + A := by positivity
  calc ‖deriv ζ ((u : ℂ) + y * I) / ζ ((u : ℂ) + y * I)‖ *
        (x ^ u / ‖((u : ℂ) + y * I) * ((u : ℂ) + y * I + 1)‖)
      ≤ (A * Real.log (|y| + 3) + 2 * K + 1 + A) * ((x ^ σ + x ^ (-1 / 2 : ℝ)) / y ^ 2) := by
        gcongr

/-- **The rectangle identity in the limit `T → ∞`**, for fixed `K ≥ 1`. -/
theorem line_identity {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) :
    (1 / (2 * π) : ℂ) * ((∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I)) -
        ∫ t : ℝ, F x ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)) =
      (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) - ∑ n ∈ Finset.range K, tterm x n := by
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  set T : ℕ → ℝ := fun n => (n : ℝ) + 1 with hT
  have hTpos : ∀ n, 0 < T n := fun n => by simp [hT]; positivity
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hid : ∀ n : ℕ, (1 / (2 * π) : ℂ) * (VInt x (-1 / 2) (T n) - VInt x σ (T n)) +
      (1 / (2 * π * I)) * (HIntL x σ (-T n) - HIntL x σ (T n)) =
        (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) - ∑ n ∈ Finset.range K, tterm x n := by
    intro n
    rw [← rect_decomp_left]
    exact rect_left hx hK (hTpos n)
  have hVL : Tendsto (fun n => VInt x (-1 / 2) (T n)) atTop
      (𝓝 (∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I))) :=
    intervalIntegral_tendsto_integral (integrable_left hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hVσ : Tendsto (fun n => VInt x σ (T n)) atTop
      (𝓝 (∫ t : ℝ, F x (((σ : ℝ) : ℂ) + t * I))) :=
    intervalIntegral_tendsto_integral (integrable_far hx K hK)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  obtain ⟨A, hA, hH⟩ := horiz_bound
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set X : ℝ := x ^ σ + x ^ (-1 / 2 : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  set C : ℝ := 2 * K * ((4 * A + 2 * K + 1 + A) * X) with hC
  have hC0 : 0 ≤ C := by positivity
  have hHb : ∀ n : ℕ, ‖HIntL x σ (-T n) - HIntL x σ (T n)‖ ≤ 2 * (2 * C / T n) := by
    intro n
    have hT1 : 1 ≤ T n := by simp [hT]
    have hb : ∀ y : ℝ, |y| = T n → ‖HIntL x σ y‖ ≤ 2 * C / T n := by
      intro y hy
      have hy1 : 1 ≤ |y| := by rw [hy]; exact hT1
      refine (hH x hx K hK y hy1).trans ?_
      show 2 * K * ((A * Real.log (|y| + 3) + 2 * K + 1 + A) * X / y ^ 2) ≤ 2 * C / T n
      have hyy : y ^ 2 = T n ^ 2 := by rw [← sq_abs, hy]
      rw [hy, hyy]
      have hl := log_le_sqrt (T n)
      rw [Real.norm_eq_abs, abs_of_pos (hTpos n)] at hl
      have hs : (1 + T n) ^ (1 / 2 : ℝ) ≤ 1 + T n := by
        apply Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
      have hlog : Real.log (T n + 3) ≤ 4 * (2 * T n) := by linarith
      have hlog0 : 0 ≤ Real.log (T n + 3) := Real.log_nonneg (by linarith)
      have hnum : A * Real.log (T n + 3) + 2 * K + 1 + A ≤ (4 * A + 2 * K + 1 + A) * (2 * T n) := by
        nlinarith
      have key : 2 * K * ((A * Real.log (T n + 3) + 2 * K + 1 + A) * X) ≤ 2 * C * T n := by
        rw [hC]
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnum hX0)
          (show (0 : ℝ) ≤ 2 * K by positivity)
        nlinarith
      have hT2 : 0 < T n ^ 2 := by have := hTpos n; positivity
      calc 2 * K * ((A * Real.log (T n + 3) + 2 * K + 1 + A) * X / T n ^ 2)
          = (2 * K * ((A * Real.log (T n + 3) + 2 * K + 1 + A) * X)) / T n ^ 2 := by ring
        _ ≤ (2 * C * T n) / T n ^ 2 := by gcongr
        _ = 2 * C / T n := by have := (hTpos n).ne'; field_simp
    calc _ ≤ ‖HIntL x σ (-T n)‖ + ‖HIntL x σ (T n)‖ := norm_sub_le _ _
      _ ≤ 2 * C / T n + 2 * C / T n :=
          add_le_add (hb _ (by rw [abs_neg, abs_of_pos (hTpos n)]))
            (hb _ (abs_of_pos (hTpos n)))
      _ = 2 * (2 * C / T n) := by ring
  have hHt : Tendsto (fun n => HIntL x σ (-T n) - HIntL x σ (T n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm hHb
    have := (tendsto_const_nhds (x := 2 * C)).div_atTop hTtop
    simpa using this.const_mul 2
  have hlim1 : Tendsto (fun n => (1 / (2 * π) : ℂ) * (VInt x (-1 / 2) (T n) - VInt x σ (T n)) +
      (1 / (2 * π * I)) * (HIntL x σ (-T n) - HIntL x σ (T n))) atTop
      (𝓝 ((1 / (2 * π) : ℂ) * ((∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I)) -
        ∫ t : ℝ, F x (((σ : ℝ) : ℂ) + t * I)) + (1 / (2 * π * I)) * 0)) :=
    ((hVL.sub hVσ).const_mul _).add (hHt.const_mul _)
  have hlim2 : Tendsto (fun n => (1 / (2 * π) : ℂ) * (VInt x (-1 / 2) (T n) - VInt x σ (T n)) +
      (1 / (2 * π * I)) * (HIntL x σ (-T n) - HIntL x σ (T n))) atTop
      (𝓝 ((deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) - ∑ n ∈ Finset.range K, tterm x n)) := by
    simp_rw [hid]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim1 hlim2
  rw [mul_zero, add_zero] at heq
  exact heq

/-- `‖tterm x n‖ ≤ 1/(n + 1)²` for `x ≥ 1`. -/
lemma norm_tterm_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : ‖tterm x n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold tterm
  have hx0 : 0 < x := by linarith
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx0]
  have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [hre]
  have hxp : x ^ (-2 * ((n : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hden : ((n : ℝ) + 1) ^ 2 ≤ ‖(-2 * ((n : ℂ) + 1)) * (-2 * ((n : ℂ) + 1) + 1)‖ := by
    have e : (-2 * ((n : ℂ) + 1)) * (-2 * ((n : ℂ) + 1) + 1) =
        (((2 * (n : ℝ) + 2) * (2 * n + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  calc x ^ (-2 * ((n : ℝ) + 1)) / ‖(-2 * ((n : ℂ) + 1)) * (-2 * ((n : ℂ) + 1) + 1)‖
      ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by linarith) hp]
        nlinarith [Real.rpow_nonneg hx0.le (-2 * ((n : ℝ) + 1))]

lemma summable_tterm {x : ℝ} (hx : 1 ≤ x) : Summable (tterm x) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ?_ (norm_tterm_le hx)
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

/-- **The left line in closed form**, for `x > 1`:
`(1/2π) ∫ F(-1/2 + it) dt = (ζ'/ζ)(-1) x⁻¹ - Σₙ x^{ρₙ}/(ρₙ(ρₙ + 1))`. -/
theorem left_integral_eq {x : ℝ} (hx : 1 < x) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I) =
      (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) - ∑' n : ℕ, tterm x n := by
  have hx0 : 0 < x := by linarith
  obtain ⟨A, I0, hA0, hfar⟩ := norm_integral_far_le
  set L := ∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I) with hL
  set J : ℕ → ℂ := fun K => ∫ t : ℝ, F x ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) with hJ
  -- the far line tends to 0
  set r : ℝ := x ^ (-2 : ℝ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hx0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hpow : ∀ K : ℕ, x ^ (-2 * (K : ℝ) - 1 / 2) = x ^ (-1 / 2 : ℝ) * r ^ K := by
    intro K
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1; ring
  have hJ0 : Tendsto J atTop (𝓝 0) := by
    have hb : ∀ᶠ K : ℕ in atTop, ‖J K‖ ≤ x ^ (-1 / 2 : ℝ) * I0 * (A * r ^ K + 16 * (K * r ^ K)) := by
      filter_upwards [eventually_ge_atTop 1] with K hK
      refine (hfar x hx0 K hK).trans (le_of_eq ?_)
      rw [hpow]; ring
    apply squeeze_zero_norm' hb
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have h2 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
    have := ((h1.const_mul A).add (h2.const_mul 16)).const_mul (x ^ (-1 / 2 : ℝ) * I0)
    simpa using this
  -- the partial sums converge
  have hS := (summable_tterm hx.le).hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun K : ℕ => (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) -
      ∑ n ∈ Finset.range K, tterm x n + (1 / (2 * π) : ℂ) * J K) atTop
      (𝓝 ((deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) - ∑' n : ℕ, tterm x n +
        (1 / (2 * π) : ℂ) * 0)) :=
    (tendsto_const_nhds.sub hS).add (hJ0.const_mul _)
  have hconst : Tendsto (fun K : ℕ => (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) -
      ∑ n ∈ Finset.range K, tterm x n + (1 / (2 * π) : ℂ) * J K) atTop
      (𝓝 ((1 / (2 * π) : ℂ) * L)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have := line_identity hx0 hK
    rw [← this]; simp only [hJ, hL]; ring
  have heq := tendsto_nhds_unique hconst hlim
  rw [mul_zero, add_zero] at heq
  exact heq

/-- **The explicit formula for `ψ₁(x)/x` with the trivial zeros**, `x > 1`, Davenport ch. 17. -/
theorem explicit_formula_psi1_trivial {x : ℝ} (hx : 1 < x) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / x) =
      x / 2 - deriv ζ 0 / ζ 0 - ∑' ρ : Zall, zterm x ρ +
        (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) - ∑' n : ℕ, tterm x n := by
  rw [explicit_formula_psi1 (by linarith), left_integral_eq hx]
  ring

end LeanLab.PNTPort.ExplicitPsi1.Trivial
