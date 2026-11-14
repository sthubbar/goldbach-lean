module

public import LeanLab.Linnik.ExplicitFormula.Kernel
public import LeanLab.Linnik.ExplicitFormula.Residues
public import LeanLab.Linnik.ExplicitFormula.Heights
public import LeanLab.Linnik.ExplicitFormula.ZeroSum

/-!
# The explicit formula for primitive `L(s, χ)`, uniform in `q`

AI wrote the Lean code. Binary Goldbach is OPEN.
Davenport ch. 17 and 19, in the Cesaro form of `LeanLab.PNTPort.ExplicitPsi1.Final` for `ζ`:
`Σ χ(n)Λ(n) w(n/x) = [q = 1] x/6 - Σ_{ρ ∈ Zall} m(ρ) x^ρ/((ρ+1)(ρ+2)) + (1/2π) ∫ F(-1/2 + it) dt`
for every primitive `χ` mod `q` and `x > 0`, and the left line integral is `≪ log(q + 2) x^(-1/2)`
uniformly in `q`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex MeasureTheory
open scoped Real


open Filter Topology Set

/-! ### Helpers, ported from `LeanLab.PNTPort.ExplicitPsi1.Edges` -/

/-- Elementary: the vertical integral `∫_{-T}^{T} F(σ + it) dt`. -/
noncomputable def efVInt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ T : ℝ) : ℂ :=
  ∫ t in -T..T, Fchi χ x ((σ : ℂ) + t * I)

/-- Elementary: the horizontal integral `∫_{-1/2}^{2} F(σ + iy) dσ`. -/
noncomputable def efHInt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x y : ℝ) : ℂ :=
  ∫ σ in (-1 / 2 : ℝ)..2, Fchi χ x ((σ : ℂ) + y * I)

/-- Elementary: the rectangle integral as two vertical and two horizontal integrals. -/
theorem ef_rect_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x T : ℝ) :
    RectangleIntegral' (Fchi χ x) ⟨-1 / 2, -T⟩ ⟨2, T⟩ =
      (1 / (2 * π)) * (efVInt χ x 2 T - efVInt χ x (-1 / 2) T) +
        (1 / (2 * π * I)) * (efHInt χ x (-T) - efHInt χ x T) := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, efVInt,
    efHInt]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : I ≠ 0 := I_ne_zero
  rw [div_mul_eq_mul_div, one_mul]
  field_simp
  ring

/-- Elementary: `X = x² + x^(-1/2)`. -/
noncomputable def efXb (x : ℝ) : ℝ := x ^ (2 : ℝ) + x ^ (-1 / 2 : ℝ)

/-- Elementary: `x^σ ≤ X` for `-1/2 ≤ σ ≤ 2`. -/
lemma ef_rpow_le_Xb {x σ : ℝ} (hx : 0 < x) (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 2) : x ^ σ ≤ efXb x := by
  unfold efXb
  have a := Real.rpow_nonneg hx.le (2 : ℝ)
  have b := Real.rpow_nonneg hx.le (-1 / 2 : ℝ)
  rcases le_total 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 h2; linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 h1; linarith

lemma ef_Xb_pos {x : ℝ} (hx : 0 < x) : 0 < efXb x := by
  unfold efXb; positivity

/-- Elementary: `‖F(s)‖ = ‖L'/L(s)‖ x^(Re s) / ‖(s+1)(s+2)‖`. -/
lemma ef_norm_Fchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖Fchi χ x s‖ = ‖deriv χ.LFunction s / χ.LFunction s‖ * (x ^ s.re / ‖(s + 1) * (s + 2)‖) := by
  rw [Fchi, norm_mul, norm_neg, norm_div ((x : ℂ) ^ s), norm_cpow_eq_rpow_re_of_pos hx]

/-- Elementary: on a horizontal line at height `y`, `‖F‖ ≤ ‖L'/L‖ X / y²`. -/
lemma ef_norm_F_horiz_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    {σ y : ℝ} (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 2) (hy : 1 ≤ |y|) :
    ‖Fchi χ x ((σ : ℂ) + y * I)‖ ≤
      ‖deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)‖ * (efXb x / y ^ 2) := by
  rw [ef_norm_Fchi χ hx]
  have hre : ((σ : ℂ) + y * I).re = σ := by simp
  have hy2 : y ^ 2 ≤ ‖((σ : ℂ) + y * I + 1) * ((σ : ℂ) + y * I + 2)‖ := by
    have := im_sq_le_norm_mul ((σ : ℂ) + y * I)
    simpa using this
  have hy0 : 0 < y ^ 2 := by
    have : 0 < |y| := by linarith
    rw [← sq_abs]; positivity
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact div_le_div₀ (ef_Xb_pos hx).le (ef_rpow_le_Xb hx h1 h2) hy0 hy2

/-- Elementary: the horizontal edges at a good height are `O(log²(T+2) X/T²)`. -/
theorem ef_norm_HInt_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    {C T T' y : ℝ} (hT : 5 ≤ T) (hTT : T ≤ T') (hy : |y| = T')
    (hb : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
      ‖deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)‖ ≤
        C * Real.log (T + 2) ^ 2) :
    ‖efHInt χ x y‖ ≤ C * Real.log (T + 2) ^ 2 * (efXb x / T ^ 2) * (5 / 2) := by
  unfold efHInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1 / 2) (b := 2) (C := C * Real.log (T + 2) ^ 2 * (efXb x / T ^ 2))
    (f := fun σ : ℝ => Fchi χ x ((σ : ℂ) + y * I)) ?_
  · rw [show |(2 : ℝ) - -1 / 2| = 5 / 2 by norm_num] at h
    exact h
  intro σ hσ
  rw [uIoc_of_le (by norm_num)] at hσ
  have hσ' : σ ∈ Icc (-1 / 2 : ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
  have hy1 : 1 ≤ |y| := by rw [hy]; linarith
  refine (ef_norm_F_horiz_le χ hx hσ'.1 hσ'.2 hy1).trans ?_
  have hX := ef_Xb_pos hx
  have hT0 : 0 < T := by linarith
  have hyT : T ^ 2 ≤ y ^ 2 := by
    rw [← sq_abs y, hy]; exact pow_le_pow_left₀ hT0.le hTT 2
  calc ‖deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)‖ * (efXb x / y ^ 2)
      ≤ C * Real.log (T + 2) ^ 2 * (efXb x / y ^ 2) := by gcongr; exact hb σ hσ'
    _ ≤ C * Real.log (T + 2) ^ 2 * (efXb x / T ^ 2) := by
        have : 0 ≤ C * Real.log (T + 2) ^ 2 := le_trans (norm_nonneg _) (hb σ hσ')
        gcongr

/-- Elementary: `F` is continuous on a vertical line `Re s = σ ≥ -1/2`, `σ ≠ 1`, free of zeros. -/
lemma ef_continuous_F_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    {σ : ℝ} (hσ : -1 / 2 ≤ σ) (h1 : σ ≠ 1) (hz : ∀ t : ℝ, χ.LFunction ((σ : ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => Fchi χ x ((σ : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hre : -1 / 2 ≤ ((σ : ℂ) + t * I).re := by simpa using hσ
  have hne : (σ : ℂ) + t * I ≠ 1 := by
    intro h; apply h1; have := congr_arg re h; simpa using this
  have hA := analyticAt_Fchi χ hx hre (Or.inl hne) (hz t)
  exact ContinuousAt.comp (g := Fchi χ x) (f := fun t : ℝ => (σ : ℂ) + t * I) hA.continuousAt
    (by fun_prop)

/-- Elementary: `(1 + |t|)²/16 ≤ ‖(s+1)(s+2)‖` on `s = -1/2 + it`. -/
lemma ef_norm_left_ge (t : ℝ) :
    (1 + |t|) ^ 2 / 16 ≤
      ‖((((-1 / 2 : ℝ) : ℂ) + t * I) + 1) * ((((-1 / 2 : ℝ) : ℂ) + t * I) + 2)‖ := by
  have e1 : (((-1 / 2 : ℝ) : ℂ) + t * I) + 1 = ((1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  have e2 : (((-1 / 2 : ℝ) : ℂ) + t * I) + 2 = ((3 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  rw [e1, e2, norm_mul, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
  have ha : (1 + |t|) / 4 ≤ √((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs t, abs_nonneg t]
  have hb : (1 + |t|) / 4 ≤ √((3 / 2 : ℝ) ^ 2 + t ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs t, abs_nonneg t]
  have h0 : 0 ≤ (1 + |t|) / 4 := by positivity
  calc (1 + |t|) ^ 2 / 16 = ((1 + |t|) / 4) * ((1 + |t|) / 4) := by ring
    _ ≤ _ := mul_le_mul ha hb h0 (Real.sqrt_nonneg _)

/-- Elementary: `log(|t| + 3) ≤ 4 (1 + |t|)^(1/2)`. -/
lemma ef_log_le_sqrt (t : ℝ) : Real.log (|t| + 3) ≤ 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hy : 0 ≤ |t| + 3 := by positivity
  have h1 := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (|t| + 3) ^ (1 / 2 : ℝ) ≤ (4 * (1 + |t|)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hy (by linarith [abs_nonneg t]) (by norm_num)
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [Real.mul_rpow (by norm_num) (by positivity), h4] at h2
  have : (|t| + 3) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (|t| + 3) ^ (1 / 2 : ℝ) := by ring
  linarith

/-- Elementary: `1 ≤ log(q + 2)` for `q ≥ 1`. -/
lemma ef_one_le_log_q {q : ℝ} (hq : 1 ≤ q) : 1 ≤ Real.log (q + 2) := by
  have h3 : Real.exp 1 ≤ q + 2 := by
    have := Real.exp_one_lt_d9; linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (q + 2) := Real.log_le_log (Real.exp_pos 1) h3

/-- Elementary: `log(q(|t|+2)) ≤ 5 log(q+2) (1+|t|)^(1/2)` for `q ≥ 1`. -/
lemma ef_log_qt_le {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    Real.log (q * (|t| + 2)) ≤ 5 * Real.log (q + 2) * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have ht : 0 < |t| + 2 := by positivity
  rw [Real.log_mul (by linarith) ht.ne']
  have hlq : Real.log q ≤ Real.log (q + 2) := Real.log_le_log (by linarith) (by linarith)
  have hlt : Real.log (|t| + 2) ≤ 4 * (1 + |t|) ^ (1 / 2 : ℝ) :=
    (Real.log_le_log ht (by linarith)).trans (ef_log_le_sqrt t)
  have hL1 := ef_one_le_log_q hq
  have hu : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  nlinarith

/-- Davenport ch. 19 via `logDeriv_left_line`: on `Re s = -1/2`,
`‖F(-1/2 + it)‖ ≤ A log(q + 2) x^(-1/2) (1 + |t|)^(-3/2)`, uniformly in the primitive `χ`. -/
theorem ef_left_majorant : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ x : ℝ, 0 < x → ∀ t : ℝ,
      ‖Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        A * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hL⟩ := logDeriv_left_line
  refine ⟨80 * C, by positivity, fun q _ χ hχ x hx t => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rw [ef_norm_Fchi χ hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + t * I).re = -(1 / 2) := by simp; norm_num
  rw [hre, Real.norm_eq_abs]
  have hs : (((-1 / 2 : ℝ) : ℂ) + t * I) = -1 / 2 + t * I := by push_cast; ring
  have hb := hL q χ hχ t
  rw [← hs] at hb
  have hlog := ef_log_qt_le hq1 t
  have hden := ef_norm_left_ge t
  have hu : 0 < 1 + |t| := by positivity
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hd0 : 0 < (1 + |t|) ^ 2 / 16 := by positivity
  have hsplit : (1 + |t|) ^ (-(3 / 2 : ℝ)) = (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 := by
    rw [show -(3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hu]; norm_cast
  rw [hsplit]
  have hLq : 0 ≤ Real.log (q + 2) := by linarith [ef_one_le_log_q hq1]
  calc ‖deriv χ.LFunction (((-1 / 2 : ℝ) : ℂ) + t * I) / χ.LFunction (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
        (x ^ (-(1 / 2) : ℝ) / ‖((((-1 / 2 : ℝ) : ℂ) + t * I) + 1) *
          ((((-1 / 2 : ℝ) : ℂ) + t * I) + 2)‖)
      ≤ (C * (5 * Real.log (q + 2) * (1 + |t|) ^ (1 / 2 : ℝ))) *
          (x ^ (-(1 / 2) : ℝ) / ((1 + |t|) ^ 2 / 16)) := by
        gcongr
        exact hb.trans (mul_le_mul_of_nonneg_left hlog hC)
    _ = 80 * C * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) *
          ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2) := by
        field_simp; ring

/-- The left line integrand is integrable, for a primitive character. -/
theorem ef_integrable_left {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) : Integrable (fun t : ℝ => Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  obtain ⟨A, _, hA⟩ := ef_left_majorant
  have hg : Integrable (fun t : ℝ =>
      A * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall (hA q χ hχ x hx))
  refine (ef_continuous_F_line χ hx (by norm_num) (by norm_num) (fun t => ?_)).aestronglyMeasurable
  have hs : (((-1 / 2 : ℝ) : ℂ) + t * I) = -1 / 2 + t * I := by push_cast; ring
  rw [hs]; exact no_zero_left_line hχ t

/-- Davenport ch. 17: on `Re s = 2`, `‖L'/L(s, χ)‖ ≤ Σ Λ(n)/n²`. -/
lemma ef_logDeriv_right_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖deriv χ.LFunction ((2 : ℂ) + t * I) / χ.LFunction ((2 : ℂ) + t * I)‖ ≤
      ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
  have hre : 1 < ((2 : ℂ) + t * I).re := by simp
  rw [← norm_neg, ← lseries_chi_vonMangoldt χ hre]
  have hS := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  have hle : ∀ n : ℕ, ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((2 : ℂ) + t * I) n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
    intro n
    refine (LSeries.norm_term_le (g := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) _ ?_).trans
      (le_of_eq ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    · simp only [LSeries.norm_term_eq]
      simp
  have hS' := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hS
  unfold LSeries
  exact (norm_tsum_le_tsum_norm hS').trans (hS'.tsum_le_tsum hle hS)

/-- The right line integrand is integrable. -/
theorem ef_integrable_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => Fchi χ x (((2 : ℝ) : ℂ) + t * I)) := by
  set D := ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖
  have hg : Integrable (fun t : ℝ => D * x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have e2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hz : ∀ t : ℝ, χ.LFunction (((2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t
    refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr ?_) (by simp)
    intro h; have := congr_arg re h; norm_num at this
  refine hg.mono' (ef_continuous_F_line χ hx (by norm_num) (by norm_num) hz).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [ef_norm_Fchi χ hx]
  have hre : (((2 : ℝ) : ℂ) + t * I).re = 2 := by simp
  rw [hre]
  have hdl := ef_logDeriv_right_le χ t
  rw [← e2] at hdl
  have hk := norm_kernelK_le (σ := 2) (by norm_num) t
  rw [norm_div, norm_one] at hk
  have hxp : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx.le _
  calc ‖deriv χ.LFunction (((2 : ℝ) : ℂ) + t * I) / χ.LFunction (((2 : ℝ) : ℂ) + t * I)‖ *
        (x ^ (2 : ℝ) / ‖(((2 : ℝ) : ℂ) + t * I + 1) * (((2 : ℝ) : ℂ) + t * I + 2)‖)
      ≤ D * (x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹) := by
        have hkx : x ^ (2 : ℝ) / ‖(((2 : ℝ) : ℂ) + t * I + 1) * (((2 : ℝ) : ℂ) + t * I + 2)‖ ≤
            x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹ := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hk hxp
        exact mul_le_mul hdl hkx (by positivity) (tsum_nonneg fun n => norm_nonneg _)
    _ = D * x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹ := by ring

/-- Elementary: `log(y + 2)² ≤ 8 y` for `y ≥ 2`. -/
lemma ef_log_sq_le {y : ℝ} (hy : 2 ≤ y) : Real.log (y + 2) ^ 2 ≤ 8 * y := by
  have h0 : 0 ≤ Real.log (y + 2) := Real.log_nonneg (by linarith)
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ y + 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : ((y + 2) ^ (1 / 2 : ℝ)) ^ 2 = y + 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have h3 : Real.log (y + 2) ≤ 2 * (y + 2) ^ (1 / 2 : ℝ) := by
    have : (y + 2) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (y + 2) ^ (1 / 2 : ℝ) := by ring
    linarith
  calc Real.log (y + 2) ^ 2 ≤ (2 * (y + 2) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h3 2
    _ = 4 * (y + 2) := by rw [mul_pow, h2]; ring
    _ ≤ 8 * y := by linarith

/-- Davenport ch. 17 and 19, the exact formula with all zeros in `Re s ≥ -1/2`. -/
theorem explicit_formula_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {x : ℝ} (hx : 0 < x) :
    cesaroChi χ x = (if q = 1 then (x : ℂ) / 6 else 0) - ∑' ρ : Zall χ, zterm χ x ρ +
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I) := by
  obtain ⟨C, hC, hgood⟩ := good_heights hχ
  choose! Tf hTfI hTf using hgood
  set T : ℕ → ℝ := fun n => Tf (max (n : ℝ) 5) with hTdef
  have hT5 : ∀ n : ℕ, (5 : ℝ) ≤ max (n : ℝ) 5 := fun n => le_max_right _ _
  have hTI : ∀ n : ℕ, T n ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1) := fun n => hTfI _ (hT5 n)
  have hTge : ∀ n : ℕ, (n : ℝ) ≤ T n := fun n => (le_max_left _ _).trans (hTI n).1
  have hTpos : ∀ n : ℕ, 0 < T n := fun n => by linarith [(hTI n).1, hT5 n]
  have hTtop : Tendsto T atTop atTop := tendsto_atTop_mono hTge tendsto_natCast_atTop_atTop
  have hTb : ∀ n : ℕ, ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T n, -T n} : Set ℝ),
      χ.LFunction ((σ : ℂ) + y * I) ≠ 0 ∧
        ‖deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)‖ ≤
          C * Real.log (max (n : ℝ) 5 + 2) ^ 2 :=
    fun n => hTf _ (hT5 n)
  -- the border of each rectangle is free of zeros
  have hborder : ∀ n : ℕ, ∀ z ∈ RectangleBorder (⟨-1 / 2, -T n⟩ : ℂ) ⟨2, T n⟩,
      χ.LFunction z ≠ 0 := by
    intro n z hz
    have hzR := rectangleBorder_subset_rectangle _ _ hz
    rw [mem_rect2 (by norm_num) (hTpos n).le] at hzR
    obtain ⟨⟨hr1, hr2⟩, _, _⟩ := hzR
    have hzz : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
    rcases border_cases2 hz with h | h | h | h
    · rw [hzz, h]; exact (hTb n z.re ⟨hr1, hr2⟩ (-T n) (by simp)).1
    · rw [hzz, h]
      have e : (((-1 / 2 : ℝ)) : ℂ) = -1 / 2 := by push_cast; ring
      rw [e]; exact no_zero_left_line hχ z.im
    · rw [hzz, h]; exact (hTb n z.re ⟨hr1, hr2⟩ (T n) (by simp)).1
    · refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr ?_) (by rw [h]; norm_num)
      intro h1; rw [h1] at h; norm_num at h
  have hid : ∀ n : ℕ, (1 / (2 * π) : ℂ) * (efVInt χ x 2 (T n) - efVInt χ x (-1 / 2) (T n)) +
      (1 / (2 * π * I)) * (efHInt χ x (-T n) - efHInt χ x (T n)) =
        (if q = 1 then (x : ℂ) / 6 else 0) -
          ∑ ρ ∈ (zeros_rect_finite hχ (T n)).toFinset, zterm χ x ρ := by
    intro n
    rw [← ef_rect_decomp]
    exact rect_explicit_chi χ hχ hx (hTpos n) (hborder n)
  -- the vertical integrals converge
  have hV2 : Tendsto (fun n => efVInt χ x 2 (T n)) atTop
      (𝓝 (∫ t : ℝ, Fchi χ x (((2 : ℝ) : ℂ) + t * I))) :=
    intervalIntegral_tendsto_integral (ef_integrable_right χ hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hVL : Tendsto (fun n => efVInt χ x (-1 / 2) (T n)) atTop
      (𝓝 (∫ t : ℝ, Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I))) :=
    intervalIntegral_tendsto_integral (ef_integrable_left hχ hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  -- the horizontal integrals tend to 0
  have hHb : ∀ n : ℕ, ‖efHInt χ x (-T n) - efHInt χ x (T n)‖ ≤
      2 * (20 * C * efXb x / max (n : ℝ) 5) := by
    intro n
    have hy5 := hT5 n
    have hlog := ef_log_sq_le (by linarith : (2 : ℝ) ≤ max (n : ℝ) 5)
    have hX := ef_Xb_pos hx
    have hm : 0 < max (n : ℝ) 5 := by linarith
    have hb : ∀ y ∈ ({T n, -T n} : Set ℝ), ‖efHInt χ x y‖ ≤ 20 * C * efXb x / max (n : ℝ) 5 := by
      intro y hy
      have hyabs : |y| = T n := by
        rcases hy with rfl | rfl
        · exact abs_of_pos (hTpos n)
        · rw [abs_neg]; exact abs_of_pos (hTpos n)
      refine (ef_norm_HInt_le χ hx hy5 (hTI n).1 hyabs (fun σ hσ => (hTb n σ hσ y hy).2)).trans ?_
      calc C * Real.log (max (n : ℝ) 5 + 2) ^ 2 * (efXb x / max (n : ℝ) 5 ^ 2) * (5 / 2)
          ≤ C * (8 * max (n : ℝ) 5) * (efXb x / max (n : ℝ) 5 ^ 2) * (5 / 2) := by gcongr
        _ = 20 * C * efXb x / max (n : ℝ) 5 := by field_simp; ring
    calc ‖efHInt χ x (-T n) - efHInt χ x (T n)‖ ≤ ‖efHInt χ x (-T n)‖ + ‖efHInt χ x (T n)‖ :=
          norm_sub_le _ _
      _ ≤ 20 * C * efXb x / max (n : ℝ) 5 + 20 * C * efXb x / max (n : ℝ) 5 :=
          add_le_add (hb _ (by simp)) (hb _ (by simp))
      _ = 2 * (20 * C * efXb x / max (n : ℝ) 5) := by ring
  have hH : Tendsto (fun n => efHInt χ x (-T n) - efHInt χ x (T n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm hHb
    have hmax : Tendsto (fun n : ℕ => max (n : ℝ) 5) atTop atTop :=
      tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := 20 * C * efXb x)).div_atTop hmax
    simpa using this.const_mul 2
  -- the zero sums converge
  classical
  set fs : ℕ → Finset (Zall χ) := fun n =>
    (zeros_rect_finite hχ (T n)).toFinset.subtype (· ∈ Zall χ)
  have hfs : ∀ n : ℕ, ∑ ρ ∈ (zeros_rect_finite hχ (T n)).toFinset, zterm χ x ρ =
      ∑ ρ ∈ fs n, zterm χ x ρ := by
    intro n
    rw [Finset.sum_subtype_of_mem]
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact hρ.1
  have hfs_top : Tendsto fs atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    set M := ∑ ρ ∈ b, |(ρ : ℂ).im|
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop M] with n hn
    intro ρ hρ
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset]
    have him : |(ρ : ℂ).im| ≤ M :=
      Finset.single_le_sum (f := fun ρ : Zall χ => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
    exact ⟨ρ.2, by linarith [hTge n]⟩
  have hS : Tendsto (fun n => ∑ ρ ∈ (zeros_rect_finite hχ (T n)).toFinset, zterm χ x ρ) atTop
      (𝓝 (∑' ρ : Zall χ, zterm χ x ρ)) := by
    simp_rw [hfs]
    exact (summable_zterm hχ hx).hasSum.comp hfs_top
  -- pass to the limit
  have hlim1 : Tendsto (fun n => (1 / (2 * π) : ℂ) *
      (efVInt χ x 2 (T n) - efVInt χ x (-1 / 2) (T n)) +
      (1 / (2 * π * I)) * (efHInt χ x (-T n) - efHInt χ x (T n))) atTop
      (𝓝 ((1 / (2 * π) : ℂ) * ((∫ t : ℝ, Fchi χ x (((2 : ℝ) : ℂ) + t * I)) -
        ∫ t : ℝ, Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I)) + (1 / (2 * π * I)) * 0)) :=
    ((hV2.sub hVL).const_mul _).add (hH.const_mul _)
  have hlim2 : Tendsto (fun n => (1 / (2 * π) : ℂ) *
      (efVInt χ x 2 (T n) - efVInt χ x (-1 / 2) (T n)) +
      (1 / (2 * π * I)) * (efHInt χ x (-T n) - efHInt χ x (T n))) atTop
      (𝓝 ((if q = 1 then (x : ℂ) / 6 else 0) - ∑' ρ : Zall χ, zterm χ x ρ)) := by
    simp_rw [hid]
    exact tendsto_const_nhds.sub hS
  have heq := tendsto_nhds_unique hlim1 hlim2
  have e2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  simp only [e2, mul_zero, add_zero] at heq
  rw [perron_chi χ hx]
  linear_combination heq

/-- The left line integral, uniformly in the primitive character. -/
theorem left_line_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ x : ℝ, 0 < x →
      ‖(1 / (2 * π) : ℂ) * ∫ t : ℝ, Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        C * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := ef_left_majorant
  set I0 := ∫ t : ℝ, (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) with hI0def
  have hI0 : 0 ≤ I0 := integral_nonneg (fun t => by positivity)
  refine ⟨A * I0, by positivity, fun q _ χ hχ x hx => ?_⟩
  have hg : Integrable (fun t : ℝ =>
      A * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  have hint := norm_integral_le_of_norm_le hg (Eventually.of_forall (hA q χ hχ x hx))
  rw [integral_const_mul] at hint
  have hπ : ‖(1 / (2 * π) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  rw [norm_mul]
  calc ‖(1 / (2 * π) : ℂ)‖ * ‖∫ t : ℝ, Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ 1 * ‖∫ t : ℝ, Fchi χ x (((-1 / 2 : ℝ) : ℂ) + t * I)‖ :=
        mul_le_mul_of_nonneg_right hπ (norm_nonneg _)
    _ ≤ A * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) * I0 := by rw [one_mul]; exact hint
    _ = A * I0 * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) := by ring

/-- **The explicit formula for primitive `L(s, χ)`, uniform in `q`.** Davenport ch. 17 and 19
in Cesaro form: for every primitive `χ` mod `q` and `x > 0`, the zero sum converges and
`|S(x, χ) - [q = 1] x/6 + Σ_ρ m(ρ) x^ρ/((ρ+1)(ρ+2))| ≤ C log(q + 2) x^(-1/2)`. -/
theorem explicit_formula_primitive : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ x : ℝ, 0 < x →
      Summable (fun ρ : Zall χ => zterm χ x ρ) ∧
      ‖cesaroChi χ x - (if q = 1 then (x : ℂ) / 6 else 0) + ∑' ρ : Zall χ, zterm χ x ρ‖ ≤
        C * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := left_line_bound
  refine ⟨C, hC, fun q _ χ hχ x hx => ⟨summable_zterm hχ hx, ?_⟩⟩
  rw [explicit_formula_integral χ hχ hx]
  have := h q χ hχ x hx
  convert this using 2
  ring

end LeanLab.Linnik.ExplicitFormula
