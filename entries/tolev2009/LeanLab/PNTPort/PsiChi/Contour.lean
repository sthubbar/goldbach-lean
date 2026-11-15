module

public import LeanLab.PNTPort.PsiChi.SmoothedDirichlet

/-!
# The contour shift for the smoothed `ψ(X, χ)`

Lab proof, unit U-5204, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics,
Davenport ch. 20 with a smooth weight; no cited input. It uses the rectangle API of the ported
StrongPNT files, Apache-2.0, the PrimeNumberTheoremAnd contributors.

`contour_bound`: let `χ ≠ 1`, `X > 3`, `0 < ε < 1`, `σ₀ = 1 + 1/log X`, `1/2 ≤ σ₁ < 1`, `T ≥ 1`.
If `L(s, χ) ≠ 0` on the rectangle `[σ₁, σ₀] × [-T, T]`, `‖L'/L‖ ≤ M₀` on the line `Re s = σ₀`
and `‖L'/L‖ ≤ M` on the left edge and the two horizontal edges, then
`‖∑ χ(n) Λ(n) Smooth1 F ε (n/X)‖ ≤ (C/(2πε)) (2e M₀ X/T + 4π M X^{σ₁} + 3e M X/T²)`,
`C` depending on the smoothing `F` only.
-/

@[expose] public section


set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory

open ArithmeticFunction (vonMangoldt)
open scoped LSeries.notation

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

namespace LeanLab.PNTPort.PsiChi

lemma norm_cpow_real {X : ℝ} (hX : 0 < X) (s : ℂ) : ‖(X : ℂ) ^ s‖ = X ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hX s

lemma normSq_line (σ t : ℝ) : ‖(σ : ℂ) + t * I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp; ring

lemma inv_normSq_le_t (σ t : ℝ) (ht : t ≠ 0) : (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 1 / t ^ 2 := by
  rw [normSq_line, one_div]
  exact inv_anti₀ (by positivity) (by nlinarith)

lemma inv_normSq_le_one_add (σ t : ℝ) (hσ : 1 / 2 ≤ σ) :
    (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 4 * (1 + t ^ 2)⁻¹ := by
  rw [normSq_line]
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have h2 : (1 + t ^ 2) / 4 ≤ σ ^ 2 + t ^ 2 := by nlinarith
  calc (σ ^ 2 + t ^ 2)⁻¹ ≤ ((1 + t ^ 2) / 4)⁻¹ := inv_anti₀ (by positivity) h2
    _ = 4 * (1 + t ^ 2)⁻¹ := by field_simp

/-- A tail bound: `‖∫_{t > T} g‖ ≤ K/T` when `‖g t‖ ≤ K/t²` for `t ≥ T`. -/
lemma tail_le {g : ℝ → ℂ} {K T : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (hg : ∀ t, T ≤ t → ‖g t‖ ≤ K * t ^ (-2 : ℝ)) :
    ‖∫ t in Ioi T, g t‖ ≤ K / T := by
  have hint : IntegrableOn (fun t : ℝ ↦ K * t ^ (-2 : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have h := norm_integral_le_of_norm_le hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ hg t (le_of_lt ht)))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT] at h
  calc _ ≤ _ := h
    _ = K / T := by
      have : T ^ ((-2 : ℝ) + 1) = T⁻¹ := by
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      rw [this]; field_simp; ring

section Chi

variable {N : ℕ} [NeZero N]

lemma integrand_differentiableAt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X ε : ℝ} (hX : 0 < X) (εpos : 0 < ε) (ε_lt_one : ε < 1) {s : ℂ} (hs : 0 < s.re)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (SmoothedChiIntegrand χ SmoothingF ε X) s := by
  have hLd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hD : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    (hLd.analyticAt s).deriv.differentiableAt
  have hM := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
    SmoothingFpos mass_one hs
  have hXs : DifferentiableAt ℂ (fun s : ℂ ↦ (X : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (by exact_mod_cast hX.ne'))
  exact ((hD.neg.div (hLd s) hL).mul hM).mul hXs

lemma integrand_norm_le (χ : DirichletCharacter ℂ N) {SmoothingF : ℝ → ℝ} {ε X : ℝ}
    (hX : 0 < X) {s : ℂ} {C : ℝ}
    (hC : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹) {B : ℝ}
    (hB : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ B) :
    ‖SmoothedChiIntegrand χ SmoothingF ε X s‖ ≤ B * (C * (ε * ‖s‖ ^ 2)⁻¹) * X ^ s.re := by
  simp only [SmoothedChiIntegrand, norm_mul, neg_div, norm_neg]
  rw [norm_cpow_real hX]
  have h0 : 0 ≤ X ^ s.re := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  gcongr

lemma rpow_sigma0 {X : ℝ} (hX : 3 < X) : X ^ (1 + (Real.log X)⁻¹) = Real.exp 1 * X := by
  have hX0 : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.rpow_add hX0, Real.rpow_one, Real.rpow_def_of_pos hX0, mul_inv_cancel₀ hl.ne']
  ring

/-- **The contour bound.** -/
theorem contour_bound {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ X ε σ₁ T M₀ M : ℝ, 3 < X → 0 < ε → ε < 1 → 1 / 2 ≤ σ₁ → σ₁ < 1 → 1 ≤ T →
      0 ≤ M₀ → 0 ≤ M →
      (∀ s ∈ Rectangle ((σ₁ : ℂ) - I * T) (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + I * T),
        DirichletCharacter.LFunction χ s ≠ 0) →
      (∀ t : ℝ, ‖deriv (DirichletCharacter.LFunction χ) (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I) /
        DirichletCharacter.LFunction χ (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤ M₀) →
      (∀ t : ℝ, |t| ≤ T → ‖deriv (DirichletCharacter.LFunction χ) ((σ₁ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ₁ : ℂ) + t * I)‖ ≤ M) →
      (∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 1 + (Real.log X)⁻¹ →
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + T * I)‖ ≤ M ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (-T) * I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + (-T) * I)‖ ≤ M) →
      ‖∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 SmoothingF ε (n / X)‖ ≤
        C / (2 * π * ε) * (2 * Real.exp 1 * M₀ * X / T + 4 * π * M * X ^ σ₁ +
          3 * Real.exp 1 * M * X / T ^ 2) := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  refine ⟨C, Cpos, fun N _ χ hχ X ε σ₁ T M₀ M hX εpos ε1 hσ₁ hσ₁1 hT hM₀0 hM0 hzero hM₀ hleft
    hhor ↦ ?_⟩
  set σ₀ : ℝ := 1 + (Real.log X)⁻¹ with hσ₀
  have hX0 : 0 < X := by linarith
  have log_gt : 1 < Real.log X := logt_gt_one hX.le
  have hσ₀1 : 1 < σ₀ := by
    have : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hσ₀2 : σ₀ ≤ 2 := by
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  have hXσ₀ : X ^ σ₀ = Real.exp 1 * X := rpow_sigma0 hX
  set f := SmoothedChiIntegrand χ SmoothingF ε X with hf
  have hT0 : 0 < T := by linarith
  -- the Mellin bound in the form used below
  have hMel : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ :=
    fun s h1 h2 ↦ hC (1 / 2) (by norm_num) s h1 h2 ε εpos ε1
  have re_line : ∀ σ t : ℝ, ((σ : ℂ) + t * I).re = σ := by intro σ t; simp
  have im_line : ∀ σ t : ℝ, ((σ : ℂ) + t * I).im = t := by intro σ t; simp
  -- pointwise bound on the line σ₀
  have hline : ∀ t : ℝ, ‖f ((σ₀ : ℂ) + t * I)‖ ≤
      M₀ * C * ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹ * (Real.exp 1 * X) := by
    intro t
    have h := integrand_norm_le χ hX0 (hMel _ (by rw [re_line]; linarith) (by rw [re_line]; linarith))
      (hM₀ t)
    rw [re_line, hXσ₀] at h
    calc _ ≤ _ := h
      _ = _ := by rw [mul_inv]; ring
  have hLne : ∀ t : ℝ, DirichletCharacter.LFunction χ ((σ₀ : ℂ) + t * I) ≠ 0 := fun t ↦
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [re_line]; linarith)
  have hcont : Continuous fun t : ℝ ↦ f ((σ₀ : ℂ) + t * I) := by
    rw [continuous_iff_continuousAt]; intro t
    have hd := integrand_differentiableAt hχ diffSmoothingF SmoothingFpos suppSmoothingF mass_one
      hX0 εpos ε1 (s := (σ₀ : ℂ) + t * I) (by rw [re_line]; linarith) (hLne t)
    exact ContinuousAt.comp (g := f) hd.continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ ↦ (σ₀ : ℂ) + t * I) t)
  have hint : Integrable fun t : ℝ ↦ f ((σ₀ : ℂ) + t * I) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul
      (M₀ * C * ε⁻¹ * 4 * (Real.exp 1 * X))) hcont.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    refine (hline t).trans ?_
    have h4 := inv_normSq_le_one_add σ₀ t (by linarith)
    have hk : 0 ≤ M₀ * C * ε⁻¹ := by positivity
    have hk2 : 0 ≤ Real.exp 1 * X := by positivity
    calc M₀ * C * ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹ * (Real.exp 1 * X)
        ≤ M₀ * C * ε⁻¹ * (4 * (1 + t ^ 2)⁻¹) * (Real.exp 1 * X) := by gcongr
      _ = _ := by ring
  have hσ₁σ₀ : σ₁ ≤ σ₀ := by linarith
  have hX1 : 1 ≤ X := by linarith
  -- holomorphy on the rectangle and Cauchy
  have hholo : HolomorphicOn f (Rectangle ((σ₁ : ℂ) - I * T) ((σ₀ : ℂ) + I * T)) := by
    intro s hs
    have hs' := hs
    simp only [Rectangle, Complex.mem_reProdIm] at hs'
    have hre : σ₁ ≤ s.re := by
      have h1 := hs'.1
      simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero, sub_zero,
        add_re, one_mul, sub_self, add_zero] at h1
      rw [Set.uIcc_of_le hσ₁σ₀] at h1
      exact h1.1
    exact (integrand_differentiableAt hχ diffSmoothingF SmoothingFpos suppSmoothingF mass_one
      hX0 εpos ε1 (by linarith) (hzero s hs)).differentiableWithinAt
  have hrect := HolomorphicOn.vanishesOnRectangle hholo subset_rfl
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul,
    mul_zero, sub_zero, add_re, one_mul, sub_self, add_zero, sub_im, mul_im, add_im, zero_add,
    zero_sub] at hrect
  have hsplit := verticalIntegral_split_three (f := f) (σ := σ₀) (-T) T hint
  have hV : VerticalIntegral f σ₀ =
      I • (∫ t in Iic (-T), f (σ₀ + t * I)) + VIntegral f σ₁ (-T) T -
        HIntegral f σ₁ σ₀ (-T) + HIntegral f σ₁ σ₀ T + I • ∫ t in Ici T, f (σ₀ + t * I) := by
    rw [hsplit]
    have : VIntegral f σ₀ (-T) T =
        VIntegral f σ₁ (-T) T - HIntegral f σ₁ σ₀ (-T) + HIntegral f σ₁ σ₀ T := by
      linear_combination hrect
    rw [this]; abel
  -- the tails
  set K := M₀ * C * ε⁻¹ * (Real.exp 1 * X) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ t : ℝ, 0 < t → ‖f ((σ₀ : ℂ) + t * I)‖ ≤ K * t ^ (-2 : ℝ) ∧
      ‖f ((σ₀ : ℂ) + (-t) * I)‖ ≤ K * t ^ (-2 : ℝ) := by
    intro t ht
    have e : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
      rw [Real.rpow_neg ht.le, one_div]; norm_cast
    have hk : 0 ≤ M₀ * C * ε⁻¹ := by positivity
    have hk2 : 0 ≤ Real.exp 1 * X := by positivity
    constructor
    · refine (hline t).trans ?_
      have := inv_normSq_le_t σ₀ t ht.ne'
      rw [e, hK]
      calc M₀ * C * ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹ * (Real.exp 1 * X)
          ≤ M₀ * C * ε⁻¹ * (1 / t ^ 2) * (Real.exp 1 * X) := by gcongr
        _ = _ := by ring
    · have h1 := hline (-t)
      push_cast at h1
      refine h1.trans ?_
      have := inv_normSq_le_t σ₀ (-t) (by linarith)
      push_cast at this
      rw [e, hK]
      calc M₀ * C * ε⁻¹ * (‖(σ₀ : ℂ) + -(t : ℂ) * I‖ ^ 2)⁻¹ * (Real.exp 1 * X)
          ≤ M₀ * C * ε⁻¹ * (1 / (-t) ^ 2) * (Real.exp 1 * X) := by gcongr
        _ = _ := by ring
  have htail1 : ‖∫ t in Ici T, f (σ₀ + t * I)‖ ≤ K / T := by
    rw [integral_Ici_eq_integral_Ioi]
    exact tail_le hT0 hK0 fun t ht ↦ (hpt t (by linarith)).1
  have htail2 : ‖∫ t in Iic (-T), f (σ₀ + t * I)‖ ≤ K / T := by
    rw [← integral_comp_neg_Ioi]
    refine tail_le hT0 hK0 fun t ht ↦ ?_
    have := (hpt t (by linarith)).2
    push_cast at this ⊢
    exact this
  -- the left edge
  set KL := M * C * ε⁻¹ * 4 * X ^ σ₁ with hKL
  have hKL0 : 0 ≤ KL := by positivity
  have hleft' : ‖VIntegral f σ₁ (-T) T‖ ≤ KL * π := by
    simp only [VIntegral, norm_smul, Complex.norm_I, one_mul]
    have hb : ∀ᵐ t, t ∈ Ioc (-T) T → ‖f ((σ₁ : ℂ) + t * I)‖ ≤ KL * (1 + t ^ 2)⁻¹ := by
      refine Eventually.of_forall fun t ht ↦ ?_
      have habs : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have h := integrand_norm_le χ hX0
        (hMel _ (by rw [re_line]; linarith) (by rw [re_line]; linarith)) (hleft t habs)
      rw [re_line] at h
      refine h.trans ?_
      have h4 := inv_normSq_le_one_add σ₁ t hσ₁
      have hk : 0 ≤ M * C * ε⁻¹ := by positivity
      have hXs : 0 ≤ X ^ σ₁ := by positivity
      rw [hKL, mul_inv]
      calc M * (C * (ε⁻¹ * (‖(σ₁ : ℂ) + t * I‖ ^ 2)⁻¹)) * X ^ σ₁
          = M * C * ε⁻¹ * (‖(σ₁ : ℂ) + t * I‖ ^ 2)⁻¹ * X ^ σ₁ := by ring
        _ ≤ M * C * ε⁻¹ * (4 * (1 + t ^ 2)⁻¹) * X ^ σ₁ := by gcongr
        _ = _ := by ring
    have hii : IntervalIntegrable (fun t : ℝ ↦ KL * (1 + t ^ 2)⁻¹) volume (-T) T :=
      (integrable_inv_one_add_sq.const_mul KL).intervalIntegrable
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) hb hii).trans ?_
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_univ_inv_one_add_sq,
      ← integral_const_mul]
    exact setIntegral_le_integral (integrable_inv_one_add_sq.const_mul KL)
      (Eventually.of_forall fun t ↦ by positivity)
  -- the horizontal edges
  set KH := M * C * ε⁻¹ * (T ^ 2)⁻¹ * (Real.exp 1 * X) with hKH
  have hhor' : ∀ y : ℝ, (y = T ∨ y = -T) → ‖HIntegral f σ₁ σ₀ y‖ ≤ KH * (3 / 2) := by
    intro y hy
    simp only [HIntegral]
    have hb : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖f ((x : ℂ) + y * I)‖ ≤ KH := by
      intro x hx
      rw [Set.uIoc_of_le hσ₁σ₀] at hx
      have hM' : ‖deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I) /
          DirichletCharacter.LFunction χ ((x : ℂ) + y * I)‖ ≤ M := by
        rcases hy with rfl | rfl
        · exact (hhor x hx.1.le hx.2).1
        · have := (hhor x hx.1.le hx.2).2
          push_cast; exact this
      have h := integrand_norm_le χ hX0
        (hMel _ (by rw [re_line]; linarith [hx.1]) (by rw [re_line]; linarith [hx.2])) hM'
      rw [re_line] at h
      refine h.trans ?_
      have hy0 : y ≠ 0 := by rcases hy with rfl | rfl <;> [exact hT0.ne'; linarith]
      have h4 := inv_normSq_le_t x y hy0
      have hy2 : y ^ 2 = T ^ 2 := by rcases hy with rfl | rfl <;> ring
      rw [hy2] at h4
      have hXx : X ^ x ≤ Real.exp 1 * X := by
        rw [← hXσ₀]; exact Real.rpow_le_rpow_of_exponent_le hX1 hx.2
      have hk : 0 ≤ M * C * ε⁻¹ := by positivity
      rw [hKH, mul_inv]
      calc M * (C * (ε⁻¹ * (‖(x : ℂ) + y * I‖ ^ 2)⁻¹)) * X ^ x
          = M * C * ε⁻¹ * (‖(x : ℂ) + y * I‖ ^ 2)⁻¹ * X ^ x := by ring
        _ ≤ M * C * ε⁻¹ * (1 / T ^ 2) * (Real.exp 1 * X) := by gcongr
        _ = _ := by ring
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have hKH0 : 0 ≤ KH := by positivity
    have : |σ₀ - σ₁| ≤ 3 / 2 := by rw [abs_of_nonneg (by linarith)]; linarith
    exact mul_le_mul_of_nonneg_left this hKH0
  -- assembly
  have hS := smoothedChebyshevChi_eq χ diffSmoothingF SmoothingFpos suppSmoothingF mass_one hX
    εpos ε1
  rw [← hS]
  simp only [VerticalIntegral']
  rw [norm_smul, hV]
  have hnorm : ‖(1 / (2 * π * I) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  have htot : ‖I • (∫ t in Iic (-T), f (σ₀ + t * I)) + VIntegral f σ₁ (-T) T -
      HIntegral f σ₁ σ₀ (-T) + HIntegral f σ₁ σ₀ T + I • ∫ t in Ici T, f (σ₀ + t * I)‖ ≤
      K / T + KL * π + KH * (3 / 2) + KH * (3 / 2) + K / T := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ (hhor' T (Or.inl rfl)))
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hhor' (-T) (Or.inr rfl)))
      refine (norm_add_le _ _).trans (add_le_add ?_ hleft')
      rw [norm_smul, Complex.norm_I, one_mul]; exact htail2
    · rw [norm_smul, Complex.norm_I, one_mul]; exact htail1
  have hpi : 0 < 2 * π := by positivity
  calc 1 / (2 * π) * ‖_‖ ≤ 1 / (2 * π) * (K / T + KL * π + KH * (3 / 2) + KH * (3 / 2) + K / T) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = _ := by
        rw [hK, hKL, hKH]
        field_simp
        ring

end Chi

end LeanLab.PNTPort.PsiChi
