module

public import LeanLab.HardyLittlewood1923.U1503Mellin
public import LeanLab.PNTPort.PsiChi.Contour

/-!
AI-written Lean code, Claude, 2026-10-23, CLOUD run 20261023T1343Z-19109, unit U-1503, paper P0004.

# The contour shift for the smoothed `ψ(X, χ)` with the Mellin bound `C/‖s‖`

Known mathematics, Davenport ch. 17 to 20 with a smooth weight, no cited input. It reuses the
rectangle API and `SmoothedChebyshevPull1` of the ported StrongPNT files, Apache-2.0, the
PrimeNumberTheoremAnd contributors, and the lab's PsiChi/Contour.lean, whose `contour_bound`
carries a factor `1/ε` on every edge. Here the left edge and the horizontal edges use U1503Mellin's
`‖𝓜 (Smooth1 F ε)(s)‖ ≤ C₁/‖s‖`, so only the two tails of the right line keep `1/ε`.

* `edge_bounds`: for any `Lf : ℂ → ℂ`, bounds on the five pieces of the contour for the
  integrand `-Lf'/Lf(s) 𝓜(s) X^s` from `‖Lf'/Lf‖ ≤ M₀` on `Re s = 1 + 1/log X` and `≤ M` on
  `[σ₁, 1 + 1/log X] × [-T, T]` minus `{1}`.
* `contour_bound_inv`: `χ ≠ 1`, no zero of `L(s, χ)` on the rectangle:
  `‖∑ χ(n) Λ(n) Smooth1 F ε (n/X)‖ ≤ C (M₀ X/(εT) + M X^{σ₁} log(1 + T) + M X/T)`.
* `contour_bound_zeta`: no zero of `ζ` on `[σ₁, 2] × [-T, T]` minus `{1}`:
  `‖SmoothedChebyshev F ε X - 𝓜(Smooth1 F ε)(1) X‖ ≤` the same right side.
-/

@[expose] public section

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

namespace LeanLab.HardyLittlewood1923.U1503

open LeanLab.PNTPort.PsiChi (tail_le inv_normSq_le_t rpow_sigma0 integrand_differentiableAt
  SmoothedChiIntegrand smoothedChebyshevChi_eq)

/-- The integrand `-Lf'/Lf(s) 𝓜(Smooth1 F ε)(s) X^s` for an arbitrary `Lf`. -/
noncomputable abbrev IGr (Lf : ℂ → ℂ) (SmoothingF : ℝ → ℝ) (ε X : ℝ) : ℂ → ℂ :=
  fun s ↦ -deriv Lf s / Lf s * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

lemma norm_IGr_le (Lf : ℂ → ℂ) (SmoothingF : ℝ → ℝ) {ε X : ℝ} (hX : 0 < X) (s : ℂ) {B D : ℝ}
    (h1 : ‖deriv Lf s / Lf s‖ ≤ B) (h2 : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D) :
    ‖IGr Lf SmoothingF ε X s‖ ≤ B * D * X ^ s.re := by
  simp only [IGr, norm_mul, neg_div, norm_neg, norm_cpow_eq_rpow_re_of_pos hX]
  have hB : 0 ≤ B := (norm_nonneg _).trans h1
  have hX0 : 0 ≤ X ^ s.re := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) hB) hX0

lemma tails_le {g : ℝ → ℂ} {K T : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (hg : ∀ t : ℝ, t ≠ 0 → ‖g t‖ ≤ K * (1 / t ^ 2)) :
    ‖∫ t in Ici T, g t‖ ≤ K / T ∧ ‖∫ t in Iic (-T), g t‖ ≤ K / T := by
  have e : ∀ t : ℝ, 0 < t → t ^ (-2 : ℝ) = 1 / t ^ 2 := by
    intro t ht; rw [Real.rpow_neg ht.le, one_div]; norm_cast
  constructor
  · rw [integral_Ici_eq_integral_Ioi]
    exact tail_le hT hK fun t ht ↦ by rw [e t (by linarith)]; exact hg t (by linarith)
  · rw [← integral_comp_neg_Ioi]
    refine tail_le hT hK fun t ht ↦ ?_
    rw [e t (by linarith)]
    have := hg (-t) (by linarith)
    rwa [neg_sq] at this

lemma horiz_le {g : ℝ → ℂ} {a b H W : ℝ} (hab : a ≤ b) (hW : b - a ≤ W) (hH : 0 ≤ H)
    (hg : ∀ x : ℝ, a ≤ x → x ≤ b → ‖g x‖ ≤ H) : ‖∫ x in a..b, g x‖ ≤ H * W := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := g) (C := H)
    (fun x hx ↦ by rw [Set.uIoc_of_le hab] at hx; exact hg x hx.1.le hx.2)
  rw [abs_of_nonneg (by linarith)] at h
  exact h.trans (mul_le_mul_of_nonneg_left hW hH)

/-- **Bounds for the five pieces of the contour.** -/
theorem edge_bounds {SmoothingF : ℝ → ℝ} (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (Lf : ℂ → ℂ) (X ε σ₁ T M₀ M : ℝ), 3 < X → 0 < ε → ε < 1 →
      1 / 2 ≤ σ₁ → σ₁ < 1 → 1 ≤ T → 0 ≤ M₀ → 0 ≤ M →
      (∀ t : ℝ, ‖deriv Lf (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I) /
        Lf (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤ M₀) →
      (∀ t : ℝ, |t| ≤ T → ‖deriv Lf ((σ₁ : ℂ) + t * I) / Lf ((σ₁ : ℂ) + t * I)‖ ≤ M) →
      (∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 1 + (Real.log X)⁻¹ →
        ‖deriv Lf ((σ : ℂ) + T * I) / Lf ((σ : ℂ) + T * I)‖ ≤ M ∧
        ‖deriv Lf ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) / Lf ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ M) →
      ‖∫ t in Ici T, IGr Lf SmoothingF ε X (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤
          C₂ * Real.exp 1 * M₀ * X / (ε * T) ∧
      ‖∫ t in Iic (-T), IGr Lf SmoothingF ε X (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤
          C₂ * Real.exp 1 * M₀ * X / (ε * T) ∧
      ‖∫ t in (-T)..T, IGr Lf SmoothingF ε X ((σ₁ : ℂ) + t * I)‖ ≤
          8 * (M * C₁ * X ^ σ₁) * Real.log (1 + T) ∧
      ‖∫ x in σ₁..(1 + (Real.log X)⁻¹), IGr Lf SmoothingF ε X ((x : ℂ) + T * I)‖ ≤
          M * C₁ * Real.exp 1 * X / T * (3 / 2) ∧
      ‖∫ x in σ₁..(1 + (Real.log X)⁻¹), IGr Lf SmoothingF ε X ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
          M * C₁ * Real.exp 1 * X / T * (3 / 2) := by
  obtain ⟨C₁, hC₁, hM1⟩ := mellin_smooth1_le_inv diffSmoothingF suppSmoothingF
  obtain ⟨C₂, hC₂, hM2⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  refine ⟨C₁, C₂, hC₁, hC₂, fun Lf X ε σ₁ T M₀ M hX εpos ε1 hσ₁ hσ₁1 hT hM₀0 hM0 hright hleft hhor ↦ ?_⟩
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
  have hT0 : 0 < T := by linarith
  have re_line : ∀ σ t : ℝ, ((σ : ℂ) + t * I).re = σ := by intro σ t; simp
  have im_line : ∀ σ t : ℝ, ((σ : ℂ) + t * I).im = t := by intro σ t; simp
  -- the tails
  set K := M₀ * (C₂ * ε⁻¹) * (Real.exp 1 * X) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ t : ℝ, t ≠ 0 →
      ‖IGr Lf SmoothingF ε X ((σ₀ : ℂ) + t * I)‖ ≤ K * (1 / t ^ 2) := by
    intro t ht
    have hm := hM2 (1 / 2) (by norm_num) ((σ₀ : ℂ) + t * I) (by rw [re_line]; linarith)
      (by rw [re_line]; linarith) ε εpos ε1
    have h := norm_IGr_le Lf SmoothingF hX0 _ (hright t) hm
    rw [re_line, hXσ₀] at h
    refine h.trans ?_
    have h4 := inv_normSq_le_t σ₀ t ht
    rw [hK, mul_inv]
    have hk : 0 ≤ M₀ * C₂ * ε⁻¹ := by positivity
    calc M₀ * (C₂ * (ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹)) * (Real.exp 1 * X)
        = M₀ * C₂ * ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹ * (Real.exp 1 * X) := by ring
      _ ≤ M₀ * C₂ * ε⁻¹ * (1 / t ^ 2) * (Real.exp 1 * X) := by gcongr
      _ = _ := by ring
  obtain ⟨ht1, ht2⟩ := tails_le hT0 hK0 hpt
  have hKT : K / T = C₂ * Real.exp 1 * M₀ * X / (ε * T) := by
    rw [hK]; field_simp
  rw [hKT] at ht1 ht2
  refine ⟨ht1, ht2, ?_, ?_, ?_⟩
  -- the left edge
  · refine norm_integral_line_le hσ₁ hT0.le (by positivity) fun t ht ↦ ?_
    have hm := hM1 ε εpos ε1 ((σ₁ : ℂ) + t * I) (by rw [re_line]; linarith)
      (by rw [re_line]; linarith)
    have h := norm_IGr_le Lf SmoothingF hX0 _ (hleft t ht) hm
    rw [re_line] at h
    calc _ ≤ _ := h
      _ = M * C₁ * X ^ σ₁ * ‖(σ₁ : ℂ) + t * I‖⁻¹ := by ring
  -- the horizontal edges
  all_goals
    refine horiz_le (by linarith) (by linarith) (by positivity) fun x hx1 hx2 ↦ ?_
  · have hm := hM1 ε εpos ε1 ((x : ℂ) + T * I) (by rw [re_line]; linarith)
      (by rw [re_line]; linarith)
    have h := norm_IGr_le Lf SmoothingF hX0 _ (hhor x hx1 hx2).1 hm
    rw [re_line] at h
    refine h.trans ?_
    have hT' : T ≤ ‖(x : ℂ) + T * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + T * I)
      rw [im_line, abs_of_pos hT0] at this; exact this
    have hinv : ‖(x : ℂ) + T * I‖⁻¹ ≤ T⁻¹ := inv_anti₀ hT0 hT'
    have hXx : X ^ x ≤ Real.exp 1 * X := by
      rw [← hXσ₀]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hx2
    have hk : 0 ≤ M * C₁ := by positivity
    calc M * (C₁ * ‖(x : ℂ) + T * I‖⁻¹) * X ^ x ≤ M * (C₁ * T⁻¹) * (Real.exp 1 * X) := by
          gcongr
      _ = M * C₁ * Real.exp 1 * X / T := by ring
  · have hm := hM1 ε εpos ε1 ((x : ℂ) + ((-T : ℝ) : ℂ) * I) (by rw [re_line]; linarith)
      (by rw [re_line]; linarith)
    have h := norm_IGr_le Lf SmoothingF hX0 _ (hhor x hx1 hx2).2 hm
    rw [re_line] at h
    refine h.trans ?_
    have hT' : T ≤ ‖(x : ℂ) + ((-T : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + ((-T : ℝ) : ℂ) * I)
      rw [im_line, abs_neg, abs_of_pos hT0] at this; exact this
    have hinv : ‖(x : ℂ) + ((-T : ℝ) : ℂ) * I‖⁻¹ ≤ T⁻¹ := inv_anti₀ hT0 hT'
    have hXx : X ^ x ≤ Real.exp 1 * X := by
      rw [← hXσ₀]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hx2
    have hk : 0 ≤ M * C₁ := by positivity
    calc M * (C₁ * ‖(x : ℂ) + ((-T : ℝ) : ℂ) * I‖⁻¹) * X ^ x ≤
          M * (C₁ * T⁻¹) * (Real.exp 1 * X) := by gcongr
      _ = M * C₁ * Real.exp 1 * X / T := by ring

lemma norm_two_pi_I : ‖(1 / (2 * π * I) : ℂ)‖ = 1 / (2 * π) := by
  rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

lemma one_div_two_pi_le : 1 / (2 * π) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]

/-- The final arithmetic: five pieces to `C (M₀X/(εT) + M X^{σ₁} log(1 + T) + M X/T)`. -/
lemma five_le {C₁ C₂ M₀ M X ε T σ₁ a1 a2 a3 a4 a5 : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M) (hX : 0 < X) (hε : 0 < ε) (hT : 0 < T) (hl : 0 ≤ Real.log (1 + T))
    (h1 : a1 ≤ C₂ * Real.exp 1 * M₀ * X / (ε * T)) (h2 : a2 ≤ C₂ * Real.exp 1 * M₀ * X / (ε * T))
    (h3 : a3 ≤ 8 * (M * C₁ * X ^ σ₁) * Real.log (1 + T))
    (h4 : a4 ≤ M * C₁ * Real.exp 1 * X / T * (3 / 2))
    (h5 : a5 ≤ M * C₁ * Real.exp 1 * X / T * (3 / 2)) :
    1 / (2 * π) * (a1 + a2 + a3 + a4 + a5) ≤
      (2 * C₂ * Real.exp 1 + 8 * C₁ + 3 * C₁ * Real.exp 1) *
        (M₀ * X / (ε * T) + M * X ^ σ₁ * Real.log (1 + T) + M * X / T) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set A := M₀ * X / (ε * T) with hA
  set B := M * X ^ σ₁ * Real.log (1 + T) with hB
  set D := M * X / T with hD
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  have e1 : C₂ * Real.exp 1 * M₀ * X / (ε * T) = C₂ * Real.exp 1 * A := by rw [hA]; ring
  have e3 : 8 * (M * C₁ * X ^ σ₁) * Real.log (1 + T) = 8 * C₁ * B := by rw [hB]; ring
  have e4 : M * C₁ * Real.exp 1 * X / T * (3 / 2) = 3 / 2 * C₁ * Real.exp 1 * D := by
    rw [hD]; ring
  rw [e1] at h1 h2; rw [e3] at h3; rw [e4] at h4 h5
  have hsum : a1 + a2 + a3 + a4 + a5 ≤ 2 * C₂ * Real.exp 1 * A + 8 * C₁ * B +
      3 * C₁ * Real.exp 1 * D := by linarith
  have hpos : 0 ≤ 2 * C₂ * Real.exp 1 * A + 8 * C₁ * B + 3 * C₁ * Real.exp 1 * D := by positivity
  have hle : 2 * C₂ * Real.exp 1 * A + 8 * C₁ * B + 3 * C₁ * Real.exp 1 * D ≤
      (2 * C₂ * Real.exp 1 + 8 * C₁ + 3 * C₁ * Real.exp 1) * (A + B + D) := by
    nlinarith [mul_nonneg (mul_nonneg hC₂.le he.le) hB0, mul_nonneg (mul_nonneg hC₂.le he.le) hD0,
      mul_nonneg hC₁.le hA0, mul_nonneg hC₁.le hD0, mul_nonneg (mul_nonneg hC₁.le he.le) hA0,
      mul_nonneg (mul_nonneg hC₁.le he.le) hB0]
  have hsum0 : 0 ≤ a1 + a2 + a3 + a4 + a5 ∨ a1 + a2 + a3 + a4 + a5 < 0 := le_or_gt _ _
  have h2pi := one_div_two_pi_le
  have h2pi0 : 0 ≤ 1 / (2 * π) := by positivity
  rcases hsum0 with h | h
  · calc 1 / (2 * π) * (a1 + a2 + a3 + a4 + a5) ≤ 1 * (a1 + a2 + a3 + a4 + a5) :=
          mul_le_mul_of_nonneg_right h2pi h
      _ ≤ _ := by linarith
  · have : 1 / (2 * π) * (a1 + a2 + a3 + a4 + a5) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h2pi0 h.le
    have : 0 ≤ (2 * C₂ * Real.exp 1 + 8 * C₁ + 3 * C₁ * Real.exp 1) * (A + B + D) := by
      positivity
    linarith

section Chi

variable {N : ℕ} [NeZero N]

/-- **The contour bound for `χ ≠ 1` with the Mellin bound `C/‖s‖`.** -/
theorem contour_bound_inv {SmoothingF : ℝ → ℝ}
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
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ M) →
      ‖∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 SmoothingF ε (n / X)‖ ≤
        C * (M₀ * X / (ε * T) + M * X ^ σ₁ * Real.log (1 + T) + M * X / T) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hE⟩ := edge_bounds diffSmoothingF suppSmoothingF
  refine ⟨2 * C₂ * Real.exp 1 + 8 * C₁ + 3 * C₁ * Real.exp 1, by positivity,
    fun N _ χ hχ X ε σ₁ T M₀ M hX εpos ε1 hσ₁ hσ₁1 hT hM₀0 hM0 hzero hM₀ hleft hhor ↦ ?_⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := hE (DirichletCharacter.LFunction χ) X ε σ₁ T M₀ M hX εpos ε1
    hσ₁ hσ₁1 hT hM₀0 hM0 hM₀ hleft hhor
  set σ₀ : ℝ := 1 + (Real.log X)⁻¹ with hσ₀
  have hX0 : 0 < X := by linarith
  have log_gt : 1 < Real.log X := logt_gt_one hX.le
  have hσ₀1 : 1 < σ₀ := by
    have : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hT0 : 0 < T := by linarith
  set f := SmoothedChiIntegrand χ SmoothingF ε X with hf
  have hfI : f = IGr (DirichletCharacter.LFunction χ) SmoothingF ε X := rfl
  have re_line : ∀ σ t : ℝ, ((σ : ℂ) + t * I).re = σ := by intro σ t; simp
  -- integrability on the right line, from the old `1/(ε‖s‖²)` Mellin bound
  obtain ⟨C₃, hC₃, hC₃b⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  have hline : ∀ t : ℝ, ‖f ((σ₀ : ℂ) + t * I)‖ ≤
      M₀ * (C₃ * (ε * ‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹) * (Real.exp 1 * X) := by
    intro t
    have hm := hC₃b (1 / 2) (by norm_num) ((σ₀ : ℂ) + t * I) (by rw [re_line]; linarith)
      (by rw [re_line]; have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt; linarith)
      ε εpos ε1
    have h := norm_IGr_le (DirichletCharacter.LFunction χ) SmoothingF hX0 _ (hM₀ t) hm
    rw [re_line, rpow_sigma0 hX] at h
    exact h
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
      (M₀ * C₃ * ε⁻¹ * 4 * (Real.exp 1 * X))) hcont.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    refine (hline t).trans ?_
    have h4 := LeanLab.PNTPort.PsiChi.inv_normSq_le_one_add σ₀ t (by linarith)
    have hk : 0 ≤ M₀ * C₃ * ε⁻¹ := by positivity
    have hk2 : 0 ≤ Real.exp 1 * X := by positivity
    rw [mul_inv]
    calc M₀ * (C₃ * (ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹)) * (Real.exp 1 * X)
        = M₀ * C₃ * ε⁻¹ * (‖(σ₀ : ℂ) + t * I‖ ^ 2)⁻¹ * (Real.exp 1 * X) := by ring
      _ ≤ M₀ * C₃ * ε⁻¹ * (4 * (1 + t ^ 2)⁻¹) * (Real.exp 1 * X) := by gcongr
      _ = _ := by ring
  have hσ₁σ₀ : σ₁ ≤ σ₀ := by linarith
  -- holomorphy on the rectangle and Cauchy
  have hholo : HolomorphicOn f (Rectangle ((σ₁ : ℂ) - I * T) ((σ₀ : ℂ) + I * T)) := by
    intro s hs
    have hs' := hs
    simp only [Rectangle, Complex.mem_reProdIm] at hs'
    have hre : σ₁ ≤ s.re := by
      have h1 := hs'.1
      simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero, sub_zero,
        add_re, sub_self, add_zero] at h1
      rw [Set.uIcc_of_le hσ₁σ₀] at h1
      exact h1.1
    exact (integrand_differentiableAt hχ diffSmoothingF SmoothingFpos suppSmoothingF mass_one
      hX0 εpos ε1 (by linarith) (hzero s hs)).differentiableWithinAt
  have hrect0 := HolomorphicOn.vanishesOnRectangle hholo subset_rfl
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul,
    mul_zero, sub_zero, add_re, one_mul, sub_self, add_zero, sub_im, mul_im, add_im, zero_add,
    zero_sub] at hrect0
  have hsplit := verticalIntegral_split_three (f := f) (σ := σ₀) (-T) T hint
  have hV : VerticalIntegral f σ₀ =
      I • (∫ t in Iic (-T), f (σ₀ + t * I)) + VIntegral f σ₁ (-T) T -
        HIntegral f σ₁ σ₀ (-T) + HIntegral f σ₁ σ₀ T + I • ∫ t in Ici T, f (σ₀ + t * I) := by
    rw [hsplit]
    have : VIntegral f σ₀ (-T) T =
        VIntegral f σ₁ (-T) T - HIntegral f σ₁ σ₀ (-T) + HIntegral f σ₁ σ₀ T := by
      linear_combination hrect0
    rw [this]; abel
  -- assembly
  have hS := smoothedChebyshevChi_eq χ diffSmoothingF SmoothingFpos suppSmoothingF mass_one hX
    εpos ε1
  rw [← hS]
  simp only [VerticalIntegral']
  rw [norm_smul, hV, norm_two_pi_I]
  have htot : ‖I • (∫ t in Iic (-T), f (σ₀ + t * I)) + VIntegral f σ₁ (-T) T -
      HIntegral f σ₁ σ₀ (-T) + HIntegral f σ₁ σ₀ T + I • ∫ t in Ici T, f (σ₀ + t * I)‖ ≤
      ‖∫ t in Iic (-T), f (σ₀ + t * I)‖ + ‖∫ t in (-T)..T, f (σ₁ + t * I)‖ +
        ‖HIntegral f σ₁ σ₀ (-T)‖ + ‖HIntegral f σ₁ σ₀ T‖ + ‖∫ t in Ici T, f (σ₀ + t * I)‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Complex.norm_I, one_mul]
      · rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    · rw [norm_smul, Complex.norm_I, one_mul]
  have hb5 : ‖HIntegral f σ₁ σ₀ (-T)‖ ≤ M * C₁ * Real.exp 1 * X / T * (3 / 2) := b5
  have hb4 : ‖HIntegral f σ₁ σ₀ T‖ ≤ M * C₁ * Real.exp 1 * X / T * (3 / 2) := b4
  have hfin := five_le hC₁ hC₂ hM₀0 hM0 hX0 εpos hT0 (Real.log_nonneg (by linarith)) b2 b1 b3
    hb5 hb4
  exact (mul_le_mul_of_nonneg_left htot (by positivity)).trans (Eq.trans_le (by ring) hfin)

end Chi

/-- **The contour bound for `ζ`, with the pole at `1`.** -/
theorem contour_bound_zeta {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ε σ₁ T M₀ M : ℝ, 3 < X → 0 < ε → ε < 1 → 1 / 2 ≤ σ₁ → σ₁ < 1 →
      1 ≤ T → 0 ≤ M₀ → 0 ≤ M →
      (∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → |s.im| ≤ T → s ≠ 1 → riemannZeta s ≠ 0) →
      (∀ t : ℝ, ‖deriv riemannZeta (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I) /
        riemannZeta (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤ M₀) →
      (∀ t : ℝ, |t| ≤ T →
        ‖deriv riemannZeta ((σ₁ : ℂ) + t * I) / riemannZeta ((σ₁ : ℂ) + t * I)‖ ≤ M) →
      (∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 1 + (Real.log X)⁻¹ →
        ‖deriv riemannZeta ((σ : ℂ) + T * I) / riemannZeta ((σ : ℂ) + T * I)‖ ≤ M ∧
        ‖deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
          riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ M) →
      ‖SmoothedChebyshev SmoothingF ε X - 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X‖ ≤
        C * (M₀ * X / (ε * T) + M * X ^ σ₁ * Real.log (1 + T) + M * X / T) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hE⟩ := edge_bounds diffSmoothingF suppSmoothingF
  refine ⟨2 * C₂ * Real.exp 1 + 8 * C₁ + 3 * C₁ * Real.exp 1, by positivity,
    fun X ε σ₁ T M₀ M hX εpos ε1 hσ₁ hσ₁1 hT hM₀0 hM0 hzero hM₀ hleft hhor ↦ ?_⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := hE riemannZeta X ε σ₁ T M₀ M hX εpos ε1
    hσ₁ hσ₁1 hT hM₀0 hM0 hM₀ hleft hhor
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have holo : HolomorphicOn (deriv riemannZeta / riemannZeta)
      ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs1' : s ≠ 1 := hs2
    rw [Complex.mem_reProdIm] at hs1
    have hz := hzero s hs1.1.1 hs1.1.2 (abs_le.mpr ⟨hs1.2.1, hs1.2.2⟩) hs1'
    have hd : DifferentiableAt ℂ (fun z ↦ deriv riemannZeta z / riemannZeta z) s :=
      ((analyticAt_riemannZeta hs1').deriv.differentiableAt).div
        (differentiableAt_riemannZeta hs1') hz
    exact hd.differentiableWithinAt
  have hP := SmoothedChebyshevPull1 εpos ε1 X hX hT0 (by linarith) hσ₁1 holo suppSmoothingF
    SmoothingFpos mass_one diffSmoothingF
  rw [hP, add_sub_cancel_right]
  have hI : ∀ z : ℂ, ‖(1 / (2 * π * I)) * (I * z)‖ = 1 / (2 * π) * ‖z‖ := by
    intro z; rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_two_pi_I]
  have hI' : ∀ z : ℂ, ‖(1 / (2 * π * I)) * z‖ = 1 / (2 * π) * ‖z‖ := by
    intro z; rw [norm_mul, norm_two_pi_I]
  have e0 : ∀ t : ℝ, (1 : ℂ) + ((Real.log X)⁻¹ : ℝ) + t * I =
      (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I) := by intro t; push_cast; ring
  have n1 : ‖I₁ SmoothingF ε X T‖ ≤ 1 / (2 * π) * ‖∫ t in Iic (-T),
      IGr riemannZeta SmoothingF ε X (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ := by
    unfold I₁; rw [hI]; simp only [e0]; exact le_rfl
  have n9 : ‖I₉ SmoothingF ε X T‖ ≤ 1 / (2 * π) * ‖∫ t in Ici T,
      IGr riemannZeta SmoothingF ε X (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)‖ := by
    unfold I₉; rw [hI]; simp only [e0]; exact le_rfl
  have n37 : ‖I₃₇ SmoothingF ε T X σ₁‖ ≤ 1 / (2 * π) * ‖∫ t in (-T)..T,
      IGr riemannZeta SmoothingF ε X ((σ₁ : ℂ) + t * I)‖ := by
    unfold I₃₇; rw [hI]
  have n8 : ‖I₈ SmoothingF ε T X σ₁‖ ≤ 1 / (2 * π) * ‖∫ x in σ₁..(1 + (Real.log X)⁻¹),
      IGr riemannZeta SmoothingF ε X ((x : ℂ) + T * I)‖ := by
    unfold I₈; rw [hI']
  have e2 : ∀ x : ℝ, (x : ℂ) - T * I = (x : ℂ) + ((-T : ℝ) : ℂ) * I := by
    intro x; push_cast; ring
  have n2 : ‖I₂ SmoothingF ε T X σ₁‖ ≤ 1 / (2 * π) * ‖∫ x in σ₁..(1 + (Real.log X)⁻¹),
      IGr riemannZeta SmoothingF ε X ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
    unfold I₂; rw [hI']; simp only [e2]; exact le_rfl
  have hfin := five_le hC₁ hC₂ hM₀0 hM0 hX0 εpos hT0 (Real.log_nonneg (by linarith)) b2 b1 b3
    b5 b4
  have hsplit : ‖I₁ SmoothingF ε X T - I₂ SmoothingF ε T X σ₁ + I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ + I₉ SmoothingF ε X T‖ ≤
      ‖I₁ SmoothingF ε X T‖ + ‖I₃₇ SmoothingF ε T X σ₁‖ + ‖I₂ SmoothingF ε T X σ₁‖ +
        ‖I₈ SmoothingF ε T X σ₁‖ + ‖I₉ SmoothingF ε X T‖ := by
    have := norm_add_le (I₁ SmoothingF ε X T - I₂ SmoothingF ε T X σ₁ + I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁) (I₉ SmoothingF ε X T)
    have := norm_add_le (I₁ SmoothingF ε X T - I₂ SmoothingF ε T X σ₁ + I₃₇ SmoothingF ε T X σ₁)
      (I₈ SmoothingF ε T X σ₁)
    have := norm_add_le (I₁ SmoothingF ε X T - I₂ SmoothingF ε T X σ₁) (I₃₇ SmoothingF ε T X σ₁)
    have := norm_sub_le (I₁ SmoothingF ε X T) (I₂ SmoothingF ε T X σ₁)
    linarith
  exact hsplit.trans ((add_le_add (add_le_add (add_le_add (add_le_add n1 n37) n2) n8) n9).trans
    (Eq.trans_le (by ring) hfin))

end LeanLab.HardyLittlewood1923.U1503
