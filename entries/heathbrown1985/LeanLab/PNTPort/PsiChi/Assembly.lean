module

public import LeanLab.PNTPort.PsiChi.Contour
public import LeanLab.PNTPort.DirichletZF.LogDerivStripZF

/-!
# The smoothed `ψ(X, χ)` bound from the zero-free region

Lab proof, unit U-5205, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics, no
cited input.

* `logDeriv_right_le`: `‖L'/L(1 + d + it, χ)‖ ≤ 1/d + A` for `0 < d < 1`, every `χ` and `t`, from
  `‖L'/L(s, χ)‖ ≤ ∑ Λ(n) n^{-Re s} = -ζ'/ζ(Re s)` and the ported `ShiftZeroBound`.
-/

@[expose] public section


open Set Function Filter Complex Real MeasureTheory

open ArithmeticFunction (vonMangoldt)
open scoped LSeries.notation

local notation "Λ" => vonMangoldt

namespace LeanLab.PNTPort.PsiChi

open LeanLab.PNTPort.DirichletZF

lemma norm_term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    ‖LSeries.term (fun n ↦ (Λ n : ℂ)) (σ : ℂ) n‖ =
      (LSeries.term (fun n ↦ (Λ n : ℂ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hn0]; norm_cast
  rw [e, ← Complex.ofReal_div, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))]

theorem logDeriv_right_le : ∃ A : ℝ, 1 ≤ A ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (d t : ℝ), d ∈ Ioo 0 1 →
    ‖deriv (DirichletCharacter.LFunction χ) (((1 + d : ℝ) : ℂ) + t * I) /
      DirichletCharacter.LFunction χ (((1 + d : ℝ) : ℂ) + t * I)‖ ≤ 1 / d + A := by
  obtain ⟨C, hC, h⟩ := ShiftZeroBound
  refine ⟨C, hC, fun N _ χ d t hd ↦ ?_⟩
  set s : ℂ := ((1 + d : ℝ) : ℂ) + t * I with hsdef
  have hsre : s.re = 1 + d := by simp [hsdef]
  have hs : 1 < s.re := by rw [hsre]; linarith [hd.1]
  have hσ : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith [hd.1]
  have e := LSeries_chi_vonMangoldt_eq χ hs
  have hn : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
      ‖LSeries (↗χ * ↗Λ) s‖ := by rw [e, neg_div, norm_neg]
  rw [hn]
  have s1 := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).norm
  have s2 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hσ).norm
  have hterm : ∀ n, ‖LSeries.term (↗χ * ↗Λ) s n‖ ≤
      ‖LSeries.term (fun n ↦ (Λ n : ℂ)) ((1 + d : ℝ) : ℂ) n‖ := by
    intro n
    refine (LSeries.norm_term_le s (g := fun n ↦ (Λ n : ℂ)) ?_).trans
      (LSeries.norm_term_le_of_re_le_re _ (by rw [hsre]; simp) n)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  have hle : ‖LSeries (↗χ * ↗Λ) s‖ ≤
      ∑' n, ‖LSeries.term (fun n ↦ (Λ n : ℂ)) ((1 + d : ℝ) : ℂ) n‖ :=
    (norm_tsum_le_tsum_norm s1).trans (s1.tsum_le_tsum hterm s2)
  have hre : ∑' n, ‖LSeries.term (fun n ↦ (Λ n : ℂ)) ((1 + d : ℝ) : ℂ) n‖ =
      (LSeries (fun n ↦ (Λ n : ℂ)) ((1 + d : ℝ) : ℂ)).re := by
    simp only [LSeries]
    rw [Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt hσ)]
    congr 1; ext n; exact norm_term_vonMangoldt_real (1 + d) n
  have hζ : LSeries (fun n ↦ (Λ n : ℂ)) ((1 + d : ℝ) : ℂ) =
      -deriv riemannZeta (1 + d) / riemannZeta (1 + d) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ]; push_cast; ring_nf
  have hz := h d hd
  rw [hre, hζ, neg_div, neg_re] at hle
  linarith

/-- **The smoothed `ψ(X, χ)` bound.** For a fixed smoothing `F` and `c > 0` there are `κ, K, A`
and `C` such that for every `N`, every `χ ≠ χ₀` mod `N`, `X > 3`, `0 < ε < 1`, `T ≥ 1`, with
`L = log B(T)`: if every zero `ρ` of `L(s, χ)` has `Re ρ ≤ 1 - c / log B(Im ρ)` or
`Re ρ ≤ 1 - 2κ/L`, then
`‖∑ χ(n) Λ(n) Smooth1 F ε (n/X)‖ ≤ (C/(2πε)) (2e (log X + A) X/T + 4π K L² X^{1-κ/L} + 3e K L² X/T²)`.
Here `c > 0` is arbitrary; the zero-free region `zero_free_region_real` supplies one for which
the first alternative holds outside the exceptional box, and the second is where Siegel's theorem
puts the exceptional zero once `N` is small against `T`, `zeros_classical_or_siegel`. -/
theorem smoothed_psiChi_bound {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1) (c : ℝ) (hc : 0 < c) :
    ∃ κ K A C : ℝ, 0 < κ ∧ 0 < K ∧ 1 ≤ A ∧ 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ X ε T : ℝ,
      3 < X → 0 < ε → ε < 1 → 1 ≤ T →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) ∨ ρ.re ≤ 1 - 2 * κ / Real.log (Bt N T)) →
      ‖∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 SmoothingF ε (n / X)‖ ≤
        C / (2 * π * ε) * (2 * Real.exp 1 * (Real.log X + A) * X / T +
          4 * π * (K * Real.log (Bt N T) ^ 2) * X ^ (1 - κ / Real.log (Bt N T)) +
          3 * Real.exp 1 * (K * Real.log (Bt N T) ^ 2) * X / T ^ 2) := by
  obtain ⟨A, hA, hright⟩ := logDeriv_right_le
  obtain ⟨C, hCpos, hcont⟩ := contour_bound diffSmoothingF SmoothingFpos suppSmoothingF mass_one
  set c₀ := min c (5 / 12) with hc₀
  have hc₀pos : 0 < c₀ := lt_min hc (by norm_num)
  have hc₀le : c₀ ≤ 5 / 12 := min_le_right _ _
  have hc₀c : c₀ ≤ c := min_le_left _ _
  set κ := 2 * c₀ / 5 with hκ
  have hκpos : 0 < κ := by positivity
  have hl109 : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  set K := K0 + 5 / (2 * c₀ * Real.log (10 / 9)) with hK
  have hKpos : 0 < K := by have := K0_pos; positivity
  refine ⟨κ, K, A, C, hκpos, hKpos, hA, hCpos,
    fun N _ χ hχ X ε T hX εpos ε1 hT hfar ↦ ?_⟩
  set LT := Real.log (Bt N T) with hLdef
  have hL1 : 1 ≤ LT := one_le_log_Bt T
  have hLpos : 0 < LT := by linarith
  set σ₁ := 1 - κ / LT with hσ₁
  have hκLT : κ / LT ≤ 1 / 6 := by
    rw [div_le_iff₀ hLpos]; rw [hκ]; nlinarith
  have hκL0 : 0 < κ / LT := by positivity
  have log_gt : 1 < Real.log X := logt_gt_one hX.le
  have hd : (Real.log X)⁻¹ ∈ Ioo (0 : ℝ) 1 :=
    ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ log_gt⟩
  have hσ₀le : 1 + (Real.log X)⁻¹ ≤ 2 := by linarith [hd.2]
  have hlogt : ∀ t : ℝ, |t| ≤ T → Real.log (Bt N t) ≤ LT := fun t ht ↦
    log_Bt_mono (by rw [abs_of_pos (by linarith : (0 : ℝ) < T)]; exact ht)
  -- the strip bound on the line pieces
  have hstrip : ∀ σ t : ℝ, |t| ≤ T → σ₁ ≤ σ → σ ≤ 2 →
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤ K * LT ^ 2 := by
    intro σ t ht h1 h2
    have e : (σ : ℂ) + t * I = (σ : ℂ) + I * t := by ring
    rw [e]
    refine logDeriv_strip_le_L hχ hc₀pos hc₀le t σ LT (hlogt t ht) (fun ρ hρ _ ↦ ?_)
      (by rw [← hκ]; exact h1) h2
    rcases hfar ρ hρ with h | h
    · left
      have hLγ : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
      have : c₀ / Real.log (Bt N ρ.im) ≤ c / Real.log (Bt N ρ.im) :=
        div_le_div_of_nonneg_right hc₀c hLγ.le
      linarith
    · right
      have e2 : ((σ : ℂ) + I * t - ρ).re = σ - ρ.re := by simp
      have := Complex.re_le_norm ((σ : ℂ) + I * t - ρ)
      have h2κ : 2 * κ / LT = 2 * (κ / LT) := by ring
      rw [← hκ]
      linarith
  have hmain := hcont N χ hχ X ε σ₁ T (Real.log X + A) (K * LT ^ 2) hX εpos ε1
    (by linarith) (by linarith) hT (by linarith) (by positivity)
    (fun s hs h0 ↦ ?_)
    (fun t ↦ ?_)
    (fun t ht ↦ hstrip σ₁ t ht le_rfl (by linarith))
    (fun σ h1 h2 ↦ ⟨hstrip σ T (by rw [abs_of_pos (by linarith)]) h1 (by linarith),
      by have := hstrip σ (-T) (by rw [abs_neg, abs_of_pos (by linarith)]) h1 (by linarith)
         push_cast at this; exact this⟩)
  · exact hmain
  · -- no zero in the rectangle
    have hs' := hs
    simp only [Rectangle, Complex.mem_reProdIm] at hs'
    obtain ⟨hre, him⟩ := hs'
    simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero, sub_zero,
      add_re, sub_self, add_zero, sub_im, mul_im, add_im, zero_add, zero_sub, one_mul] at hre him
    rw [Set.uIcc_of_le (by linarith [hd.1])] at hre
    rw [Set.uIcc_of_le (by linarith)] at him
    have habs : |s.im| ≤ T := abs_le.mpr ⟨him.1, him.2⟩
    rcases hfar s h0 with h | h
    · have hLγ : 0 < Real.log (Bt N s.im) := by linarith [one_le_log_Bt (N := N) s.im]
      have h1 : c / LT ≤ c / Real.log (Bt N s.im) :=
        div_le_div_of_nonneg_left hc.le hLγ (hlogt s.im habs)
      have h2 : κ / LT < c / LT := by
        apply div_lt_div_of_pos_right _ hLpos
        rw [hκ]; linarith
      linarith [hre.1]
    · have : 2 * κ / LT = 2 * (κ / LT) := by ring
      linarith [hre.1]
  · have h := hright N χ (Real.log X)⁻¹ t hd
    rw [one_div, inv_inv] at h
    exact h

end LeanLab.PNTPort.PsiChi
