module

public import LeanLab.PNTPort.ZetaZeros.GoodHeight
public import LeanLab.PNTPort.ZetaZeros.Sym
public import LeanLab.PNTPort.ZetaZeros.Digamma2
public import LeanLab.PNTPort.StrongPNT.ZetaConj

/-!
# Good heights on `-1/2 ≤ σ ≤ 2`

Lab proof, unit U-5272, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
Davenport ch. 17, no cited input. Mathlib's `logDeriv_riemannZeta_one_sub`,
`ζ'/ζ(s) = -ζ'/ζ(1 - s) + log 2π - ψ(s) + (π/2) tan(πs/2)`, moves `good_height` from
`1/2 ≤ σ ≤ 2` to `-1/2 ≤ σ < 1/2`, with `digamma_strip` for `ψ` and `norm_tan_le` for the tangent.

`good_height_full`: an absolute `C` such that for every `T ≥ 5` some `T'` in `[T, T + 1]` has
`ζ(σ + iT') ≠ 0` and `‖ζ'/ζ(σ + iT')‖ ≤ C log² T` for every `σ` in `[-1/2, 2]`. These are the
horizontal edges of the rectangle for an explicit formula with all zeros.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric
open scoped Real ComplexConjugate

local notation "ζ" => riemannZeta

/-- `‖tan(x + iy)‖ ≤ 2` for real `x` and `y ≥ 1`. -/
theorem norm_tan_le {x y : ℝ} (hy : 1 ≤ y) : ‖Complex.tan (x + y * I)‖ ≤ 2 := by
  have hsh : 1 ≤ Real.sinh y := by
    have := Real.self_le_sinh_iff.mpr (by linarith : (0 : ℝ) ≤ y); linarith
  have hc2 : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by
    rw [Real.cosh_sq]; ring
  have hcos : Complex.cos (x + y * I) =
      ((Real.cos x * Real.cosh y : ℝ) : ℂ) + ((-(Real.sin x * Real.sinh y) : ℝ) : ℂ) * I := by
    rw [Complex.cos_add_mul_I]; push_cast; ring
  have hsin : Complex.sin (x + y * I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]; push_cast; ring
  have hnc : Real.sinh y ^ 2 ≤ ‖Complex.cos (x + y * I)‖ ^ 2 := by
    rw [hcos, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    have := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]
  have hns : ‖Complex.sin (x + y * I)‖ ^ 2 ≤ Real.cosh y ^ 2 := by
    rw [hsin, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    have := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y), sq_nonneg (Real.sin x)]
  have hcpos : 0 < ‖Complex.cos (x + y * I)‖ := by
    by_contra h
    have h0 : ‖Complex.cos (x + y * I)‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hnc; nlinarith
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_iff₀ hcpos]
  have hsq : ‖Complex.sin (x + y * I)‖ ^ 2 ≤ (2 * ‖Complex.cos (x + y * I)‖) ^ 2 := by
    nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hsq

lemma log_two_pi_le : Real.log (2 * π) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h1 := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 :=
    mul_lt_mul'' h1 h1 (by norm_num) (by norm_num)
  rw [e]; linarith [Real.pi_lt_d2]

/-- **Good heights on `-1/2 ≤ σ ≤ 2`.** -/
theorem good_height_full : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
    ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ζ (σ + I * T') ≠ 0 ∧
      ‖deriv ζ (σ + I * T') / ζ (σ + I * T')‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨C1, hC1, hg⟩ := good_height
  obtain ⟨K, hK, hψ⟩ := digamma_strip
  refine ⟨C1 + 2 * K + 10, by positivity, fun T hT => ?_⟩
  obtain ⟨T', hT'I, hgT⟩ := hg T hT
  refine ⟨T', hT'I, fun σ hσ => ?_⟩
  obtain ⟨hT1, hT2⟩ := hT'I
  have hlT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlT2 : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  rcases le_or_gt (1 / 2) σ with h | h
  · obtain ⟨hne, hb⟩ := hgT σ ⟨h, hσ.2⟩
    refine ⟨hne, hb.trans ?_⟩
    have : 0 ≤ Real.log T ^ 2 := by positivity
    nlinarith
  -- the left part, `-1/2 ≤ σ < 1/2`
  set s : ℂ := σ + I * T' with hs
  set u : ℂ := ((1 - σ : ℝ) : ℂ) + I * T' with hu
  have hw : 1 - s = conj u := by
    rw [hs, hu]; apply Complex.ext <;> simp
  obtain ⟨hune, hub⟩ := hgT (1 - σ) ⟨by linarith, by linarith [hσ.1]⟩
  have hsim : s.im = T' := by simp [hs]
  have hsre : s.re = σ := by simp [hs]
  have hwre : 0 < (1 - s).re := by simp [hsre]; linarith
  have hwim : (1 - s).im ≠ 0 := by simp [hsim]; linarith
  have hζw : ζ (1 - s) ≠ 0 := by rw [hw, riemannZeta_conj]; exact (map_ne_zero _).mpr hune
  have hζs : ζ s ≠ 0 := by
    have hw1 : (1 - s) ≠ 1 := by intro h; apply hwim; rw [h]; simp
    have := riemannZeta_one_sub (not_neg_nat_of_re_pos hwre) hw1
    rw [show 1 - (1 - s) = s by ring] at this
    rw [this]
    exact mul_ne_zero (feF_ne_zero hwre (not_odd_of_im hwim)) hζw
  refine ⟨hζs, ?_⟩
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h; have := congr_arg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hFE := logDeriv_riemannZeta_one_sub hint hζs
  rw [logDeriv_apply, logDeriv_apply] at hFE
  -- the four pieces
  have h1 : ‖deriv ζ (1 - s) / ζ (1 - s)‖ ≤ C1 * Real.log T ^ 2 := by
    have := logDerivZeta_conj u
    simp only [Pi.div_apply] at this
    rw [hw, this, Complex.norm_conj]; exact hub
  have h2 : ‖Complex.log (2 * π)‖ ≤ 2 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact log_two_pi_le
  have h3 : ‖digamma s‖ ≤ K * (2 * Real.log T) + 2 := by
    have e : s = (σ : ℂ) + T' * I := by rw [hs]; ring
    have hb := hψ T' (by linarith) σ (by linarith [hσ.1]) (by linarith)
    rw [← e] at hb
    have hl : Real.log (T' + 3) ≤ 2 * Real.log T := by
      calc Real.log (T' + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    have : K * Real.log (T' + 3) ≤ K * (2 * Real.log T) := by gcongr
    linarith
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    have e : (π : ℂ) * s / 2 = ((π * σ / 2 : ℝ) : ℂ) + ((π * T' / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [e, norm_mul]
    have ht := norm_tan_le (x := π * σ / 2) (y := π * T' / 2) (by nlinarith [Real.pi_gt_three])
    have hp : ‖(π : ℂ) / 2‖ ≤ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num; linarith [Real.pi_lt_four]
    calc _ ≤ 2 * 2 := mul_le_mul hp ht (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  rw [hFE]
  calc ‖-(deriv ζ (1 - s) / ζ (1 - s)) + Complex.log (2 * π) - digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖deriv ζ (1 - s) / ζ (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖digamma s‖ +
        ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (by rw [norm_neg])) le_rfl)) le_rfl)
    _ ≤ C1 * Real.log T ^ 2 + 2 + (K * (2 * Real.log T) + 2) + 4 := by gcongr
    _ ≤ (C1 + 2 * K + 10) * Real.log T ^ 2 := by nlinarith

end LeanLab.PNTPort.ZetaZeros

