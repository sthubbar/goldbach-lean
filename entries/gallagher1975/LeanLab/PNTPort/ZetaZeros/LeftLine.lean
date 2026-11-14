module

public import LeanLab.PNTPort.ZetaZeros.LeftHalf

/-!
# `ζ'/ζ` on the line `Re s = -1/2`

Lab proof, unit U-5273, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
no cited input. `logDeriv_left_line`: an absolute `C` with `ζ(-1/2 + it) ≠ 0` and
`‖ζ'/ζ(-1/2 + it)‖ ≤ C log(|t| + 3)` for every real `t`: for `|t| ≥ 1` by Mathlib's
`logDeriv_riemannZeta_one_sub`, the ported bound on `Re s = 3/2`, `digamma_strip` and
`norm_tan_le`, using conjugation for `t ≤ -1`; for `|t| ≤ 1` by continuity on a compact segment.
This is the left vertical edge of the rectangle for an explicit formula with all zeros.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric
open scoped Real ComplexConjugate

local notation "ζ" => riemannZeta

lemma zeta_left_ne (t : ℝ) : ζ ((-1 / 2 : ℝ) + t * I) ≠ 0 := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  set w : ℂ := 1 - s with hw
  have hwre : (w).re = 3 / 2 := by rw [hw, hs]; simp; norm_num
  have hw1 : w ≠ 1 := by intro h; rw [h] at hwre; simp at hwre; norm_num at hwre
  have hodd : ∀ k : ℤ, w ≠ 2 * k + 1 := by
    intro k hk
    have := congr_arg Complex.re hk; rw [hwre] at this; simp at this
    have h1 : (2 : ℝ) * k = 1 / 2 := by linarith
    have : (4 * k : ℤ) = 1 := by exact_mod_cast (by linarith : (4 : ℝ) * k = 1)
    omega
  have := riemannZeta_one_sub (not_neg_nat_of_re_pos (by rw [hwre]; norm_num)) hw1
  rw [show 1 - w = s by rw [hw]; ring] at this
  rw [this]
  exact mul_ne_zero (feF_ne_zero (by rw [hwre]; norm_num) hodd)
    (riemannZeta_ne_zero_of_one_lt_re (by rw [hwre]; norm_num))

/-- The bound for `t ≥ 1`. -/
lemma logDeriv_left_pos : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
    ‖deriv ζ ((-1 / 2 : ℝ) + t * I) / ζ ((-1 / 2 : ℝ) + t * I)‖ ≤ C * Real.log (t + 3) := by
  obtain ⟨K, hK, hψ⟩ := digamma_strip
  obtain ⟨c, hc, hv⟩ := dlog_riemannZeta_bdd_on_vertical_lines (σ₀ := 3 / 2) (by norm_num)
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  refine ⟨c + K + 10, by positivity, fun t ht => ?_⟩
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hsim : s.im = t := by simp [hs]
  have hζs := zeta_left_ne t
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h; have := congr_arg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hFE := logDeriv_riemannZeta_one_sub hint hζs
  rw [logDeriv_apply, logDeriv_apply] at hFE
  have hlt : 1 ≤ Real.log (t + 3) := le_trans hl3 (Real.log_le_log (by norm_num) (by linarith))
  have h1 : ‖deriv ζ (1 - s) / ζ (1 - s)‖ ≤ c := by
    have e : 1 - s = ((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
    rw [e]; exact hv (-t)
  have h2 : ‖Complex.log (2 * π)‖ ≤ 2 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact log_two_pi_le
  have h3 : ‖digamma s‖ ≤ K * Real.log (t + 3) + 2 := hψ t ht (-1 / 2) (by norm_num) (by norm_num)
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    have e : (π : ℂ) * s / 2 = ((π * (-1 / 2) / 2 : ℝ) : ℂ) + ((π * t / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [e, norm_mul]
    have ht' := norm_tan_le (x := π * (-1 / 2) / 2) (y := π * t / 2) (by nlinarith [Real.pi_gt_three])
    have hp : ‖(π : ℂ) / 2‖ ≤ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num; linarith [Real.pi_lt_four]
    calc _ ≤ 2 * 2 := mul_le_mul hp ht' (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  rw [hFE]
  calc ‖-(deriv ζ (1 - s) / ζ (1 - s)) + Complex.log (2 * π) - digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖deriv ζ (1 - s) / ζ (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖digamma s‖ +
        ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (by rw [norm_neg])) le_rfl)) le_rfl)
    _ ≤ c + 2 + (K * Real.log (t + 3) + 2) + 4 := by gcongr
    _ ≤ (c + K + 10) * Real.log (t + 3) := by nlinarith

/-- **`‖ζ'/ζ(-1/2 + it)‖ ≤ C log(|t| + 3)` for every real `t`.** -/
theorem logDeriv_left_line : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ζ ((-1 / 2 : ℝ) + t * I) ≠ 0 ∧
    ‖deriv ζ ((-1 / 2 : ℝ) + t * I) / ζ ((-1 / 2 : ℝ) + t * I)‖ ≤ C * Real.log (|t| + 3) := by
  obtain ⟨C1, hC1, hpos⟩ := logDeriv_left_pos
  -- the compact middle segment
  have hcont : ContinuousOn (fun t : ℝ => deriv ζ ((-1 / 2 : ℝ) + t * I) /
      ζ ((-1 / 2 : ℝ) + t * I)) (Icc (-1) 1) := by
    intro t _
    have hne1 : ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 1 := by
      intro h; have := congr_arg Complex.re h; simp at this; norm_num at this
    have hA := analyticAt_riemannZeta hne1
    have hcomp : ContinuousAt (fun t : ℝ => ((-1 / 2 : ℝ) : ℂ) + t * I) t := by fun_prop
    have h1 := ContinuousAt.comp (g := deriv ζ) (f := fun t : ℝ => ((-1 / 2 : ℝ) : ℂ) + t * I)
      (x := t) hA.deriv.continuousAt hcomp
    have h2 := ContinuousAt.comp (g := ζ) (f := fun t : ℝ => ((-1 / 2 : ℝ) : ℂ) + t * I)
      (x := t) hA.continuousAt hcomp
    exact (h1.div h2 (zeta_left_ne t)).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  refine ⟨C1 + |M| + 1, by positivity, fun t => ⟨zeta_left_ne t, ?_⟩⟩
  have hlt : 1 ≤ Real.log (|t| + 3) :=
    le_trans hl3 (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  have hl0 : 0 ≤ Real.log (|t| + 3) := by linarith
  rcases le_or_gt 1 t with h | h
  · have := hpos t h
    rw [abs_of_nonneg (show (0 : ℝ) ≤ t by linarith)]
    calc _ ≤ C1 * Real.log (t + 3) := this
      _ ≤ (C1 + |M| + 1) * Real.log (t + 3) := by
          have : 0 ≤ Real.log (t + 3) := Real.log_nonneg (by linarith)
          nlinarith [abs_nonneg M]
  rcases le_or_gt t (-1) with h' | h'
  · have := hpos (-t) (by linarith)
    have hconj : ((-1 / 2 : ℝ) : ℂ) + t * I = conj (((-1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [hconj]
    have hc := logDerivZeta_conj (((-1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
    simp only [Pi.div_apply] at hc
    rw [hc, Complex.norm_conj, abs_of_neg (show t < 0 by linarith)]
    calc _ ≤ C1 * Real.log (-t + 3) := this
      _ ≤ (C1 + |M| + 1) * Real.log (-t + 3) := by
          have : 0 ≤ Real.log (-t + 3) := Real.log_nonneg (by linarith)
          nlinarith [abs_nonneg M]
  · have := hM t ⟨h'.le, h.le⟩
    calc _ ≤ M := this
      _ ≤ |M| := le_abs_self M
      _ ≤ (C1 + |M| + 1) * Real.log (|t| + 3) := by nlinarith [abs_nonneg M]

end LeanLab.PNTPort.ZetaZeros

