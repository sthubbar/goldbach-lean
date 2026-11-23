module

public import LeanLab.HelfgottMajor.Decomp511a
public import LeanLab.HelfgottMajor.Gamma503
public import LeanLab.HelfgottArcs.Statements
public import LeanLab.HelfgottMajor.BookL1523
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Tactic

/-!
P0014 Corollary 3.2 at k equal to zero, pages 27 and 28.
Scalar decay estimates and smaller analytic inputs for Gaussian123Base.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- The right side of display 3.4 on page 10 for k equal to 0, without the constant c0. -/
noncomputable def corEnvelope (δ τ : ℝ) : ℝ :=
  if |τ| < 3 / 2 * (π * δ) ^ 2 then exp (-0.1065 * (τ / (π * δ)) ^ 2)
  else exp (-0.1598 * |τ|)

end LeanLab.HelfgottMajor.SplitGaussian123

namespace LeanLab.HelfgottMajor.Decomp503a
open Real SplitGaussian123

/-- The first negligible error in display 3.73, page 28, at k equal to zero.
The threshold is exactly the height 100 used in Corollary 3.2. -/
theorem linear_remainder_bound (t : ℝ) (ht : 100 ≤ t) :
    1.025 * sqrt t * exp (-0.4798 * t) ≤
      0.000000000013 * exp (-0.1598 * t) := by
  have ht1 : 1 ≤ t := by linarith
  have hs : sqrt t ≤ t := sqrt_le_self_iff.mpr (Or.inr ht1)
  have hp : t * exp (-0.01 * t) ≤ 100 := by
    have h := mul_exp_neg_le_exp_neg_one (0.01 * t)
    have h1 : exp (-1 : ℝ) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    have heq : -(0.01 * t) = -0.01 * t := by ring
    rw [heq] at h
    nlinarith
  have he31 : (2.7 : ℝ) ^ 31 ≤ exp 31 := by
    calc
      _ ≤ (exp 1) ^ 31 := pow_le_pow_left₀ (by norm_num)
        (by linarith [exp_one_gt_d9]) _
      _ = exp 31 := by rw [← exp_nat_mul]; norm_num
  have hem : exp (-31 : ℝ) ≤ 1 / (2.7 : ℝ) ^ 31 := by
    rw [exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he31
  have hd : exp (-0.31 * t) ≤ exp (-31 : ℝ) := exp_le_exp.mpr (by linarith)
  have hdec : sqrt t * exp (-0.32 * t) ≤ 100 * (1 / (2.7 : ℝ) ^ 31) := by
    calc
      _ ≤ t * exp (-0.32 * t) := mul_le_mul_of_nonneg_right hs (exp_pos _).le
      _ = (t * exp (-0.01 * t)) * exp (-0.31 * t) := by
        rw [mul_assoc, ← exp_add]
        congr 2; ring
      _ ≤ 100 * (1 / (2.7 : ℝ) ^ 31) :=
        mul_le_mul hp (hd.trans hem) (exp_pos _).le (by norm_num)
  calc
    _ = (1.025 * (sqrt t * exp (-0.32 * t))) * exp (-0.1598 * t) := by
      rw [show -0.4798 * t = -0.32 * t + -0.1598 * t by ring, exp_add]
      ring
    _ ≤ (1.025 * (100 * (1 / (2.7 : ℝ) ^ 31))) * exp (-0.1598 * t) := by
      gcongr
    _ ≤ _ := by gcongr; norm_num

/-- The exponential branch of display 3.74 on page 28. -/
theorem exponential_remainder_bound (t : ℝ) (ht : 100 ≤ t) :
    exp (-(25 / 32 : ℝ) * t) ≤
      0.00000000000000000000000000103 * exp (-0.1598 * t) := by
  have h62 : (2.71828 : ℝ) ^ 62 ≤ exp 62 := by
    calc
      _ ≤ (exp 1) ^ 62 := pow_le_pow_left₀ (by norm_num)
        (by linarith [exp_one_gt_d9]) _
      _ = exp 62 := by rw [← exp_nat_mul]; norm_num
  have hsmall : (1.1555125 : ℝ) ≤ exp 0.145 := by
    have h := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.145)
    norm_num at h ⊢
    exact h
  have hlarge : (2.71828 : ℝ) ^ 62 * 1.1555125 ≤ exp 62.145 := by
    calc
      _ ≤ exp 62 * exp 0.145 :=
        mul_le_mul h62 hsmall (by norm_num) (exp_pos _).le
      _ = _ := by rw [← exp_add]; norm_num
  have htail : exp (-0.62145 * t) ≤ 0.00000000000000000000000000103 := by
    calc
      _ ≤ exp (-62.145 : ℝ) := exp_le_exp.mpr (by linarith)
      _ ≤ 1 / ((2.71828 : ℝ) ^ 62 * 1.1555125) := by
        rw [exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hlarge
      _ ≤ _ := by norm_num
  calc
    _ = exp (-0.62145 * t) * exp (-0.1598 * t) := by
      rw [← exp_add]
      congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (exp_pos _).le

/-- The Gaussian branch of display 3.74 on page 28.
The height hypothesis of Corollary 3.2 makes its normalized ratio at least four pi. -/
theorem gaussian_remainder_bound (u : ℝ) (hu : 4 * π ≤ |u|) :
    exp (-(1 / 8 : ℝ) * u ^ 2) ≤ 0.055 * exp (-0.1066 * u ^ 2) := by
  have habs : (12.566368 : ℝ) ≤ |u| := by linarith [pi_gt_d6]
  have hsq : (12.566368 : ℝ) ^ 2 ≤ u ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (by norm_num) habs 2
  have hr : (2.905 : ℝ) ≤ 0.0184 * u ^ 2 := by nlinarith
  have he : (200 / 11 : ℝ) ≤ exp 2.905 := by
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.905) 12
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have htail : exp (-0.0184 * u ^ 2) ≤ 0.055 := by
    calc
      _ ≤ exp (-2.905 : ℝ) := exp_le_exp.mpr (by linarith)
      _ ≤ 1 / (200 / 11 : ℝ) := by
        rw [exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he
      _ = _ := by norm_num
  calc
    _ = exp (-0.0184 * u ^ 2) * exp (-0.1066 * u ^ 2) := by
      rw [← exp_add]
      congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (exp_pos _).le

/-- The rate comparison of display 3.68 on page 27.
The exact saddle point rate is the existing BookE.E of display 3.2. -/
theorem saddle_rate_lower (r : ℝ) (hr : 0 < r) :
    (if (1.5 : ℝ) ≤ r then 0.1598 else 0.1065 * r) ≤ BookE.E r := by
  have hval : (0.1598 : ℝ) ≤ BookE.E 1.5 := by
    have h := BookE.E_lower (r := 1.5) (rL := 1.5) (rU := 1.5)
      (sL := 1.8027756) (sU := 1.8027757) (XL := 0.63355) (uU := 1.183803)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hp := BookE.arctan_ge_of_lt_one (X := 0.63355) (by norm_num) (by norm_num)
    norm_num [BookE.P17] at hp
    norm_num at h
    nlinarith [pi_gt_d6]
  have hm : MonotoneOn BookE.E (Set.Ioi (0 : ℝ)) := by
    have hf : Monotone BookL1523.Ft := by
      apply monotone_of_deriv_nonneg
        (fun t => (BookL1523.hasDerivAt_Ft t).differentiableAt)
      intro t
      rw [(BookL1523.hasDerivAt_Ft t).deriv]
      positivity
    intro a ha b hb hab
    obtain ⟨ta, hta, hRa⟩ := BookL1523.Rt_surj (r := a) ha
    obtain ⟨tb, htb, hRb⟩ := BookL1523.Rt_surj (r := b) hb
    have hle : ta ≤ tb := by
      by_contra h
      have hlt : tb < ta := lt_of_not_ge h
      have hh := BookL1523.Rt_strictMono ⟨htb.1.le, htb.2⟩ ⟨hta.1.le, hta.2⟩ hlt
      rw [hRa, hRb] at hh
      linarith
    rw [← hRa, ← hRb, BookL1523.E_Rt hta.1 hta.2, BookL1523.E_Rt htb.1 htb.2]
    exact hf hle
  split_ifs with h
  · exact hval.trans (hm (by norm_num) hr h)
  · have hsmall : r ≤ 1.5 := (lt_of_not_ge h).le
    have hh := BookL1523.lemma_15_23 hr (by norm_num : (0 : ℝ) < 1.5) hsmall
    dsimp only at hh
    have hbase : (0.1065 : ℝ) ≤ BookE.E 1.5 / 1.5 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have hl : (0.1065 : ℝ) ≤ BookE.E r / r := hbase.trans hh
    exact (le_div_iff₀ hr).mp hl

/-- The two elementary error envelopes are below the envelope of display 3.4.
Source page 28, the comparison after display 3.75. -/
theorem corEnvelope_domination (δ τ : ℝ) (hδ : δ ≠ 0) :
    exp (-0.1598 * |τ|) ≤ corEnvelope δ τ ∧
      exp (-0.1066 * (τ / (π * δ)) ^ 2) ≤ corEnvelope δ τ := by
  have hd : 0 < (π * δ) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero pi_ne_zero hδ)
  have hs : |τ| ^ 2 = τ ^ 2 := sq_abs τ
  unfold corEnvelope
  split_ifs with h
  · have hratio : (τ / (π * δ)) ^ 2 ≤ 1.5 * |τ| := by
      rw [div_pow, div_le_iff₀ hd]
      have hh := mul_le_mul_of_nonneg_right h.le (abs_nonneg τ)
      nlinarith
    constructor
    · apply exp_le_exp.mpr
      nlinarith [abs_nonneg τ]
    · apply exp_le_exp.mpr
      nlinarith [sq_nonneg (τ / (π * δ))]
  · have hratio : 1.5 * |τ| ≤ (τ / (π * δ)) ^ 2 := by
      rw [div_pow, le_div_iff₀ hd]
      have hh := mul_le_mul_of_nonneg_right (le_of_not_gt h) (abs_nonneg τ)
      nlinarith
    constructor
    · exact le_rfl
    · apply exp_le_exp.mpr
      nlinarith [abs_nonneg τ]

/-- The exact saddle exponential is below the envelope of display 3.4.
Source display 3.68 and the conclusion on page 28. -/
theorem saddle_exponential_bound (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    exp (-BookE.E (|τ| / (π * δ) ^ 2) * |τ|) ≤ corEnvelope δ τ := by
  have hd : 0 < (π * δ) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero pi_ne_zero hδ)
  let r := |τ| / (π * δ) ^ 2
  have hr : 0 < r := div_pos hτ hd
  have heq : r * |τ| = (τ / (π * δ)) ^ 2 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_pow]
    congr 1
    nlinarith [sq_abs τ]
  have hrate := saddle_rate_lower r hr
  change exp (-BookE.E r * |τ|) ≤ _
  unfold corEnvelope
  split_ifs with h
  · have hrlt : r < 1.5 := by
      dsimp [r]
      rw [div_lt_iff₀ hd]
      nlinarith
    rw [if_neg (not_le.mpr hrlt)] at hrate
    have hm : 0.1065 * (τ / (π * δ)) ^ 2 ≤ BookE.E r * |τ| := by
      calc
        _ = (0.1065 * r) * |τ| := by rw [← heq]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hrate hτ.le
    exact exp_le_exp.mpr (by linarith)
  · have hrge : 1.5 ≤ r := by
      dsimp [r]
      rw [le_div_iff₀ hd]
      have hh := le_of_not_gt h
      nlinarith
    rw [if_pos hrge] at hrate
    have hm := mul_le_mul_of_nonneg_right hrate hτ.le
    exact exp_le_exp.mpr (by linarith)

/-- The last two terms of display 3.69 at k equal to zero, after display 3.72.
The reciprocal coefficient is the k equal to zero row of display 3.70. -/
noncomputable def saddleRemainder (δ τ : ℝ) : ℝ :=
  1.025 * sqrt |τ| * exp (-0.4798 * |τ|) +
    (min (|τ| / (2 * π * |δ|)) (5 / 4 * sqrt |τ|))⁻¹ *
      exp (-min ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * |τ|))

/-- Displays 3.73 to 3.75 absorb the two explicit residual terms into 0.0089
of the envelope, as used at the end of page 28. -/
theorem saddle_remainder_bound (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |τ|) :
    saddleRemainder δ τ ≤ 0.0089 * corEnvelope δ τ := by
  let t := |τ|
  let C := min (t / (2 * π * |δ|)) (5 / 4 * sqrt t)
  have ht : 100 ≤ t := (le_max_left _ _).trans hτ
  have hδt : 4 * π ^ 2 * |δ| ≤ t := (le_max_right _ _).trans hτ
  have hd : 0 < |δ| := abs_pos.mpr hδ
  have ha : 2 * π ≤ t / (2 * π * |δ|) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hs : 10 ≤ sqrt t := le_sqrt_of_sq_le (by nlinarith)
  have hb : 2 * π ≤ 5 / 4 * sqrt t := by nlinarith [pi_lt_four]
  have hC : (6.28 : ℝ) ≤ C := by
    have hh : 2 * π ≤ C := le_min ha hb
    linarith [pi_gt_d2]
  have hCi : C⁻¹ ≤ 1 / (6.28 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hC
  have hC0 : 0 ≤ C⁻¹ := inv_nonneg.mpr (by linarith)
  have hCi1 : C⁻¹ ≤ 1 := by norm_num at hCi; linarith
  have hCg : C⁻¹ * 0.055 ≤ 0.0088 := by norm_num at hCi; nlinarith
  have hu : 4 * π ≤ |τ / (π * δ)| := by
    rw [abs_div, abs_mul, abs_of_pos pi_pos, le_div_iff₀ (mul_pos pi_pos hd)]
    nlinarith
  have hg := gaussian_remainder_bound (τ / (π * δ)) hu
  have he := exponential_remainder_bound t ht
  have hl := linear_remainder_bound t ht
  have hmin :
      exp (-min ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * t)) ≤
        exp (-(1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) + exp (-(25 / 32 : ℝ) * t) := by
    rcases le_total ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * t) with h | h
    · rw [min_eq_left h]
      simp only [neg_mul]
      exact le_add_of_nonneg_right (exp_nonneg _)
    · rw [min_eq_right h]
      simp only [neg_mul]
      exact le_add_of_nonneg_left (exp_nonneg _)
  have hlast :
      C⁻¹ * exp (-min ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * t)) ≤
        0.0088 * exp (-0.1066 * (τ / (π * δ)) ^ 2) +
          0.00000000000000000000000000103 * exp (-0.1598 * t) := by
    calc
      _ ≤ C⁻¹ * (exp (-(1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) +
          exp (-(25 / 32 : ℝ) * t)) := mul_le_mul_of_nonneg_left hmin hC0
      _ ≤ C⁻¹ * (0.055 * exp (-0.1066 * (τ / (π * δ)) ^ 2) +
          0.00000000000000000000000000103 * exp (-0.1598 * t)) := by gcongr
      _ = (C⁻¹ * 0.055) * exp (-0.1066 * (τ / (π * δ)) ^ 2) +
          (C⁻¹ * 0.00000000000000000000000000103) * exp (-0.1598 * t) := by ring
      _ ≤ _ := by gcongr; linarith only [hCi1]
  obtain ⟨hdom1, hdom2⟩ := corEnvelope_domination δ τ hδ
  have hE : 0 ≤ corEnvelope δ τ := (exp_pos _).le.trans hdom1
  unfold saddleRemainder
  change 1.025 * sqrt t * exp (-0.4798 * t) +
    C⁻¹ * exp (-min ((1 / 8 : ℝ) * (τ / (π * δ)) ^ 2) ((25 / 32 : ℝ) * t)) ≤ _
  change exp (-0.1598 * t) ≤ corEnvelope δ τ at hdom1
  linarith only [hl, hlast, hdom1, hdom2, hE]

/-- The zero shift decay of display 3.3 is stronger than the envelope at height 100.
This is a scalar consequence of Theorem 3.1 on page 10. -/
theorem zero_shift_scalar_bound (t : ℝ) (ht : 100 ≤ t) :
    exp (π / 2) * sqrt t * exp (-(π / 4) * t) ≤
      4.226 * exp (-0.1598 * t) := by
  have ht1 : 1 ≤ t := by linarith
  have hp : exp (π / 2) ≤ 9 := by
    calc
      _ ≤ exp 2 := exp_le_exp.mpr (by linarith [pi_lt_four])
      _ = (exp 1) ^ 2 := by rw [← exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ (exp_nonneg _) exp_one_lt_three.le 2
      _ = _ := by norm_num
  have he3 : (8 : ℝ) ≤ exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) exp_one_gt_two.le 3
      _ = exp 3 := by rw [← exp_nat_mul]; norm_num
  have he : exp (-0.2902 * t) ≤ 1 / (8 : ℝ) := by
    calc
      _ ≤ exp (-3 : ℝ) := exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he3
  have hpoly : t * exp (-0.3 * t) ≤ 10 / 3 := by
    have h := mul_exp_neg_le_exp_neg_one (0.3 * t)
    have h1 : exp (-1 : ℝ) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    rw [show -(0.3 * t) = -0.3 * t by ring] at h
    nlinarith only [h, h1]
  have hs : sqrt t * exp (-0.5902 * t) ≤ (10 / 3 : ℝ) * (1 / 8) := by
    calc
      _ ≤ t * exp (-0.5902 * t) :=
        mul_le_mul_of_nonneg_right (sqrt_le_self_iff.mpr (Or.inr ht1)) (exp_nonneg _)
      _ = (t * exp (-0.3 * t)) * exp (-0.2902 * t) := by
        rw [mul_assoc, ← exp_add]
        congr 2; ring
      _ ≤ _ := mul_le_mul hpoly he (exp_nonneg _) (by norm_num)
  have hdec : exp (-(π / 4) * t) ≤ exp (-0.5902 * t) * exp (-0.1598 * t) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have hpt := mul_le_mul_of_nonneg_right pi_gt_three.le (by linarith : 0 ≤ t)
    nlinarith only [hpt]
  calc
    _ ≤ exp (π / 2) * sqrt t * (exp (-0.5902 * t) * exp (-0.1598 * t)) := by gcongr
    _ = (exp (π / 2) * (sqrt t * exp (-0.5902 * t))) * exp (-0.1598 * t) := by ring
    _ ≤ (9 * ((10 / 3 : ℝ) * (1 / 8))) * exp (-0.1598 * t) := by gcongr
    _ ≤ _ := by gcongr; norm_num

/-- LEAF: proved from Gamma reflection and the raw integral boundary.
P0014 Theorem 3.1, page 10, display 3.3 at delta equal to zero.
This is its single Mellin transform bound in the narrower height range at least 100.
The two reflected points in Corollary 3.2 will be handled by the assembly. -/
theorem zero_shift_mellin_decay (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : 100 ≤ |s.im|) :
    ‖gaussianMellin 0 s‖ ≤
      exp (π / 2) / 2 * |s.im| ^ (s.re / 2) * exp (-(π / 4) * |s.im|) := by
  have ht0 : 0 < |s.im| := by linarith
  by_cases hpos : 0 < s.re
  · let a := s.re / 2 + 1
    let y := s.im / 2
    have ha : 1 ≤ a := by dsimp [a]; linarith
    have hb : a ≤ 3 / 2 := by dsimp [a]; linarith
    have hy : 1 ≤ |y| := by
      dsimp [y]
      rw [abs_div]
      norm_num
      linarith
    have hg := Gamma503.gamma_shifted_decay a y ha hb hy
    have heq : (a : ℂ) + y * Complex.I = s / 2 + 1 := by
      apply Complex.ext <;> simp [a, y]
    rw [heq] at hg
    have hyabs : |y| = |s.im| / 2 := by simp [y, abs_div]
    rw [hyabs] at hg
    rw [show -(π / 2) * (|s.im| / 2) = -(π / 4) * |s.im| by ring] at hg
    have hm := congrArg norm (Gamma503.gaussian_mellin_regularized s hpos)
    have hpow : ‖(2 : ℂ) ^ (s / 2)‖ = (2 : ℝ) ^ (s.re / 2) := by
      have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (s / 2)
      simpa using h
    rw [norm_mul, norm_mul, hpow] at hm
    have hsmall : (2 : ℝ) ^ (s.re / 2) ≤ |s.im| ^ (s.re / 2) :=
      rpow_le_rpow (by norm_num) (by linarith) (by linarith)
    have hcoef : 4 * (|s.im| / 2 + 1) ≤ exp (π / 2) / 2 * |s.im| := by
      have he := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.5) 4
      norm_num [Finset.sum_range_succ] at he
      have hpi : exp 1.5 ≤ exp (π / 2) := exp_le_exp.mpr (by linarith [pi_gt_three])
      have hlow : (4.08 : ℝ) ≤ exp (π / 2) := by linarith only [he, hpi]
      have hh := mul_le_mul_of_nonneg_right hlow (abs_nonneg s.im)
      nlinarith only [hh, hτ]
    apply (mul_le_mul_iff_right₀ ht0).mp
    calc
      |s.im| * ‖gaussianMellin 0 s‖ ≤ ‖s‖ * ‖gaussianMellin 0 s‖ :=
        mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) (norm_nonneg _)
      _ = (2 : ℝ) ^ (s.re / 2) * ‖Complex.Gamma (s / 2 + 1)‖ := hm
      _ ≤ |s.im| ^ (s.re / 2) *
          (4 * (|s.im| / 2 + 1) * exp (-(π / 4) * |s.im|)) :=
        mul_le_mul hsmall hg (norm_nonneg _) (rpow_nonneg (abs_nonneg _) _)
      _ ≤ |s.im| ^ (s.re / 2) *
          ((exp (π / 2) / 2 * |s.im|) * exp (-(π / 4) * |s.im|)) := by gcongr
      _ = |s.im| * (exp (π / 2) / 2 * |s.im| ^ (s.re / 2) *
          exp (-(π / 4) * |s.im|)) := by ring
  · have hs0 : s.re = 0 := le_antisymm (le_of_not_gt hpos) hσ0
    have hni := Gamma503.gaussian_zero_re_not_integrable s hs0
    have hz : gaussianMellin 0 s = 0 := by
      simpa [gaussianMellin, mellin, LeanLab.HelfgottArcs.e, smul_eq_mul] using
        MeasureTheory.integral_undef hni
    rw [hz, norm_zero]
    positivity

/-- LEAF: OPEN. P0014 proof of Corollary 3.2, pages 27 and 28, displays 3.69 to 3.72
at k equal to zero. Theorem 3.1 supplies the saddle expansion, the coefficient of its
main exponential is at most 4.217, and the other terms are saddleRemainder.
The rate floor and the small error absorption are separate proved scalar steps. -/
theorem saddle_pair_expansion (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
        saddleRemainder δ s.im := by
  simpa only [saddleRemainder] using
    Decomp511a.pair_expansion δ s hδ hσ0 hσ1 hτ

/-- The zero shift case of Corollary 3.2 has no open analytic input.
P0014 page 10, display 3.4, with delta and k equal to zero.
The raw integral boundary convention is the same as in zero_shift_mellin_decay. -/
theorem zero_shift_corollary (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : 100 ≤ |s.im|) :
    ‖gaussianMellin 0 s‖ + ‖gaussianMellin 0 (1 - s)‖ ≤
      4.226 * corEnvelope 0 s.im := by
  have ht1 : 1 ≤ |s.im| := by linarith
  have hτ2 : |(1 - s).im| = |s.im| := by simp
  have h1 := zero_shift_mellin_decay s hσ0 hσ1 hτ
  have h2 := zero_shift_mellin_decay (1 - s)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simpa only [hτ2] using hτ)
  rw [hτ2] at h2
  have hp1 : |s.im| ^ (s.re / 2) ≤ sqrt |s.im| := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hp2 : |s.im| ^ ((1 - s).re / 2) ≤ sqrt |s.im| := by
    rw [sqrt_eq_rpow]
    apply rpow_le_rpow_of_exponent_le ht1
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hh1 : ‖gaussianMellin 0 s‖ ≤
      exp (π / 2) / 2 * sqrt |s.im| * exp (-(π / 4) * |s.im|) :=
    h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp1 (by positivity)) (exp_nonneg _))
  have hh2 : ‖gaussianMellin 0 (1 - s)‖ ≤
      exp (π / 2) / 2 * sqrt |s.im| * exp (-(π / 4) * |s.im|) :=
    h2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp2 (by positivity)) (exp_nonneg _))
  have hpair : ‖gaussianMellin 0 s‖ + ‖gaussianMellin 0 (1 - s)‖ ≤
      exp (π / 2) * sqrt |s.im| * exp (-(π / 4) * |s.im|) := by
    nlinarith only [hh1, hh2]
  have hbranch : ¬ |s.im| < 3 / 2 * (π * 0) ^ 2 := by
    simpa using not_lt.mpr (abs_nonneg s.im)
  have henv : corEnvelope 0 s.im = exp (-0.1598 * |s.im|) := by
    unfold corEnvelope
    rw [if_neg hbranch]
  rw [henv]
  exact hpair.trans (zero_shift_scalar_bound _ hτ)

/-- Corollary 3.2 at k equal to zero, assembled from the proved zero shift input and the OPEN twisted input.
The eight scalar estimates above have clean axioms. In the lab this assembly rests on an unproved step.
Source display 3.4 on page 10 and the conclusion on page 28. -/
theorem corollary_from_saddle_pieces (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im := by
  have ht100 : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  by_cases hδ : δ = 0
  · subst δ
    exact zero_shift_corollary s hσ0 hσ1 ht100
  · have hexp := saddle_exponential_bound δ s.im hδ (by linarith)
    have hrem := saddle_remainder_bound δ s.im hδ hτ
    have hE : 0 ≤ corEnvelope δ s.im := (exp_pos _).le.trans
      (corEnvelope_domination δ s.im hδ).1
    calc
      _ ≤ 4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
          saddleRemainder δ s.im := saddle_pair_expansion δ s hδ hσ0 hσ1 hτ
      _ ≤ 4.217 * corEnvelope δ s.im + 0.0089 * corEnvelope δ s.im :=
        add_le_add (mul_le_mul_of_nonneg_left hexp (by norm_num)) hrem
      _ ≤ _ := by nlinarith only [hE]

/-- The absolute integral bound of display 4.30 with display 4.42 cannot supply
Corollary 3.2 at height 100. This compares the two scalar budgets only.
Source pages 10, 39 and 43. It refutes no analytic estimate in the paper. -/
theorem absolute_integral_budget_too_weak :
    4.226 * exp (-0.1598 * (100 : ℝ)) < 2.15581 := by
  have he3 : (8 : ℝ) ≤ exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) exp_one_gt_two.le 3
      _ = exp 3 := by rw [← exp_nat_mul]; norm_num
  have he : exp (-0.1598 * (100 : ℝ)) ≤ 1 / (8 : ℝ) := by
    calc
      _ ≤ exp (-3 : ℝ) := exp_le_exp.mpr (by norm_num)
      _ ≤ _ := by
        rw [exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he3
  nlinarith only [he]

end LeanLab.HelfgottMajor.Decomp503a
