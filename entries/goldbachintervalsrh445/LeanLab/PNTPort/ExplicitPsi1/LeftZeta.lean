module

public import LeanLab.PNTPort.ZetaZeros.LeftLine

/-!
# ζ on the far left: no zeros off the trivial ones, and `ζ'/ζ` on the lines `Re s = -2K - 1/2`

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6551. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input. From Mathlib's functional equation
`ζ'/ζ(s) = -ζ'/ζ(1 - s) + log 2π - ψ(s) + (π/2) tan(πs/2)`:

* `zeta_ne_zero_of_re_neg`: `ζ(s) ≠ 0` for `Re s < 0` unless `s = -2k`;
* `zero_of_re_neg`: a zero with `Re s < 0` is `-2(n + 1)`;
* `logDeriv_left_region`: `‖ζ'/ζ(σ + it)‖ ≤ A log(|t| + 3) - σ + A` for `σ ≤ -1/2`, `|t| ≥ 1`;
* `logDeriv_line`: `‖ζ'/ζ(-2K - 1/2 + it)‖ ≤ A log(|t| + 3) + 4K + A` for every `K` and `t`;
* `logDeriv_zeta_neg_one`: `ζ'/ζ(-1) = log 2π - 1 + γ - ζ'/ζ(2)`.

These are the inputs for moving the left edge of the ψ₁ explicit formula to `-∞`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex Set Filter Metric Topology
open scoped Real ComplexConjugate
open LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

/-- `ζ(s) ≠ 0` for `Re s < 0` when `1 - s` is not an odd integer. -/
lemma zeta_ne_zero_of_re_neg {s : ℂ} (hre : s.re < 0) (hodd : ∀ k : ℤ, 1 - s ≠ 2 * k + 1) :
    ζ s ≠ 0 := by
  set w : ℂ := 1 - s with hw
  have hwre : 1 < w.re := by rw [hw]; simp; linarith
  have hw1 : w ≠ 1 := by intro h; rw [h] at hwre; simp at hwre
  have := riemannZeta_one_sub (not_neg_nat_of_re_pos (by linarith)) hw1
  rw [show 1 - w = s by rw [hw]; ring] at this
  rw [this]
  exact mul_ne_zero (feF_ne_zero (by linarith) hodd) (riemannZeta_ne_zero_of_one_lt_re hwre)

/-- A zero of ζ with negative real part is a trivial zero `-2(n + 1)`. -/
lemma zero_of_re_neg {s : ℂ} (hre : s.re < 0) (hz : ζ s = 0) : ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  by_contra hne
  refine zeta_ne_zero_of_re_neg hre (fun k hk => hne ?_) hz
  have hs : s = -2 * (k : ℂ) := by linear_combination -hk
  have hk0 : 0 < k := by
    have h := congr_arg Complex.re hs
    simp at h
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  refine ⟨(k - 1).toNat, ?_⟩
  have hn : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have hn' : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    rw [show (((k - 1).toNat : ℕ) : ℂ) = ((((k - 1).toNat : ℕ) : ℤ) : ℂ) by push_cast; rfl, hn]
    push_cast; ring
  rw [hs, hn']; ring

lemma norm_log_two_pi_le : ‖Complex.log (2 * π)‖ ≤ 2 := by
  rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
  exact log_two_pi_le

/-- `‖ζ'/ζ(u)‖ ≤ c₀ = ‖ζ'/ζ(3/2)‖` for `Re u ≥ 3/2`. -/
lemma logDeriv_right_le {u : ℂ} (hu : 3 / 2 ≤ u.re) :
    ‖deriv ζ u / ζ u‖ ≤ ‖deriv ζ ((3 / 2 : ℝ) : ℂ) / ζ ((3 / 2 : ℝ) : ℂ)‖ := by
  have h := dlog_riemannZeta_bdd_on_vertical_lines_generalized (3 / 2) u.re u.im (by norm_num) hu
  have e : (u.re : ℂ) + u.im * I = u := re_add_im u
  rw [e, neg_div, norm_neg] at h
  exact h

/-- The functional equation pieces for `σ ≤ -1/2`, `t ≥ 1`. -/
lemma logDeriv_left_pos : ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, σ ≤ -1 / 2 → 1 ≤ t →
    ‖deriv ζ ((σ : ℂ) + t * I) / ζ ((σ : ℂ) + t * I)‖ ≤ A * Real.log (t + 3) - σ + A := by
  obtain ⟨K, hK, hψ⟩ := digamma_strip
  set c0 := ‖deriv ζ ((3 / 2 : ℝ) : ℂ) / ζ ((3 / 2 : ℝ) : ℂ)‖ with hc0
  have hc0p : 0 ≤ c0 := norm_nonneg _
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  refine ⟨c0 + K + 9, by positivity, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsim : s.im = t := by simp [hs]
  have hsre : s.re = σ := by simp [hs]
  have hζs : ζ s ≠ 0 := zeta_ne_zero_of_re_nonpos (by rw [hsre]; linarith) (by rw [hsim]; linarith)
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h; have := congr_arg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hFE := logDeriv_riemannZeta_one_sub hint hζs
  rw [logDeriv_apply, logDeriv_apply] at hFE
  have hlt : 1 ≤ Real.log (t + 3) := le_trans hl3 (Real.log_le_log (by norm_num) (by linarith))
  have h1 : ‖deriv ζ (1 - s) / ζ (1 - s)‖ ≤ c0 := logDeriv_right_le (by simp [hs]; linarith)
  -- ψ(s) through the shift by `n = ⌈-σ⌉₊`
  set n : ℕ := ⌈-σ⌉₊ with hn
  have hn1 : -σ ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < -σ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnm : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h; have := congr_arg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hsh := digamma_apply_add_nat hnm n
  have hsn : s + n = ((σ + n : ℝ) : ℂ) + t * I := by rw [hs]; push_cast; ring
  have hψn : ‖digamma (s + n)‖ ≤ K * Real.log (t + 3) + 2 := by
    rw [hsn]; exact hψ t ht (σ + n) (by linarith) (by linarith)
  have hsum : ‖∑ k ∈ Finset.range n, (s + k)⁻¹‖ ≤ n := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range n, ‖(s + k)⁻¹‖ ≤ 1 := by
      intro k _
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have := Complex.abs_im_le_norm (s + k)
      simp [hsim] at this
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    calc ∑ k ∈ Finset.range n, ‖(s + k)⁻¹‖ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum this
      _ = n := by simp
  have h3 : ‖digamma s‖ ≤ K * Real.log (t + 3) + 2 + n := by
    have e : digamma s = digamma (s + n) - ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
      rw [hsh]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add hψn hsum)
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    have e : (π : ℂ) * s / 2 = ((π * σ / 2 : ℝ) : ℂ) + ((π * t / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [e, norm_mul]
    have ht' := norm_tan_le (x := π * σ / 2) (y := π * t / 2) (by nlinarith [Real.pi_gt_three])
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
    _ ≤ c0 + 2 + (K * Real.log (t + 3) + 2 + n) + 4 :=
        add_le_add (add_le_add (add_le_add h1 norm_log_two_pi_le) h3) h4
    _ ≤ (c0 + K + 9) * Real.log (t + 3) - σ + (c0 + K + 9) := by nlinarith

/-- **`‖ζ'/ζ(σ + it)‖ ≤ A log(|t| + 3) - σ + A` for `σ ≤ -1/2`, `|t| ≥ 1`.** -/
theorem logDeriv_left_region : ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, σ ≤ -1 / 2 → 1 ≤ |t| →
    ζ ((σ : ℂ) + t * I) ≠ 0 ∧
    ‖deriv ζ ((σ : ℂ) + t * I) / ζ ((σ : ℂ) + t * I)‖ ≤ A * Real.log (|t| + 3) - σ + A := by
  obtain ⟨A, hA, hpos⟩ := logDeriv_left_pos
  refine ⟨A, hA, fun σ t hσ ht => ⟨?_, ?_⟩⟩
  · apply zeta_ne_zero_of_re_nonpos (by simp; linarith)
    simp
    intro h; rw [h] at ht; simp at ht; linarith
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact hpos σ t hσ ht
  · rw [abs_of_neg h] at ht ⊢
    have hconj : (σ : ℂ) + t * I = conj ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [hconj]
    have hc := logDerivZeta_conj ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)
    simp only [Pi.div_apply] at hc
    rw [hc, Complex.norm_conj]
    exact hpos σ (-t) hσ ht

/-- `|tan(-π/4 + iy)| ≤ 1`. -/
lemma norm_tan_quarter (y : ℝ) : ‖Complex.tan (((-(π / 4)) : ℝ) + y * I)‖ ≤ 1 := by
  have hs : Real.sin (-(π / 4)) = -(√2 / 2) := by rw [Real.sin_neg, Real.sin_pi_div_four]
  have hc : Real.cos (-(π / 4)) = √2 / 2 := by rw [Real.cos_neg, Real.cos_pi_div_four]
  have h2 : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hcos : Complex.cos (((-(π / 4)) : ℝ) + y * I) =
      ((Real.cos (-(π / 4)) * Real.cosh y : ℝ) : ℂ) +
        ((-(Real.sin (-(π / 4)) * Real.sinh y) : ℝ) : ℂ) * I := by
    rw [Complex.cos_add_mul_I]; push_cast; ring
  have hsin : Complex.sin (((-(π / 4)) : ℝ) + y * I) =
      ((Real.sin (-(π / 4)) * Real.cosh y : ℝ) : ℂ) +
        ((Real.cos (-(π / 4)) * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]; push_cast; ring
  have heq : ‖Complex.sin (((-(π / 4)) : ℝ) + y * I)‖ ^ 2 =
      ‖Complex.cos (((-(π / 4)) : ℝ) + y * I)‖ ^ 2 := by
    rw [hsin, hcos, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add_mul_I, Complex.normSq_add_mul_I, hs, hc]
    ring
  have hcpos : 0 < ‖Complex.cos (((-(π / 4)) : ℝ) + y * I)‖ := by
    rw [hcos, norm_pos_iff]
    intro h
    have h' := congr_arg Complex.re h
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, zero_re] at h'
    rw [hc] at h'
    have : 0 < √2 / 2 * Real.cosh y := by
      have := Real.cosh_pos y; positivity
    linarith
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_one hcpos]
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hcpos.le (le_of_eq heq)

/-- `digamma` is bounded on `3/2 + it`, `|t| ≤ 1`. -/
lemma digamma_three_half_bdd : ∃ M : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1,
    ‖digamma (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ M := by
  have hcont : ContinuousOn (fun t : ℝ => digamma (((3 / 2 : ℝ) : ℂ) + t * I)) (Icc (-1) 1) := by
    intro t _
    have hre : 0 < ((((3 / 2 : ℝ) : ℂ) + t * I)).re := by norm_num
    have hA := gamma_analyticAt hre
    have hG := gamma_ne_zero_of_re_pos hre
    have hcomp : ContinuousAt (fun t : ℝ => ((3 / 2 : ℝ) : ℂ) + t * I) t := by fun_prop
    have h1 := ContinuousAt.comp (g := deriv Gamma) (f := fun t : ℝ => ((3 / 2 : ℝ) : ℂ) + t * I)
      (x := t) hA.deriv.continuousAt hcomp
    have h2 := ContinuousAt.comp (g := Gamma) (f := fun t : ℝ => ((3 / 2 : ℝ) : ℂ) + t * I)
      (x := t) hA.continuousAt hcomp
    have h3 := h1.div h2 hG
    refine (h3.congr (Eventually.of_forall fun u => ?_)).continuousWithinAt
    simp only [Pi.div_apply, Function.comp_apply, digamma_def, logDeriv_apply]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨M, hM⟩

/-- The real part `-2K - 1/2 + j` is at distance at least `1/2` from 0. -/
lemma half_le_abs_line (K j : ℕ) : 1 / 2 ≤ |(-2 * (K : ℝ) - 1 / 2) + j| := by
  rcases le_or_gt j (2 * K) with h | h
  · have : (j : ℝ) ≤ 2 * K := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith
  · have : (2 * K + 1 : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith

/-- **`‖ζ'/ζ(-2K - 1/2 + it)‖ ≤ A log(|t| + 3) + 4K + A` for every `K` and every real `t`**, and ζ
has no zero on these lines. -/
theorem logDeriv_line : ∃ A : ℝ, 0 < A ∧ ∀ K : ℕ, ∀ t : ℝ,
    ζ (((-2 * (K : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 ∧
    ‖deriv ζ (((-2 * (K : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I) /
      ζ (((-2 * (K : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ A * Real.log (|t| + 3) + 4 * K + A := by
  obtain ⟨A1, hA1, hreg⟩ := logDeriv_left_region
  obtain ⟨M, hM⟩ := digamma_three_half_bdd
  set c0 := ‖deriv ζ ((3 / 2 : ℝ) : ℂ) / ζ ((3 / 2 : ℝ) : ℂ)‖ with hc0
  have hc0p : 0 ≤ c0 := norm_nonneg _
  refine ⟨A1 + c0 + |M| + 10, by positivity, fun K t => ?_⟩
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hl0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hKp : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- `s` is not an integer and `1 - s` is not an odd integer
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h
    have := congr_arg Complex.re h
    rw [hsre] at this; simp at this
    have h4 : (4 * K + 1 : ℤ) = -2 * n := by
      have : ((4 * K + 1 : ℤ) : ℝ) = ((-2 * n : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hodd : ∀ k : ℤ, 1 - s ≠ 2 * k + 1 := by
    intro k h
    have := congr_arg Complex.re h
    simp [hsre] at this
    have h4 : (4 * K + 1 : ℤ) = 4 * k := by
      have : ((4 * K + 1 : ℤ) : ℝ) = ((4 * k : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hζs : ζ s ≠ 0 := zeta_ne_zero_of_re_neg (by rw [hsre]; linarith) hodd
  refine ⟨hζs, ?_⟩
  rcases le_or_gt 1 |t| with ht | ht
  · have := (hreg σ t (by linarith) ht).2
    calc _ ≤ A1 * Real.log (|t| + 3) - σ + A1 := this
      _ ≤ _ := by rw [hσ]; nlinarith [abs_nonneg M]
  -- `|t| < 1`: the functional equation with the shift by `2K + 2`
  have hFE := logDeriv_riemannZeta_one_sub hint hζs
  rw [logDeriv_apply, logDeriv_apply] at hFE
  have h1 : ‖deriv ζ (1 - s) / ζ (1 - s)‖ ≤ c0 := logDeriv_right_le (by simp [hs, hσ]; linarith)
  have hnm : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h; exact hint (-(m : ℤ)) (by rw [h]; push_cast; ring)
  have hsh := digamma_apply_add_nat hnm (2 * K + 2)
  have hsn : s + ((2 * K + 2 : ℕ) : ℂ) = ((3 / 2 : ℝ) : ℂ) + t * I := by
    rw [hs, hσ]; push_cast; ring
  have hψn : ‖digamma (s + ((2 * K + 2 : ℕ) : ℂ))‖ ≤ |M| := by
    rw [hsn]
    exact (hM t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).trans (le_abs_self M)
  have hsum : ‖∑ k ∈ Finset.range (2 * K + 2), (s + k)⁻¹‖ ≤ 2 * (2 * K + 2) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range (2 * K + 2), ‖(s + k)⁻¹‖ ≤ 2 := by
      intro k _
      rw [norm_inv]
      have hre := Complex.abs_re_le_norm (s + k)
      simp only [add_re, natCast_re, hsre] at hre
      have := half_le_abs_line K k
      rw [hσ] at hre
      have hpos : 0 < ‖s + k‖ := by linarith
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    calc ∑ k ∈ Finset.range (2 * K + 2), ‖(s + k)⁻¹‖
        ≤ ∑ _k ∈ Finset.range (2 * K + 2), (2 : ℝ) := Finset.sum_le_sum this
      _ = 2 * (2 * K + 2) := by simp; ring
  have h3 : ‖digamma s‖ ≤ |M| + 2 * (2 * K + 2) := by
    have e : digamma s = digamma (s + ((2 * K + 2 : ℕ) : ℂ)) -
        ∑ k ∈ Finset.range (2 * K + 2), (s + k)⁻¹ := by
      rw [hsh]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add hψn hsum)
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 2 := by
    have e : (π : ℂ) * s / 2 = ((((-(π / 4)) : ℝ) : ℂ) + ((π * t / 2 : ℝ) : ℂ) * I) -
        (K : ℂ) * π := by
      rw [hs, hσ]; push_cast; ring
    rw [e, Complex.tan_sub_nat_mul_pi, norm_mul]
    have hp : ‖(π : ℂ) / 2‖ ≤ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num; linarith [Real.pi_lt_four]
    calc _ ≤ 2 * 1 := mul_le_mul hp (norm_tan_quarter _) (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  rw [hFE]
  calc ‖-(deriv ζ (1 - s) / ζ (1 - s)) + Complex.log (2 * π) - digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖deriv ζ (1 - s) / ζ (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖digamma s‖ +
        ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (by rw [norm_neg])) le_rfl)) le_rfl)
    _ ≤ c0 + 2 + (|M| + 2 * (2 * K + 2)) + 2 :=
        add_le_add (add_le_add (add_le_add h1 norm_log_two_pi_le) h3) h4
    _ ≤ _ := by nlinarith [abs_nonneg M]

/-- `ψ(2) = 1 - γ`. -/
lemma digamma_two : digamma 2 = 1 - Real.eulerMascheroniConstant := by
  have := digamma_nat_add_one 1
  norm_num at this
  exact this

/-- **`ζ'/ζ(-1) = log 2π - 1 + γ - ζ'/ζ(2)`**, the functional equation at `s = 2` by continuity. -/
theorem logDeriv_zeta_neg_one :
    deriv ζ (-1) / ζ (-1) =
      Complex.log (2 * π) - 1 + Real.eulerMascheroniConstant - deriv ζ 2 / ζ 2 := by
  -- both sides of the functional equation, as functions of `s`, are continuous at 2
  set g : ℂ → ℂ := fun s => deriv ζ (1 - s) / ζ (1 - s) with hg
  set h : ℂ → ℂ := fun s => -(deriv ζ s / ζ s) + Complex.log (2 * π) - digamma s +
    π / 2 * Complex.tan (π * s / 2) with hh
  have hζm1 : ζ (-1) ≠ 0 := by
    have := riemannZeta_neg_nat_eq_bernoulli' 1
    rw [show ((-(1 : ℕ) : ℂ)) = -1 by push_cast; ring] at this
    rw [this]; norm_num [bernoulli'_two]
  have hζ2 : ζ 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg2 : ContinuousAt g 2 := by
    have hA : AnalyticAt ℂ ζ (1 - 2) := analyticAt_riemannZeta (by norm_num)
    have hc : ContinuousAt (fun s : ℂ => 1 - s) 2 := by fun_prop
    have e : (1 : ℂ) - 2 = -1 := by norm_num
    have h1 := ContinuousAt.comp (g := deriv ζ) (x := 2) (by rw [e] at hA ⊢; exact hA.deriv.continuousAt) hc
    have h2 := ContinuousAt.comp (g := ζ) (x := 2) (by rw [e] at hA ⊢; exact hA.continuousAt) hc
    exact h1.div h2 (by rw [e]; exact hζm1)
  have hh2 : ContinuousAt h 2 := by
    have hA : AnalyticAt ℂ ζ 2 := analyticAt_riemannZeta (by norm_num)
    have hL : ContinuousAt (fun s => deriv ζ s / ζ s) 2 :=
      hA.deriv.continuousAt.div hA.continuousAt hζ2
    have hΓ : AnalyticAt ℂ Gamma 2 := gamma_analyticAt (by norm_num)
    have hΓ0 : Gamma 2 ≠ 0 := gamma_ne_zero_of_re_pos (by norm_num)
    have hψ : ContinuousAt digamma 2 := by
      have := hΓ.deriv.continuousAt.div hΓ.continuousAt hΓ0
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [Pi.div_apply, digamma_def, logDeriv_apply]
    have hcos : Complex.cos (π * 2 / 2) ≠ 0 := by
      rw [show (π : ℂ) * 2 / 2 = π by ring, Complex.cos_pi]; norm_num
    have htan : ContinuousAt (fun s : ℂ => Complex.tan (π * s / 2)) 2 := by
      have hc : ContinuousAt (fun s : ℂ => (π : ℂ) * s / 2) 2 := by fun_prop
      exact ContinuousAt.comp (g := Complex.tan) (x := 2) (Complex.continuousAt_tan.mpr hcos) hc
    exact ((hL.neg.add continuousAt_const).sub hψ).add (continuousAt_const.mul htan)
  -- they agree off the integers near 2
  have hev : g =ᶠ[𝓝[≠] (2 : ℂ)] h := by
    have hball : ball (2 : ℂ) (1 / 2) ∈ 𝓝 (2 : ℂ) := ball_mem_nhds _ (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with s hs hs2
    have hs2' : s ≠ 2 := hs2
    rw [mem_ball, dist_eq_norm] at hs
    have hre := Complex.abs_re_le_norm (s - 2)
    rw [sub_re, show (2 : ℂ).re = 2 by norm_num] at hre
    have hsre : 3 / 2 < s.re := by
      have : |s.re - 2| < 1 / 2 := lt_of_le_of_lt hre hs
      rw [abs_lt] at this; linarith
    have hint : ∀ n : ℤ, s ≠ n := by
      intro n hn
      apply hs2'
      have hn2 : ‖(n : ℂ) - 2‖ < 1 / 2 := by rw [← hn]; exact hs
      have : |(n : ℝ) - 2| < 1 / 2 := by
        have e : ((n : ℂ) - 2) = (((n : ℝ) - 2 : ℝ) : ℂ) := by push_cast; ring
        rw [e, Complex.norm_real, Real.norm_eq_abs] at hn2; exact hn2
      rw [abs_lt] at this
      have h1 : (1 : ℝ) < n := by linarith
      have h3 : (n : ℝ) < 3 := by linarith
      have : n = 2 := by
        have : (1 : ℤ) < n := by exact_mod_cast h1
        have : n < (3 : ℤ) := by exact_mod_cast h3
        omega
      rw [hn, this]; norm_num
    have hζs : ζ s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    have hFE := logDeriv_riemannZeta_one_sub hint hζs
    rw [logDeriv_apply, logDeriv_apply] at hFE
    simp only [hg, hh]
    linear_combination hFE
  have hlim1 : Tendsto g (𝓝[≠] (2 : ℂ)) (𝓝 (g 2)) := hg2.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto g (𝓝[≠] (2 : ℂ)) (𝓝 (h 2)) :=
    (hh2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  have heq := tendsto_nhds_unique hlim1 hlim2
  simp only [hg, hh] at heq
  rw [show (1 : ℂ) - 2 = -1 by norm_num, digamma_two,
    show (π : ℂ) * 2 / 2 = π by ring] at heq
  have htp : Complex.tan (π : ℂ) = 0 := by
    rw [Complex.tan_eq_sin_div_cos, Complex.sin_pi, zero_div]
  rw [htp] at heq
  rw [heq]; ring

end LeanLab.PNTPort.ExplicitPsi1.Trivial
