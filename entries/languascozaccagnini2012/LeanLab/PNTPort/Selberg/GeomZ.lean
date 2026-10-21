module

public import Mathlib

/-!
# The geometric series against `1/z`

Lab proof, unit U-6006, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058 Lemma 1.
AI wrote this file. Elementary, no cited input.

For `z` with `0 < Re z ≤ 1` and `abs(Im z) ≤ π`:

* `norm_one_sub_exp_neg_sq`: `abs(1 - e^{-z})² ≥ abs(z)²/7`, from
  `abs(1 - re^{-iy})² = (1 - r)² + 2r(1 - cos y)`, `1 - e^{-x} ≥ x/2` and
  `cos y ≤ 1 - 2y²/π²` on `[-π, π]`;
* `geom_sub_inv_le`: `abs(1/(1 - e^{-z}) - 1/z) ≤ 8`.

Use: with `z = 1/N - 2πiα` and `abs(α) ≤ 1/2`, `1/(1 - e^{-z}) = Σ_{n≥0} e^{-n/N} e(nα)`, so the
`1/z` of P0058's `S̃(α) - 1/z` differs from the weighted sum of `1`s by at most `8`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex

/-- **The lower bound for `1 - e^{-z}`.** -/
lemma norm_one_sub_exp_neg_sq {z : ℂ} (hx0 : 0 < z.re) (hx1 : z.re ≤ 1)
    (hy : |z.im| ≤ Real.pi) : ‖z‖ ^ 2 / 7 ≤ ‖1 - cexp (-z)‖ ^ 2 := by
  set x := z.re with hx
  set y := z.im with hyd
  set r := Real.exp (-x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := by rw [hr, Real.exp_le_one_iff]; linarith
  have hre : (1 - cexp (-z)).re = 1 - r * Real.cos y := by
    simp [Complex.exp_re, hr, hx, hyd]
  have him : (1 - cexp (-z)).im = r * Real.sin y := by
    simp [Complex.exp_im, hr, hx, hyd]
  have hnorm : ‖1 - cexp (-z)‖ ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos y) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have := Real.sin_sq_add_cos_sq y
    nlinarith
  have hz : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  -- `1 - r ≥ x/2`
  have h1 : x / 2 ≤ 1 - r := by
    have he : r ≤ 1 / (1 + x) := by
      rw [hr, Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp x])
    have : x / 2 ≤ 1 - 1 / (1 + x) := by
      rw [show 1 - 1 / (1 + x) = x / (1 + x) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith
  -- `r ≥ e^{-1}`, `e < 2.72`, `π² < 9.87`
  have hr' : Real.exp (-1) ≤ r := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1 / 2.72 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hcos := Real.cos_le_one_sub_mul_cos_sq hy
  have hpi2 : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hpi0 : 0 < Real.pi ^ 2 := by positivity
  have hc : 2 / 9.87 * y ^ 2 ≤ 1 - Real.cos y := by
    have : 2 / 9.87 * y ^ 2 ≤ 2 / Real.pi ^ 2 * y ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg y)
      exact div_le_div_of_nonneg_left (by norm_num) hpi0 hpi2.le
    linarith
  have hcos0 : 0 ≤ 1 - Real.cos y := by linarith [Real.cos_le_one y]
  have hx2 : x ^ 2 / 4 ≤ (1 - r) ^ 2 := by
    have : 0 ≤ x / 2 := by positivity
    nlinarith
  have hy2 : 2 * (1 / 2.72) * (2 / 9.87 * y ^ 2) ≤ 2 * r * (1 - Real.cos y) := by
    have := mul_le_mul (he1.trans hr') hc (by positivity) hr0.le
    nlinarith
  rw [hnorm, hz]
  nlinarith [sq_nonneg x, sq_nonneg y]

/-- **`1/(1 - e^{-z})` against `1/z`.** -/
theorem geom_sub_inv_le {z : ℂ} (hx0 : 0 < z.re) (hx1 : z.re ≤ 1) (hy : |z.im| ≤ Real.pi) :
    ‖1 / (1 - cexp (-z)) - 1 / z‖ ≤ 8 := by
  have hlow := norm_one_sub_exp_neg_sq hx0 hx1 hy
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hx0; exact lt_irrefl 0 hx0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hd0 : 0 < ‖1 - cexp (-z)‖ := by
    have : 0 < ‖1 - cexp (-z)‖ ^ 2 := lt_of_lt_of_le (by positivity) hlow
    by_contra h
    push_neg at h
    have h0 : ‖1 - cexp (-z)‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [h0] at this
    norm_num at this
  have hd : 1 - cexp (-z) ≠ 0 := norm_pos_iff.mp hd0
  have heq : 1 / (1 - cexp (-z)) - 1 / z = (cexp (-z) - 1 + z) / (z * (1 - cexp (-z))) := by
    field_simp; ring
  -- the numerator
  have hnum : ‖cexp (-z) - 1 + z‖ ≤ 3 * ‖z‖ ^ 2 := by
    rcases le_or_gt ‖z‖ 1 with h | h
    · have := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by rw [norm_neg]; exact h)
      rw [norm_neg, show cexp (-z) - 1 - -z = cexp (-z) - 1 + z by ring] at this
      nlinarith [sq_nonneg ‖z‖]
    · have he : ‖cexp (-z)‖ ≤ 1 := by
        rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]; linarith
      calc ‖cexp (-z) - 1 + z‖ ≤ ‖cexp (-z)‖ + ‖(1 : ℂ)‖ + ‖z‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ ≤ 1 + 1 + ‖z‖ := by rw [norm_one]; linarith
        _ ≤ 3 * ‖z‖ ^ 2 := by nlinarith
  rw [heq, norm_div, norm_mul, div_le_iff₀ (by positivity)]
  -- `3‖z‖² ≤ 8 ‖z‖ ‖1 - e^{-z}‖`, from `‖1 - e^{-z}‖² ≥ ‖z‖²/7`
  have hsq : (3 * ‖z‖) ^ 2 ≤ (8 * ‖1 - cexp (-z)‖) ^ 2 := by nlinarith
  have h3 : 3 * ‖z‖ ≤ 8 * ‖1 - cexp (-z)‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  nlinarith

end LeanLab.PNTPort.Selberg

