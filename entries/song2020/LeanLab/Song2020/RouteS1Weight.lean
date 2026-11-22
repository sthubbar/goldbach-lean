module

public import LeanLab.Song2020.Characteristic139

/-!
AI wrote the Lean code, 2026-11-15, toward the step s1_lambda_reduction.
Source: Yanbo Song, arXiv 2012.06322 v1, printed page 5, from "For S1, we first observe" to
"We have shown so far".
This file holds the real and complex analysis of the partial summation weight of that step.
The weight at the integer x for the real frequency theta is
  (1/gamma) x^(1-gamma) (e(theta ((x+1)^gamma - x^gamma)) - 1) / log x,
written out inline everywhere, since the lab rules for this step allowed no new definition. The paper
records the facts used here as "a_h << 1/|h|", the bound of e(h(x+1)^gamma - h x^gamma) - 1
by h x^(gamma-1), and "by partial summation".
Binary Goldbach is open; nothing here changes that.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteS1Weight

open LeanLab.Song2020 LeanLab.Song2020.State1562

/-- Song 2020, page 5, the additive character e(x) is multiplicative: e(a + b) = e(a) e(b).
Used to split e(alpha x + h x^gamma) off the weight. -/
theorem eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Song 2020, page 5: the additive character has modulus one. -/
theorem norm_eC (θ : ℝ) : ‖eC θ‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- Song 2020, page 5, the bound behind "e(h(x+1)^gamma - h x^gamma) - 1 << h x^(gamma-1)":
the chord of the unit circle is at most the arc, |e(theta) - 1| at most 2 pi |theta|. -/
theorem norm_eC_sub_one_le (θ : ℝ) : ‖eC θ - 1‖ ≤ 2 * Real.pi * |θ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * θ)
  have e : eC θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

/-- Song 2020, page 5, the same chord bound for two points: |e(a) - e(b)| at most
2 pi |a - b|. Used for the variation of the weight in the partial summation. -/
theorem norm_eC_sub_eC_le (a b : ℝ) : ‖eC a - eC b‖ ≤ 2 * Real.pi * |a - b| := by
  have e : eC a = eC b * eC (a - b) := by
    rw [← eC_add]
    congr 1
    ring
  rw [e, show eC b * eC (a - b) - eC b = eC b * (eC (a - b) - 1) by ring, norm_mul, norm_eC,
    one_mul]
  exact norm_eC_sub_one_le _

/-- Song 2020, page 5, the increment bound for t^s with 0 < s < 1: for x at least 1,
(x+1)^s - x^s lies between 0 and s x^(s-1). The mean value theorem with a decreasing
derivative. Used with s = gamma for the phase and s = 1 - gamma for the weight
c x^(1-gamma). -/
theorem rpow_succ_sub_rpow_le (s x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 ≤ x) :
    0 ≤ (x + 1) ^ s - x ^ s ∧ (x + 1) ^ s - x ^ s ≤ s * x ^ (s - 1) := by
  have hx0 : 0 < x := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ s) (Set.Icc x (x + 1)) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 ht.1)))
  have hderiv : ∀ t ∈ Set.Ioo x (x + 1),
      HasDerivAt (fun t : ℝ => t ^ s) (s * t ^ (s - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hx0 ht.1)))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ s)
    (fun t : ℝ => s * t ^ (s - 1)) (by linarith : x < x + 1) hcont hderiv
  rw [show x + 1 - x = 1 by ring, div_one] at hslope
  have hcle : c ^ (s - 1) ≤ x ^ (s - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 hc.1.le (by linarith)
  refine ⟨?_, ?_⟩
  · have := Real.rpow_le_rpow hx0.le (by linarith : x ≤ x + 1) hs0.le
    linarith
  · rw [← hslope]
    exact mul_le_mul_of_nonneg_left hcle hs0.le

/-- Song 2020, page 5, the second difference of t^gamma, needed for the variation of the
factor e(h((x+1)^gamma - x^gamma)) - 1 in the partial summation: for x at least 1,
|((x+2)^gamma - (x+1)^gamma) - ((x+1)^gamma - x^gamma)| is at most
gamma (1 - gamma) x^(gamma-2). -/
theorem abs_rpow_second_diff_le (γ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx : 1 ≤ x) :
    |((x + 1 + 1) ^ γ - (x + 1) ^ γ) - ((x + 1) ^ γ - x ^ γ)| ≤
      γ * (1 - γ) * x ^ (γ - 2) := by
  have hx0 : 0 < x := by linarith
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => (t + 1) ^ γ - t ^ γ)
      (γ * (t + 1) ^ (γ - 1) - γ * t ^ (γ - 1)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => (t + 1) ^ γ) (γ * (t + 1) ^ (γ - 1)) t :=
      HasDerivAt.comp_add_const t 1
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (by linarith : (0 : ℝ) < t + 1))))
    exact h1.sub (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht)))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => (t + 1) ^ γ - t ^ γ)
    (fun t : ℝ => γ * (t + 1) ^ (γ - 1) - γ * t ^ (γ - 1)) (by linarith : x < x + 1)
    (fun t ht => (hd t (lt_of_lt_of_le hx0 ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (lt_trans hx0 ht.1))
  rw [show x + 1 - x = 1 by ring, div_one] at hslope
  have hc0 : 0 < c := lt_trans hx0 hc.1
  have hcont2 : ContinuousOn (fun t : ℝ => t ^ (γ - 1)) (Set.Icc c (c + 1)) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hc0 ht.1)))
  have hderiv2 : ∀ t ∈ Set.Ioo c (c + 1),
      HasDerivAt (fun t : ℝ => t ^ (γ - 1)) ((γ - 1) * t ^ (γ - 1 - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hc0 ht.1)))
  obtain ⟨d, hdm, hslope2⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (γ - 1))
    (fun t : ℝ => (γ - 1) * t ^ (γ - 1 - 1)) (by linarith : c < c + 1) hcont2 hderiv2
  rw [show c + 1 - c = 1 by ring, div_one] at hslope2
  have hd0 : 0 < d := lt_trans hc0 hdm.1
  have hdle : d ^ (γ - 1 - 1) ≤ x ^ (γ - 1 - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 (by linarith [hc.1, hdm.1]) (by linarith)
  have hdpos : 0 < d ^ (γ - 1 - 1) := Real.rpow_pos_of_pos hd0 _
  have hval : ((x + 1 + 1) ^ γ - (x + 1) ^ γ) - ((x + 1) ^ γ - x ^ γ) =
      -(γ * (1 - γ) * d ^ (γ - 1 - 1)) := by
    linear_combination (-1 : ℝ) * hslope - γ * hslope2
  rw [hval, abs_neg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hγ0.le (by linarith)) hdpos.le),
    show γ - 2 = γ - 1 - 1 by ring]
  exact mul_le_mul_of_nonneg_left hdle (mul_nonneg hγ0.le (by linarith))

/-- Song 2020, page 5, "e(h(x+1)^gamma - h x^gamma) - 1 << h x^(gamma-1)" times the weight
c x^(1-gamma), for a real variable x at least 1: the product has modulus at most 2 pi |theta|.
The real variable form behind `norm_phi_le`. -/
private theorem phi_real (γ θ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx : 1 ≤ x) :
    ‖((1 / γ * x ^ (1 - γ) : ℝ) : ℂ) * (eC (θ * ((x + 1) ^ γ - x ^ γ)) - 1)‖ ≤
      2 * Real.pi * |θ| := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hd0, hd1⟩ := rpow_succ_sub_rpow_le γ x hγ0 hγ1 hx
  have hab : x ^ (1 - γ) * x ^ (γ - 1) = 1 := by
    rw [← Real.rpow_add hx0, show 1 - γ + (γ - 1) = 0 by ring, Real.rpow_zero]
  have ha : 0 < x ^ (1 - γ) := Real.rpow_pos_of_pos hx0 _
  have hg : 1 / γ * γ = 1 := one_div_mul_cancel hγ0.ne'
  have hE := norm_eC_sub_one_le (θ * ((x + 1) ^ γ - x ^ γ))
  rw [abs_mul, abs_of_nonneg hd0] at hE
  have hpi := Real.pi_pos
  have hE' : ‖eC (θ * ((x + 1) ^ γ - x ^ γ)) - 1‖ ≤
      2 * Real.pi * (|θ| * (γ * x ^ (γ - 1))) := by
    refine hE.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd1 (abs_nonneg θ))
      (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine (mul_le_mul_of_nonneg_left hE' (by positivity)).trans (le_of_eq ?_)
  linear_combination (2 * Real.pi * |θ| * (x ^ (1 - γ) * x ^ (γ - 1))) * hg +
    (2 * Real.pi * |θ|) * hab

/-- Song 2020, page 5, "e(h(x+1)^gamma - h x^gamma) - 1 << h x^(gamma-1)" multiplied by the
weight c x^(1-gamma): the product (1/gamma) x^(1-gamma) (e(theta((x+1)^gamma - x^gamma)) - 1)
has modulus at most 2 pi |theta| at every natural number x, including x = 0 where the weight
vanishes. -/
theorem norm_phi_le (γ θ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (x : ℕ) :
    ‖(psWeight γ x : ℂ) * (eC (θ * (((x : ℝ) + 1) ^ γ - (x : ℝ) ^ γ)) - 1)‖ ≤
      2 * Real.pi * |θ| := by
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · subst h0
    have hz : psWeight γ 0 = 0 := by
      unfold psWeight
      rw [Nat.cast_zero, Real.zero_rpow (by linarith : (1 : ℝ) - γ ≠ 0), mul_zero]
    rw [hz, Complex.ofReal_zero, zero_mul, norm_zero]
    have := abs_nonneg θ
    have := Real.pi_pos
    positivity
  · exact phi_real γ θ (x : ℝ) hγ0 hγ1 (by exact_mod_cast hpos)

/-- Song 2020, page 5, the size of the partial summation weight after the passage to the von
Mangoldt function, which divides by log x: at every natural number x the weight has modulus
at most 10 |theta|. Here 2 pi / log 2 < 10, and at x = 0 and x = 1 the quotient is 0 because
Lean divides by zero to zero and the weight at 0 vanishes. -/
theorem norm_weight_le (γ θ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (x : ℕ) :
    ‖(psWeight γ x : ℂ) * (eC (θ * (((x : ℝ) + 1) ^ γ - (x : ℝ) ^ γ)) - 1) /
        ((Real.log (x : ℝ) : ℝ) : ℂ)‖ ≤ 10 * |θ| := by
  rcases Nat.lt_or_ge x 2 with h | h
  · have hz : Real.log (x : ℝ) = 0 := by interval_cases x <;> simp
    rw [hz, Complex.ofReal_zero, div_zero, norm_zero]
    positivity
  · have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    have hl2 : (0.69 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hL : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx2
    have hLpos : 0 < Real.log (x : ℝ) := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos, div_le_iff₀ hLpos]
    have hp := norm_phi_le γ θ hγ0 hγ1 x
    have h1 := mul_le_mul_of_nonneg_right
      (by have := Real.pi_lt_d2; linarith : 2 * Real.pi ≤ 6.3) (abs_nonneg θ)
    have h2 := mul_le_mul_of_nonneg_left (by linarith : (0.69 : ℝ) ≤ Real.log (x : ℝ))
      (by positivity : (0 : ℝ) ≤ 10 * |θ|)
    have := abs_nonneg θ
    linarith

/-- Song 2020, page 5, "by partial summation": the product rule for differences that the
variation of the weight needs. A quotient A (E - 1) / L changes from one point to the next by
((A1 - A0)(E1 - 1) + A0 (E1 - E0)) / L1 + A0 (E0 - 1) (1/L1 - 1/L0), and the triangle
inequality bounds the three pieces. -/
private theorem quotient_step (A1 A0 E1 E0 L1 L0 : ℂ) (c r : ℝ)
    (h1 : ‖A1 - A0‖ * ‖E1 - 1‖ ≤ c * r) (h2 : ‖A0‖ * ‖E1 - E0‖ ≤ c * r)
    (h3 : ‖A0 * (E0 - 1)‖ ≤ c) (h4 : ‖1 / L1‖ ≤ 1.45) (h5 : ‖1 / L1 - 1 / L0‖ ≤ 2.1025 * r)
    (hc : 0 ≤ c) (hr : 0 ≤ r) :
    ‖A1 * (E1 - 1) / L1 - A0 * (E0 - 1) / L0‖ ≤ 5.0025 * c * r := by
  have hcr : 0 ≤ c * r := mul_nonneg hc hr
  calc ‖A1 * (E1 - 1) / L1 - A0 * (E0 - 1) / L0‖
      = ‖((A1 - A0) * (E1 - 1) + A0 * (E1 - E0)) * (1 / L1) +
          A0 * (E0 - 1) * (1 / L1 - 1 / L0)‖ := by
        congr 1
        ring
    _ ≤ (‖A1 - A0‖ * ‖E1 - 1‖ + ‖A0‖ * ‖E1 - E0‖) * ‖1 / L1‖ +
          ‖A0 * (E0 - 1)‖ * ‖1 / L1 - 1 / L0‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul _ (1 / L1 - 1 / L0)]
        refine add_le_add (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) le_rfl
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (c * r + c * r) * 1.45 + c * (2.1025 * r) :=
        add_le_add
          (mul_le_mul (add_le_add h1 h2) h4 (norm_nonneg _) (by linarith))
          (mul_le_mul h3 h5 (norm_nonneg _) hc)
    _ = 5.0025 * c * r := by ring

/-- Song 2020, page 5, "by partial summation": the one step variation of the weight
(1/gamma) x^(1-gamma) (e(theta((x+1)^gamma - x^gamma)) - 1) / log x for a real variable x at
least 2 is at most 40 |theta| / x. The pieces are the increment of x^(1-gamma), the second
difference of x^gamma, and the variation of 1 / log x. The real variable form behind
`norm_weight_succ_sub_le`. -/
private theorem weight_step (γ θ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx : 2 ≤ x) :
    ‖((1 / γ * (x + 1) ^ (1 - γ) : ℝ) : ℂ) *
          (eC (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ)) - 1) / ((Real.log (x + 1) : ℝ) : ℂ) -
        ((1 / γ * x ^ (1 - γ) : ℝ) : ℂ) * (eC (θ * ((x + 1) ^ γ - x ^ γ)) - 1) /
          ((Real.log x : ℝ) : ℂ)‖ ≤ 40 * |θ| / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hθ := abs_nonneg θ
  have hpi := Real.pi_pos
  have hr : 0 < x⁻¹ := inv_pos.mpr hx0
  have ha : 0 < x ^ (1 - γ) := Real.rpow_pos_of_pos hx0 _
  have hb : 0 < x ^ (γ - 1) := Real.rpow_pos_of_pos hx0 _
  have hab : x ^ (1 - γ) * x ^ (γ - 1) = 1 := by
    rw [← Real.rpow_add hx0, show 1 - γ + (γ - 1) = 0 by ring, Real.rpow_zero]
  have hg : 1 / γ * γ = 1 := one_div_mul_cancel hγ0.ne'
  have hg0 : 0 < 1 / γ := one_div_pos.mpr hγ0
  have hP : 0 ≤ 2 * Real.pi * |θ| * x⁻¹ := by positivity
  obtain ⟨hw0, hw1⟩ := rpow_succ_sub_rpow_le (1 - γ) x (by linarith) (by linarith) hx1
  rw [Real.rpow_sub_one hx0.ne' (1 - γ), div_eq_mul_inv] at hw1
  obtain ⟨hd0, hd1⟩ := rpow_succ_sub_rpow_le γ (x + 1) hγ0 hγ1 (by linarith)
  have hb' : (x + 1) ^ (γ - 1) ≤ x ^ (γ - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have hs := abs_rpow_second_diff_le γ x hγ0 hγ1 hx1
  rw [show γ - 2 = γ - 1 - 1 by ring, Real.rpow_sub_one hx0.ne' (γ - 1), div_eq_mul_inv] at hs
  -- first piece
  have hA : ‖((1 / γ * (x + 1) ^ (1 - γ) : ℝ) : ℂ) - ((1 / γ * x ^ (1 - γ) : ℝ) : ℂ)‖ ≤
      1 / γ * ((1 - γ) * (x ^ (1 - γ) * x⁻¹)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_pos hg0, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left hw1 hg0.le
  have hE1 : ‖eC (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ)) - 1‖ ≤
      2 * Real.pi * (|θ| * (γ * x ^ (γ - 1))) := by
    have h := norm_eC_sub_one_le (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ))
    rw [abs_mul, abs_of_nonneg hd0] at h
    refine h.trans ?_
    have h' : (x + 1 + 1) ^ γ - (x + 1) ^ γ ≤ γ * x ^ (γ - 1) :=
      hd1.trans (mul_le_mul_of_nonneg_left hb' hγ0.le)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h' hθ) (by positivity)
  have h1 : ‖((1 / γ * (x + 1) ^ (1 - γ) : ℝ) : ℂ) - ((1 / γ * x ^ (1 - γ) : ℝ) : ℂ)‖ *
      ‖eC (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ)) - 1‖ ≤ 2 * Real.pi * |θ| * x⁻¹ := by
    refine (mul_le_mul hA hE1 (norm_nonneg _) ((norm_nonneg _).trans hA)).trans ?_
    have e : 1 / γ * ((1 - γ) * (x ^ (1 - γ) * x⁻¹)) *
        (2 * Real.pi * (|θ| * (γ * x ^ (γ - 1)))) = 2 * Real.pi * |θ| * x⁻¹ * (1 - γ) := by
      linear_combination
        (2 * Real.pi * |θ| * x⁻¹ * (1 - γ) * (x ^ (1 - γ) * x ^ (γ - 1))) * hg +
          (2 * Real.pi * |θ| * x⁻¹ * (1 - γ)) * hab
    rw [e]
    nlinarith [mul_nonneg hP hγ0.le]
  -- second piece
  have hA0 : ‖((1 / γ * x ^ (1 - γ) : ℝ) : ℂ)‖ = 1 / γ * x ^ (1 - γ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hg0 ha)]
  have hE10 : ‖eC (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ)) - eC (θ * ((x + 1) ^ γ - x ^ γ))‖ ≤
      2 * Real.pi * (|θ| * (γ * (1 - γ) * (x ^ (γ - 1) * x⁻¹))) := by
    have h := norm_eC_sub_eC_le (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ))
      (θ * ((x + 1) ^ γ - x ^ γ))
    rw [← mul_sub, abs_mul] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hθ) (by positivity)
  have h2 : ‖((1 / γ * x ^ (1 - γ) : ℝ) : ℂ)‖ *
      ‖eC (θ * ((x + 1 + 1) ^ γ - (x + 1) ^ γ)) - eC (θ * ((x + 1) ^ γ - x ^ γ))‖ ≤
        2 * Real.pi * |θ| * x⁻¹ := by
    rw [hA0]
    refine (mul_le_mul_of_nonneg_left hE10 (mul_pos hg0 ha).le).trans ?_
    have e : 1 / γ * x ^ (1 - γ) *
        (2 * Real.pi * (|θ| * (γ * (1 - γ) * (x ^ (γ - 1) * x⁻¹)))) =
          2 * Real.pi * |θ| * x⁻¹ * (1 - γ) := by
      linear_combination
        (2 * Real.pi * |θ| * x⁻¹ * (1 - γ) * (x ^ (1 - γ) * x ^ (γ - 1))) * hg +
          (2 * Real.pi * |θ| * x⁻¹ * (1 - γ)) * hab
    rw [e]
    nlinarith [mul_nonneg hP hγ0.le]
  -- third piece
  have h3 := phi_real γ θ x hγ0 hγ1 hx1
  -- logarithms
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hL0 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL1 : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hL0p : 0 < Real.log x := by linarith
  have hL1p : 0 < Real.log (x + 1) := by linarith
  have hu : 1 / Real.log (x + 1) * Real.log (x + 1) = 1 := one_div_mul_cancel hL1p.ne'
  have hv : 1 / Real.log x * Real.log x = 1 := one_div_mul_cancel hL0p.ne'
  have hu0 : 0 < 1 / Real.log (x + 1) := one_div_pos.mpr hL1p
  have hv0 : 0 < 1 / Real.log x := one_div_pos.mpr hL0p
  have hu1 : 1 / Real.log (x + 1) ≤ 1.45 := by
    rw [div_le_iff₀ hL1p]
    linarith
  have hv1 : 1 / Real.log x ≤ 1.45 := by
    rw [div_le_iff₀ hL0p]
    linarith
  have hdl : Real.log (x + 1) - Real.log x ≤ x⁻¹ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have e : (x + 1) / x - 1 = x⁻¹ := by
      rw [add_div, div_self hx0.ne', one_div]
      ring
    linarith
  have h4 : ‖(1 : ℂ) / ((Real.log (x + 1) : ℝ) : ℂ)‖ ≤ 1.45 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL1p]
    exact hu1
  have key : 1 / Real.log x - 1 / Real.log (x + 1) =
      1 / Real.log (x + 1) * (1 / Real.log x) * (Real.log (x + 1) - Real.log x) := by
    linear_combination (-(1 / Real.log x)) * hu + (1 / Real.log (x + 1)) * hv
  have h5 : ‖(1 : ℂ) / ((Real.log (x + 1) : ℝ) : ℂ) - 1 / ((Real.log x : ℝ) : ℂ)‖ ≤
      2.1025 * x⁻¹ := by
    have e : (1 : ℂ) / ((Real.log (x + 1) : ℝ) : ℂ) - 1 / ((Real.log x : ℝ) : ℂ) =
        ((1 / Real.log (x + 1) - 1 / Real.log x : ℝ) : ℂ) := by
      push_cast
      rfl
    have hnn : 0 ≤ 1 / Real.log x - 1 / Real.log (x + 1) := by
      rw [key]
      exact mul_nonneg (mul_nonneg hu0.le hv0.le) (sub_nonneg.mpr hL1)
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hnn, key]
    calc 1 / Real.log (x + 1) * (1 / Real.log x) * (Real.log (x + 1) - Real.log x)
        ≤ 1.45 * 1.45 * x⁻¹ :=
          mul_le_mul (mul_le_mul hu1 hv1 hv0.le (by norm_num)) hdl (sub_nonneg.mpr hL1)
            (by norm_num)
      _ = 2.1025 * x⁻¹ := by ring
  have hfin := quotient_step _ _ _ _ _ _ (2 * Real.pi * |θ|) x⁻¹ h1 h2 h3 h4 h5
    (by positivity) hr.le
  refine hfin.trans ?_
  rw [div_eq_mul_inv]
  have hθr : 0 ≤ |θ| * x⁻¹ := mul_nonneg hθ hr.le
  have h6 := mul_le_mul_of_nonneg_right (Real.pi_lt_d2.le) hθr
  nlinarith

/-- Song 2020, page 5, the one step variation of the partial summation weight: for a natural
number x at least 1 the weight changes by at most 40 |theta| / x from x to x + 1. For x at
least 2 this is the product rule for differences with the increment bound for x^(1-gamma),
the second difference bound for x^gamma, and the variation of 1 / log x, giving
(4 pi / log 2 + 2 pi / (log 2)^2) |theta| / x; for x = 1 the weight at 1 is 0 and the
weight at 2 is at most 2 pi |theta| / log 2. -/
theorem norm_weight_succ_sub_le (γ θ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖(psWeight γ (x + 1) : ℂ) *
          (eC (θ * ((((x + 1 : ℕ) : ℝ) + 1) ^ γ - ((x + 1 : ℕ) : ℝ) ^ γ)) - 1) /
          ((Real.log ((x + 1 : ℕ) : ℝ) : ℝ) : ℂ) -
        (psWeight γ x : ℂ) * (eC (θ * (((x : ℝ) + 1) ^ γ - (x : ℝ) ^ γ)) - 1) /
          ((Real.log (x : ℝ) : ℝ) : ℂ)‖ ≤ 40 * |θ| / (x : ℝ) := by
  rcases Nat.lt_or_ge x 2 with h | h
  · have hx1 : x = 1 := by omega
    subst hx1
    have h2 := norm_weight_le γ θ hγ0 hγ1 (1 + 1)
    have hz : (psWeight γ 1 : ℂ) *
        (eC (θ * ((((1 : ℕ) : ℝ) + 1) ^ γ - ((1 : ℕ) : ℝ) ^ γ)) - 1) /
          ((Real.log ((1 : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by simp
    rw [hz, sub_zero]
    refine h2.trans ?_
    have := abs_nonneg θ
    rw [Nat.cast_one, div_one]
    linarith
  · have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    have hstep := weight_step γ θ (x : ℝ) hγ0 hγ1 hx2
    simp only [psWeight, Nat.cast_add, Nat.cast_one]
    exact hstep

/-- Song 2020, page 5, the algebra behind the display for Delta psi prime: with theta = -h,
the weight times e(alpha p) times the difference e(h(-(p+1)^gamma)) - e(h(-p^gamma)) is the
factor (1/gamma) p^(1-gamma) (e(theta((p+1)^gamma - p^gamma)) - 1) times
e(alpha p + theta p^gamma). -/
theorem term_identity (γ α θ : ℝ) (p : ℕ) :
    (psWeight γ p : ℂ) * eC (α * p) *
        (eC (-θ * (-((p : ℝ) + 1) ^ γ)) - eC (-θ * (-(p : ℝ) ^ γ))) =
      ((psWeight γ p : ℂ) * (eC (θ * (((p : ℝ) + 1) ^ γ - (p : ℝ) ^ γ)) - 1)) *
        eC (α * p + θ * (p : ℝ) ^ γ) := by
  have h1 : eC (-θ * (-((p : ℝ) + 1) ^ γ)) =
      eC (θ * (p : ℝ) ^ γ) * eC (θ * (((p : ℝ) + 1) ^ γ - (p : ℝ) ^ γ)) := by
    rw [← eC_add]
    congr 1
    ring
  have h2 : eC (-θ * (-(p : ℝ) ^ γ)) = eC (θ * (p : ℝ) ^ γ) := by
    congr 1
    ring
  rw [h1, h2, eC_add]
  ring

/-- Song 2020, page 5, the loss the total variation of the weight costs when the window
reaches down to small x: 1 + log n is at most (1 + 1/epsilon) n^epsilon for n at least 1.
This is why the reduction carries the factor n^epsilon. -/
theorem one_add_log_le_rpow (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    1 + Real.log (n : ℝ) ≤ (1 + 1 / ε) * (n : ℝ) ^ ε := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  have h2 : Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have e : (1 + 1 / ε) * (n : ℝ) ^ ε = (n : ℝ) ^ ε + (n : ℝ) ^ ε / ε := by ring
  rw [e]
  linarith

end LeanLab.Song2020.RouteS1Weight
