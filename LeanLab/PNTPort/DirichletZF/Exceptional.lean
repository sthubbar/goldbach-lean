module

public import LeanLab.PNTPort.DirichletZF.ZeroFreeAll

/-!
# At most one exceptional character modulo `N`

Lab proof, unit U-5110. AI wrote this file. Known mathematics, Landau's argument,
Montgomery-Vaughan Theorem 11.4 in the form without the reality of the zero; no cited input.

* `box_zero_bound`: a zero in the box `β ≥ 1 - η`, `|γ| ≤ η` with `η ≤ 1/31` forces
  `-Re L'/L(1 + 2η, χ) ≤ K₀ log B(0) - 4/(15η)`;
* `four_nonneg`: for real characters `χ₁, χ₂`, the series of
  `Λ(n)(1 + χ₁(n))(1 + χ₂(n)) n^{-σ}` has nonnegative real part;
* `one_exceptional`: there is an absolute `c₅ > 0` such that for every `N`, two non-principal
  characters mod `N` that both have a zero in the box of size `c₅ / log B(0)` are equal;
* `zero_free_region_all`: absolute `c, c' > 0` such that for every `N`, every zero of every
  non-principal `L(s, χ)` mod `N` satisfies `β ≤ 1 - c / log B(γ)` except at most one zero of
  one character, which lies in the box `β ≥ 1 - c/log B(0)`, `|γ| ≤ c'/log B(0)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Metric Classical
open scoped LSeries.notation

variable {N : ℕ} [NeZero N]

lemma mem_Tset_of_box {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {η : ℝ} (hη : η ≤ 1 / 31)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) (hb : 1 - η ≤ ρ.re) (hg : |ρ.im| ≤ η) :
    ρ - 3 / 2 ∈ Tset hχ 0 := by
  have hβ1 : ρ.re < 1 := by
    by_contra hcc; push Not at hcc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcc hρ
  rw [mem_Tset]
  refine ⟨?_, ?_⟩
  · have e : ρ - 3 / 2 = ((ρ.re - 3 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [e]
    calc ‖((ρ.re - 3 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I‖
        ≤ ‖((ρ.re - 3 / 2 : ℝ) : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
      _ = |ρ.re - 3 / 2| + |ρ.im| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 3 / 4 := by rw [abs_of_neg (by linarith)]; linarith
  · show DirichletCharacter.LFunction χ (ρ - 3 / 2 + ((3 : ℂ) / 2 + I * ((0 : ℝ) : ℂ))) = 0
    simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_add_cancel]; exact hρ

/-- A zero in the box pushes `-Re L'/L(1 + 2η)` down by `4/(15η)`. -/
theorem box_zero_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 31) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) (hb : 1 - η ≤ ρ.re)
    (hg : |ρ.im| ≤ η) :
    -(deriv (DirichletCharacter.LFunction χ) (1 + 2 * η) /
        DirichletCharacter.LFunction χ (1 + 2 * η)).re ≤
      K0 * Real.log (Bt N 0) - 4 / (15 * η) := by
  set d : ℝ := 2 * η with hd
  have hd0 : d ∈ Ioo 0 1 := ⟨by positivity, by linarith⟩
  have b1 := shift_with_sum hχ 0 hd0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at b1
  set w : ℂ → ℂ := fun ρ ↦ (analyticOrderNatAt (fShift χ 0) ρ : ℂ) / ((d : ℂ) - 1 / 2 - ρ)
  have hterm : ∀ ρ ∈ Tset hχ 0, 0 ≤ (w ρ).re := by
    intro ρ hρ
    refine re_natCast_div_nonneg _ ?_
    have := re_lt_of_mem_Tset hρ
    simp; linarith [hd0.1]
  have hmem := mem_Tset_of_box hχ hη hρ hb hg
  have hord : 1 ≤ analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) := by
    refine one_le_order hχ 0 ?_
    show DirichletCharacter.LFunction χ (ρ - 3 / 2 + ((3 : ℂ) / 2 + I * ((0 : ℝ) : ℂ))) = 0
    simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_add_cancel]; exact hρ
  have hβ1 := re_lt_of_mem_Tset hmem
  have hone : 4 / (15 * η) ≤ (w (ρ - 3 / 2)).re := by
    set a : ℝ := d - 1 / 2 - (ρ - 3 / 2).re
    have hre : (ρ - 3 / 2).re = ρ.re - 3 / 2 := by simp
    have him : (ρ - 3 / 2).im = ρ.im := by simp
    have ha1 : 2 * η < a := by simp only [a]; rw [hre] at hβ1 ⊢; linarith
    have ha2 : a ≤ 3 * η := by simp only [a]; rw [hre]; linarith
    have hb2 : ρ.im ^ 2 ≤ a ^ 2 / 4 := by
      have : |ρ.im| ≤ a / 2 := by linarith
      nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]
    have hw : (w (ρ - 3 / 2)).re =
        (analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) : ℝ) * a / (a ^ 2 + ρ.im ^ 2) := by
      simp only [w, Complex.div_re, natCast_re, natCast_im, zero_mul, add_zero,
        Complex.normSq_apply]
      simp only [sub_re, sub_im, ofReal_re, ofReal_im, one_re, one_im, div_ofNat_re,
        div_ofNat_im, zero_sub, zero_div, re_ofNat, im_ofNat, a, hre, him]
      ring
    rw [hw]
    have hapos : 0 < a := by linarith
    have hm1 : (1 : ℝ) ≤ analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) := by exact_mod_cast hord
    have hden : 0 < a ^ 2 + ρ.im ^ 2 := by positivity
    have h1 : 4 / (15 * η) ≤ a / (a ^ 2 + ρ.im ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) hden]; nlinarith
    have h2 : a / (a ^ 2 + ρ.im ^ 2) ≤
        (analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) : ℝ) * a / (a ^ 2 + ρ.im ^ 2) := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left (div_nonneg hapos.le hden.le) hm1
    linarith
  have hsum : 4 / (15 * η) ≤ (∑ ρ ∈ Tset hχ 0, w ρ).re := by
    rw [Complex.re_sum]
    exact hone.trans (Finset.single_le_sum (f := fun ρ ↦ (w ρ).re) hterm hmem)
  have hc : (1 : ℂ) + 2 * (η : ℂ) = 1 + (d : ℂ) := by rw [hd]; push_cast; ring
  rw [hc]
  change _ ≤ K0 * Real.log (Bt N 0) - (∑ ρ ∈ Tset hχ 0, w ρ).re at b1
  linarith

lemma im_eq_zero_of_sq {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    (χ n).im = 0 := by
  have h : (χ n) ^ 2 = (1 : DirichletCharacter ℂ N) n := by
    rw [← hχ2]; simp [pow_two]
  set z := χ n
  have hz : z ^ 2 = 0 ∨ z ^ 2 = 1 := by
    rw [h]
    by_cases hu : IsUnit (n : ZMod N)
    · right; exact MulChar.one_apply hu
    · left; exact MulChar.map_nonunit _ hu
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, mul_re]; ring
  have him : (z ^ 2).im = 2 * z.re * z.im := by rw [pow_two, mul_im]; ring
  rcases hz with h0 | h1
  · rw [h0] at hre him
    simp at hre him
    rcases him with h | h
    · rw [h] at hre; nlinarith [sq_nonneg z.im]
    · exact h
  · rw [h1] at hre him
    simp at hre him
    rcases him with h | h
    · rw [h] at hre; nlinarith [sq_nonneg z.im]
    · exact h

omit [NeZero N] in
/-- The four-term positivity for two real characters. -/
lemma four_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1)
    {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (LSeries ↗ArithmeticFunction.vonMangoldt σ).re +
      (LSeries (↗χ₁ * ↗ArithmeticFunction.vonMangoldt) σ).re +
      (LSeries (↗χ₂ * ↗ArithmeticFunction.vonMangoldt) σ).re +
      (LSeries (↗(χ₁ * χ₂) * ↗ArithmeticFunction.vonMangoldt) σ).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have s0 := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have s1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₁ hs
  have s2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₂ hs
  have s3 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ₁ * χ₂) hs
  simp only [LSeries]
  rw [Complex.re_tsum s0, Complex.re_tsum s1, Complex.re_tsum s2, Complex.re_tsum s3]
  have r0 := Complex.reCLM.summable s0
  have r1 := Complex.reCLM.summable s1
  have r2 := Complex.reCLM.summable s2
  have r3 := Complex.reCLM.summable s3
  simp only [Complex.reCLM_apply] at r0 r1 r2 r3
  rw [← r0.tsum_add r1, ← (r0.add r1).tsum_add r2, ← ((r0.add r1).add r2).tsum_add r3]
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
  rw [e1]
  set a : ℝ := (n : ℝ) ^ σ
  have ha : 0 < a := Real.rpow_pos_of_pos hn0 σ
  set Lv : ℝ := ArithmeticFunction.vonMangoldt n
  have hL : 0 ≤ Lv := ArithmeticFunction.vonMangoldt_nonneg
  have r : ∀ z : ℂ, (z * (Lv : ℂ) / (a : ℂ)).re = Lv / a * z.re := by
    intro z
    have : z * (Lv : ℂ) / (a : ℂ) = ((Lv / a : ℝ) : ℂ) * z := by push_cast; field_simp
    rw [this, Complex.re_ofReal_mul]
  have r0' : ((Lv : ℂ) / (a : ℂ)).re = Lv / a := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  rw [r0', r, r, r]
  have hmul : ((χ₁ * χ₂) n).re = (χ₁ n).re * (χ₂ n).re := by
    rw [MulChar.mul_apply, mul_re, im_eq_zero_of_sq h1, im_eq_zero_of_sq h2]; ring
  rw [hmul]
  have hb1 : -1 ≤ (χ₁ n).re := by
    have := (Complex.abs_re_le_norm (χ₁ n)).trans (χ₁.norm_le_one n)
    linarith [(abs_le.mp this).1]
  have hb2 : -1 ≤ (χ₂ n).re := by
    have := (Complex.abs_re_le_norm (χ₂ n)).trans (χ₂.norm_le_one n)
    linarith [(abs_le.mp this).1]
  have hLa : 0 ≤ Lv / a := div_nonneg hL ha.le
  have : 0 ≤ (1 + (χ₁ n).re) * (1 + (χ₂ n).re) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma log_Bt_le_two_log_Bt_zero {t : ℝ} (ht : |t| ≤ 1) :
    Real.log (Bt N t) ≤ 2 * Real.log (Bt N 0) := by
  have h0 := one_le_log_Bt (N := N) 0
  have hB : Bt N t ≤ 2 * Bt N 0 := by
    unfold Bt
    have hZ := Z_pos
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp only [abs_zero, zero_add]
    have : 2 * (N : ℝ) * (|t| + 3) ≤ 2 * (2 * N * 3) := by nlinarith
    nlinarith
  have h2 : Real.log 2 ≤ Real.log (Bt N 0) := by
    have := one_lt_Bt (N := N) 0
    have h6 : (2 : ℝ) ≤ Bt N 0 := by
      unfold Bt
      have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      have hZ := one_le_Z
      simp only [abs_zero, zero_add]; nlinarith
    exact Real.log_le_log (by norm_num) h6
  calc Real.log (Bt N t) ≤ Real.log (2 * Bt N 0) :=
        Real.log_le_log (by linarith [one_lt_Bt (N := N) t]) hB
    _ = Real.log 2 + Real.log (Bt N 0) := Real.log_mul (by norm_num)
          (by linarith [one_lt_Bt (N := N) 0])
    _ ≤ 2 * Real.log (Bt N 0) := by linarith

lemma neg_logDeriv_re_eq_LSeries {χ : DirichletCharacter ℂ N} {σ : ℝ} (hσ : 1 < σ) :
    -(deriv (DirichletCharacter.LFunction χ) (σ : ℂ) /
      DirichletCharacter.LFunction χ (σ : ℂ)).re =
      (LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) σ).re := by
  rw [← neg_logDeriv_eq_LSeries χ (by simpa using hσ), neg_div_re_eq]

/-- At most one non-principal character mod `N` has a zero in the box. -/
theorem one_exceptional : ∃ c₅ : ℝ, 0 < c₅ ∧ c₅ ≤ 1 / 31 ∧ ∀ (N : ℕ) [NeZero N]
    (χ₁ χ₂ : DirichletCharacter ℂ N), χ₁ ≠ 1 → χ₂ ≠ 1 → ∀ ρ₁ ρ₂ : ℂ,
      DirichletCharacter.LFunction χ₁ ρ₁ = 0 → DirichletCharacter.LFunction χ₂ ρ₂ = 0 →
      1 - c₅ / Real.log (Bt N 0) ≤ ρ₁.re → |ρ₁.im| ≤ c₅ / Real.log (Bt N 0) →
      1 - c₅ / Real.log (Bt N 0) ≤ ρ₂.re → |ρ₂.im| ≤ c₅ / Real.log (Bt N 0) → χ₁ = χ₂ := by
  obtain ⟨C, hC, hz⟩ := ShiftZeroBound
  obtain ⟨c1, hc1, hcx⟩ := zero_free_complex
  have hK := K0_pos
  set c₅ : ℝ := min (1 / (31 * (3 * K0 + C + 1))) (c1 / 3) with hc5
  have hc5pos : 0 < c₅ := lt_min (by positivity) (by positivity)
  have hc531 : c₅ ≤ 1 / 31 := by
    refine (min_le_left _ _).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨c₅, hc5pos, hc531, fun N _ χ₁ χ₂ h1 h2 ρ₁ ρ₂ hz1 hz2 hb1 hg1 hb2 hg2 ↦ ?_⟩
  set Lg := Real.log (Bt N 0) with hLg
  have hL1 : 1 ≤ Lg := one_le_log_Bt 0
  set η := c₅ / Lg with hη
  have hη0 : 0 < η := by positivity
  have hη31 : η ≤ 1 / 31 := by
    rw [hη, div_le_iff₀ (by linarith)]; nlinarith
  have hη1 : η ≤ 1 := by linarith
  -- a complex character has no zero in the box
  have noComplex : ∀ χ : DirichletCharacter ℂ N, ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      1 - η ≤ ρ.re → |ρ.im| ≤ η → χ ^ 2 = 1 := by
    intro χ ρ hρ hb hg
    by_contra hsq
    have h := hcx N χ hsq ρ hρ
    have hle := log_Bt_le_two_log_Bt_zero (N := N) (hg.trans hη1)
    have hpos : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
    have : c1 / (2 * Lg) ≤ c1 / Real.log (Bt N ρ.im) :=
      div_le_div_of_nonneg_left hc1.le hpos hle
    have h3 : c₅ ≤ c1 / 3 := min_le_right _ _
    have : η < c1 / (2 * Lg) := by
      rw [hη, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hr1 := noComplex χ₁ ρ₁ hz1 hb1 hg1
  have hr2 := noComplex χ₂ ρ₂ hz2 hb2 hg2
  by_contra hne
  have h12 : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply hne
    have : χ₂ = χ₂⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_two, hr2]
    rw [this, eq_inv_iff_mul_eq_one, h]
  set d := 2 * η with hd
  have hd0 : d ∈ Ioo 0 1 := ⟨by positivity, by linarith⟩
  have b0 := hz d hd0
  have B1 := box_zero_bound h1 hη0 hη31 hz1 hb1 hg1
  have B2 := box_zero_bound h2 hη0 hη31 hz2 hb2 hg2
  have B3 := shiftAny_bound h12 0 hd0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at B3
  have hpos := four_nonneg hr1 hr2 (show 1 < 1 + d by linarith [hd0.1])
  have hs : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith [hd0.1]
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    ← neg_logDeriv_re_eq_LSeries (show 1 < 1 + d by linarith [hd0.1]),
    ← neg_logDeriv_re_eq_LSeries (show 1 < 1 + d by linarith [hd0.1]),
    ← neg_logDeriv_re_eq_LSeries (show 1 < 1 + d by linarith [hd0.1])] at hpos
  have hcast : ((1 + d : ℝ) : ℂ) = 1 + d := by push_cast; ring
  rw [hcast, neg_div_re_eq] at hpos
  have hcast2 : (1 : ℂ) + 2 * (η : ℂ) = 1 + (d : ℂ) := by rw [hd]; push_cast; ring
  rw [hcast2] at B1 B2
  rw [← hLg] at B1 B2 B3
  -- `8/(15η) ≤ 1/d + C + 3 K₀ Lg`, impossible for small `c₅`
  have h8 : 8 / (15 * η) = 2 * (4 / (15 * η)) := by ring
  have hmain : 8 / (15 * η) ≤ 1 / d + C + 3 * K0 * Lg := by rw [h8]; linarith
  have e1 : 8 / (15 * η) - 1 / d = Lg / (30 * c₅) := by
    rw [hd, hη]; field_simp; ring
  have h5 : c₅ ≤ 1 / (31 * (3 * K0 + C + 1)) := min_le_left _ _
  have e2 : 31 * (3 * K0 + C + 1) * Lg / 30 ≤ Lg / (30 * c₅) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h5
    nlinarith
  nlinarith

/-- The zero-free region for all non-principal characters mod `N` together: every zero is in
the region except possibly one zero of one character, in the box at `1`. -/
theorem zero_free_region_all : ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) ∨
        (1 - c / Real.log (Bt N 0) ≤ ρ.re ∧ |ρ.im| ≤ c' / Real.log (Bt N 0))) ∧
      (∀ (χ₂ : DirichletCharacter ℂ N), χ₂ ≠ 1 → ∀ ρ₁ ρ₂ : ℂ,
        DirichletCharacter.LFunction χ ρ₁ = 0 → DirichletCharacter.LFunction χ₂ ρ₂ = 0 →
        1 - c / Real.log (Bt N 0) ≤ ρ₁.re → |ρ₁.im| ≤ c' / Real.log (Bt N 0) →
        1 - c / Real.log (Bt N 0) ≤ ρ₂.re → |ρ₂.im| ≤ c' / Real.log (Bt N 0) →
          χ = χ₂ ∧ ρ₁ = ρ₂) := by
  obtain ⟨cp, hcp, hpage⟩ := page_two_zeros
  obtain ⟨c₅, hc₅, -, hexc⟩ := one_exceptional
  set c0 := min cp c₅ with hc0def
  have hc0 : 0 < c0 := lt_min hcp hc₅
  obtain ⟨c1, hc1, hcx⟩ := zero_free_complex
  obtain ⟨c2, hc2, hre⟩ := zero_free_real
  obtain ⟨M₀, hM₀, hsmall⟩ := zero_free_real_small
  set M : ℝ := M₀ + 1 / c0 with hMdef
  have hMM : M₀ ≤ M := by rw [hMdef]; linarith [one_div_pos.mpr hc0]
  have hMpos : 0 < M := by linarith
  set c3 : ℝ := 11 / (276 * M)
  have hc3 : 0 < c3 := by positivity
  set c := min (min c1 c2) (min c3 c0) with hc
  set c' : ℝ := 1 / (4 * M) with hc'
  have hcpos : 0 < c := lt_min (lt_min hc1 hc2) (lt_min hc3 hc0)
  have hc'pos : 0 < c' := by positivity
  have hcc0 : c ≤ c0 := (min_le_right _ _).trans (min_le_right _ _)
  have hc'c0 : c' ≤ c0 := by
    rw [hc', div_le_iff₀ (by positivity)]
    have : 1 ≤ c0 * M := by
      rw [hMdef, mul_add, mul_one_div_cancel hc0.ne']; nlinarith
    linarith
  refine ⟨c, c', hcpos, hc'pos, fun N _ χ hχ ↦ ⟨fun ρ hρ ↦ ?_, ?_⟩⟩
  · have hL := one_le_log_Bt (N := N) ρ.im
    have hLp : 0 < Real.log (Bt N ρ.im) := by linarith
    have mono : ∀ c₁ : ℝ, c ≤ c₁ → ρ.re ≤ 1 - c₁ / Real.log (Bt N ρ.im) →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) := by
      intro c₁ h h'
      have := div_le_div_of_nonneg_right h hLp.le
      linarith
    by_cases hsq : χ ^ 2 = 1
    · by_cases hbig : 2 ≤ |ρ.im|
      · exact Or.inl (mono c2 ((min_le_left _ _).trans (min_le_right _ _))
          (hre N χ hχ hsq ρ hρ hbig))
      · push Not at hbig
        by_cases hfar : 1 / (4 * (M * Real.log (Bt N ρ.im))) ≤ |ρ.im|
        · exact Or.inl (mono c3 ((min_le_right _ _).trans (min_le_left _ _))
            (hsmall M hMM N χ hχ hsq ρ hρ hbig.le hfar))
        · push Not at hfar
          have hL0 := one_le_log_Bt (N := N) 0
          have hmono : Real.log (Bt N 0) ≤ Real.log (Bt N ρ.im) :=
            log_Bt_mono (by simp)
          have hγ : |ρ.im| ≤ c' / Real.log (Bt N 0) := by
            rw [hc']
            have : 1 / (4 * (M * Real.log (Bt N ρ.im))) ≤ 1 / (4 * M) / Real.log (Bt N 0) := by
              rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
              nlinarith
            linarith
          by_cases hβ : 1 - c / Real.log (Bt N 0) ≤ ρ.re
          · exact Or.inr ⟨hβ, hγ⟩
          · push Not at hβ
            left
            have : c / Real.log (Bt N ρ.im) ≤ c / Real.log (Bt N 0) :=
              div_le_div_of_nonneg_left hcpos.le (by linarith) hmono
            linarith
    · exact Or.inl (mono c1 ((min_le_left _ _).trans (min_le_left _ _))
        (hcx N χ hsq ρ hρ))
  · intro χ₂ hχ₂ ρ₁ ρ₂ h1 h2 hb1 hg1 hb2 hg2
    have hL0 := one_le_log_Bt (N := N) 0
    have hLp : 0 < Real.log (Bt N 0) := by linarith
    have hh : c / Real.log (Bt N 0) ≤ c0 / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right hcc0 hLp.le
    have hw : c' / Real.log (Bt N 0) ≤ c0 / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right hc'c0 hLp.le
    have hp : c0 / Real.log (Bt N 0) ≤ cp / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLp.le
    have h5 : c0 / Real.log (Bt N 0) ≤ c₅ / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right (min_le_right _ _) hLp.le
    have heq : χ = χ₂ := hexc N χ χ₂ hχ hχ₂ ρ₁ ρ₂ h1 h2 (by linarith) (by linarith)
      (by linarith) (by linarith)
    subst heq
    exact ⟨rfl, hpage N χ hχ ρ₁ ρ₂ h1 h2 (by linarith) (by linarith) (by linarith)
      (by linarith)⟩

end LeanLab.PNTPort.DirichletZF

