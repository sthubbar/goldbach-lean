module

public import LeanLab.PNTPort.DirichletZF.ZeroFree

/-!
# At most one zero of `L(s, χ)` close to `s = 1`, uniformly in the modulus

Lab proof, unit U-5110. AI wrote this file. Known mathematics, the Landau-Page step behind
the exceptional zero, no cited input; `ShiftZeroBound` comes from the ported StrongPNT file,
Apache-2.0, the PrimeNumberTheoremAnd contributors.

With `L_N = log B(0) = log(6NZ)`, there is an absolute `c > 0` such that for every
non-principal `χ` mod `N` the zeros `β + iγ` of `L(s, χ)` with `β ≥ 1 - c/L_N` and
`|γ| ≤ c/L_N` number at most one, counted with multiplicity: `page_count`, and
`page_two_zeros`, two distinct zeros cannot both lie in the box. The proof is the positivity of
`-ζ'/ζ(σ) - Re L'/L(σ, χ) = ∑ Λ(n)(1 + Re χ(n)) n^{-σ}` against the Borel-Caratheodory sum
over zeros.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Metric Classical
open scoped LSeries.notation

variable {N : ℕ} [NeZero N]

/-- The zeros of `fShift χ t` within `3/4`, as a finset. -/
noncomputable def Tset {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) : Finset ℂ :=
  (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) (fShift_finite_zeros hχ t)).toFinset

lemma mem_Tset {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {t : ℝ} {ρ : ℂ} :
    ρ ∈ Tset hχ t ↔ ‖ρ‖ ≤ 3 / 4 ∧ fShift χ t ρ = 0 := by
  simp [Tset, SetOfZeros]

lemma re_lt_of_mem_Tset {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ Tset hχ t) : ρ.re + 3 / 2 < 1 := by
  have h := (mem_Tset.mp hρ).2
  by_contra hc; push Not at hc
  refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) ?_ h
  rw [add_re, re_c]; exact hc

/-- `-Re L'/L(1 + d + it, χ) ≤ K₀ log B(t) - Re ∑_ρ m_ρ/(d - 1/2 - ρ)`. -/
lemma shift_with_sum {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {d : ℝ}
    (hd0 : d ∈ Ioo 0 1) :
    -(deriv (DirichletCharacter.LFunction χ) (1 + d + I * t) /
        DirichletCharacter.LFunction χ (1 + d + I * t)).re ≤ K0 * Real.log (Bt N t) -
      (∑ ρ ∈ Tset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((d : ℂ) - 1 / 2 - ρ)).re := by
  obtain ⟨hz, he⟩ := shift_setup hχ t hd0
  have key := logDeriv_sub_sum_le hχ t hz
  set z : ℂ := (d : ℂ) - 1 / 2
  have hd : deriv (fShift χ t) z = deriv (DirichletCharacter.LFunction χ) (1 + d + I * t) := by
    show deriv (fun w ↦ DirichletCharacter.LFunction χ (w + ((3 : ℂ) / 2 + I * t))) z = _
    rw [deriv_comp_add_const, he]
  have hv : fShift χ t z = DirichletCharacter.LFunction χ (1 + d + I * t) := by
    show DirichletCharacter.LFunction χ (z + ((3 : ℂ) / 2 + I * t)) = _
    rw [he]
  rw [hd, hv] at key
  have := (Complex.re_le_norm _).trans ((norm_neg (_ : ℂ)).le.trans key)
  rw [neg_sub, sub_re] at this
  unfold Tset
  linarith

omit [NeZero N] in
/-- `-ζ'/ζ(σ) - Re L'/L(σ, χ) ≥ 0` for real `σ > 1`, any `χ`. -/
lemma zeta_plus_L_nonneg (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (LSeries ↗ArithmeticFunction.vonMangoldt σ).re +
      (LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) σ).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have s1 := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have s2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  simp only [LSeries]
  rw [Complex.re_tsum s1, Complex.re_tsum s2]
  have r1 := Complex.reCLM.summable s1
  have r2 := Complex.reCLM.summable s2
  simp only [Complex.reCLM_apply] at r1 r2
  rw [← r1.tsum_add r2]
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
  have r1 : ((Lv : ℂ) / (a : ℂ)).re = Lv / a := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  have r2 : (χ n * (Lv : ℂ) / (a : ℂ)).re = Lv / a * (χ n).re := by
    have : χ n * (Lv : ℂ) / (a : ℂ) = ((Lv / a : ℝ) : ℂ) * χ n := by
      push_cast; field_simp
    rw [this, Complex.re_ofReal_mul]
  rw [r1, r2]
  have hre : -1 ≤ (χ n).re := by
    have h1 := Complex.abs_re_le_norm (χ n)
    have h2 := χ.norm_le_one n
    linarith [(abs_le.mp (h1.trans h2)).1]
  have : 0 ≤ Lv / a := div_nonneg hL ha.le
  nlinarith

/-- Two zeros, counted with multiplicity, cannot both lie in the box near `1`. -/
theorem page_count : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 31 ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1),
      ∑ ρ ∈ (Tset hχ 0).filter (fun ρ ↦ 1 - c / Real.log (Bt N 0) ≤ ρ.re + 3 / 2 ∧
          |ρ.im| ≤ c / Real.log (Bt N 0)),
        analyticOrderNatAt (fShift χ 0) ρ ≤ 1 := by
  obtain ⟨C, hC, hz⟩ := ShiftZeroBound
  have hK := K0_pos
  set c : ℝ := 1 / (31 * (K0 + C + 1)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨c, hcpos, ?_, fun N _ χ hχ ↦ ?_⟩
  · rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set Lg := Real.log (Bt N 0) with hLdef
  have hL1 : 1 ≤ Lg := one_le_log_Bt 0
  set η : ℝ := c / Lg with hη
  have hηpos : 0 < η := by positivity
  have hη31 : η ≤ 1 / 31 := by
    rw [hη, div_le_iff₀ (by linarith)]
    have : c ≤ 1 / 31 := by rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  set d : ℝ := 2 * η with hd
  have hd0 : d ∈ Ioo 0 1 := ⟨by positivity, by linarith⟩
  set F := (Tset hχ 0).filter (fun ρ ↦ 1 - c / Real.log (Bt N 0) ≤ ρ.re + 3 / 2 ∧
    |ρ.im| ≤ c / Real.log (Bt N 0))
  by_contra hcon
  push Not at hcon
  have hm : (2 : ℝ) ≤ ∑ ρ ∈ F, (analyticOrderNatAt (fShift χ 0) ρ : ℝ) := by
    have : 2 ≤ ∑ ρ ∈ F, analyticOrderNatAt (fShift χ 0) ρ := hcon
    exact_mod_cast this
  set w : ℂ → ℂ := fun ρ ↦ (analyticOrderNatAt (fShift χ 0) ρ : ℂ) / ((d : ℂ) - 1 / 2 - ρ)
  have hterm : ∀ ρ ∈ Tset hχ 0, 0 ≤ (w ρ).re := by
    intro ρ hρ
    refine re_natCast_div_nonneg _ ?_
    have := re_lt_of_mem_Tset hρ
    simp; linarith [hd0.1]
  have hbig : ∀ ρ ∈ F, (analyticOrderNatAt (fShift χ 0) ρ : ℝ) * (4 / (15 * η)) ≤ (w ρ).re := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hT, hβ, hγ⟩ := hρ
    have hβ1 := re_lt_of_mem_Tset hT
    set a : ℝ := d - 1 / 2 - ρ.re
    have ha1 : 2 * η < a := by simp only [a]; linarith
    have ha2 : a ≤ 3 * η := by simp only [a]; rw [← hLdef, ← hη] at hβ; linarith
    have hγ' : |ρ.im| ≤ η := by rw [← hLdef, ← hη] at hγ; exact hγ
    have hb2 : ρ.im ^ 2 ≤ a ^ 2 / 4 := by
      have : |ρ.im| ≤ a / 2 := by linarith
      have h0 := abs_nonneg ρ.im
      nlinarith [sq_abs ρ.im]
    have hw : (w ρ).re = (analyticOrderNatAt (fShift χ 0) ρ : ℝ) * a / (a ^ 2 + ρ.im ^ 2) := by
      simp only [w, Complex.div_re, natCast_re, natCast_im, zero_mul, add_zero, Complex.normSq_apply]
      simp [a]
      ring
    rw [hw]
    have hapos : 0 < a := by linarith
    have hden : 0 < a ^ 2 + ρ.im ^ 2 := by positivity
    have hm0 : (0 : ℝ) ≤ analyticOrderNatAt (fShift χ 0) ρ := Nat.cast_nonneg _
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hm0
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith
  have hSF : (∑ ρ ∈ F, (analyticOrderNatAt (fShift χ 0) ρ : ℝ)) * (4 / (15 * η)) ≤
      (∑ ρ ∈ Tset hχ 0, w ρ).re := by
    rw [Complex.re_sum, Finset.sum_mul]
    calc ∑ ρ ∈ F, (analyticOrderNatAt (fShift χ 0) ρ : ℝ) * (4 / (15 * η))
        ≤ ∑ ρ ∈ F, (w ρ).re := Finset.sum_le_sum hbig
      _ ≤ ∑ ρ ∈ Tset hχ 0, (w ρ).re :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ρ hρ _ ↦ hterm ρ hρ)
  have hS8 : 8 / (15 * η) ≤ (∑ ρ ∈ Tset hχ 0, w ρ).re := by
    have : 8 / (15 * η) = 2 * (4 / (15 * η)) := by ring
    rw [this]
    have h4 : 0 ≤ 4 / (15 * η) := by positivity
    nlinarith
  -- the three inequalities at `σ = 1 + d`
  have b1 := shift_with_sum hχ 0 hd0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at b1
  have b0 := hz d hd0
  have hpos := zeta_plus_L_nonneg χ (show 1 < 1 + d by linarith [hd0.1])
  have hs : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith [hd0.1]
  rw [← neg_logDeriv_eq_LSeries χ hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hpos
  have hcast : ((1 + d : ℝ) : ℂ) = 1 + d := by push_cast; ring
  rw [hcast, neg_div_re_eq, neg_div_re_eq] at hpos
  -- `8/(15η) ≤ K₀ Lg + 1/(2η) + C`
  have hmain : 8 / (15 * η) ≤ K0 * Lg + 1 / d + C := by
    change _ ≤ K0 * Real.log (Bt N 0) - (∑ ρ ∈ Tset hχ 0, w ρ).re at b1
    linarith
  have e1 : 8 / (15 * η) - 1 / d = Lg / (30 * c) := by
    rw [hd, hη]; field_simp; ring
  have e2 : Lg / (30 * c) = 31 * (K0 + C + 1) * Lg / 30 := by
    rw [hc]; field_simp
  have : 31 * (K0 + C + 1) * Lg / 30 ≤ K0 * Lg + C := by linarith
  nlinarith

/-- Two distinct zeros cannot both lie in the box. -/
theorem page_two_zeros : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ ρ₁ ρ₂ : ℂ,
      DirichletCharacter.LFunction χ ρ₁ = 0 → DirichletCharacter.LFunction χ ρ₂ = 0 →
      1 - c / Real.log (Bt N 0) ≤ ρ₁.re → |ρ₁.im| ≤ c / Real.log (Bt N 0) →
      1 - c / Real.log (Bt N 0) ≤ ρ₂.re → |ρ₂.im| ≤ c / Real.log (Bt N 0) → ρ₁ = ρ₂ := by
  obtain ⟨c, hc, hc31, h⟩ := page_count
  refine ⟨c, hc, fun N _ χ hχ ρ₁ ρ₂ h1 h2 hb1 hg1 hb2 hg2 ↦ ?_⟩
  by_contra hne
  have hL1 : 1 ≤ Real.log (Bt N 0) := one_le_log_Bt 0
  have hη : c / Real.log (Bt N 0) ≤ 1 / 31 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hT : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 1 - c / Real.log (Bt N 0) ≤ ρ.re →
      |ρ.im| ≤ c / Real.log (Bt N 0) →
      ρ - 3 / 2 ∈ (Tset hχ 0).filter (fun ρ ↦ 1 - c / Real.log (Bt N 0) ≤ ρ.re + 3 / 2 ∧
          |ρ.im| ≤ c / Real.log (Bt N 0)) := by
    intro ρ hρ hb hg
    have hβ1 : ρ.re < 1 := by
      by_contra hcc; push Not at hcc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcc hρ
    rw [Finset.mem_filter, mem_Tset]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have e : ρ - 3 / 2 = ((ρ.re - 3 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [e]
      calc ‖((ρ.re - 3 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I‖
          ≤ ‖((ρ.re - 3 / 2 : ℝ) : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
        _ = |ρ.re - 3 / 2| + |ρ.im| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 3 / 4 := by
            rw [abs_of_neg (by linarith)]; linarith
    · show DirichletCharacter.LFunction χ (ρ - 3 / 2 + ((3 : ℂ) / 2 + I * ((0 : ℝ) : ℂ))) = 0
      simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_add_cancel]; exact hρ
    · simp only [sub_re]; norm_num; linarith
    · simpa using hg
  have hm1 := hT ρ₁ h1 hb1 hg1
  have hm2 := hT ρ₂ h2 hb2 hg2
  have hord : ∀ ρ, DirichletCharacter.LFunction χ ρ = 0 →
      1 ≤ analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) := by
    intro ρ hρ
    refine one_le_order hχ 0 ?_
    show DirichletCharacter.LFunction χ (ρ - 3 / 2 + ((3 : ℂ) / 2 + I * ((0 : ℝ) : ℂ))) = 0
    simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_add_cancel]; exact hρ
  have hsub : ({ρ₁ - 3 / 2, ρ₂ - 3 / 2} : Finset ℂ) ⊆ (Tset hχ 0).filter
      (fun ρ ↦ 1 - c / Real.log (Bt N 0) ≤ ρ.re + 3 / 2 ∧ |ρ.im| ≤ c / Real.log (Bt N 0)) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hm1
    · rw [Finset.mem_singleton.mp hx]; exact hm2
  have hne' : ρ₁ - 3 / 2 ≠ ρ₂ - 3 / 2 := fun h ↦ hne (sub_left_injective h)
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun ρ ↦ analyticOrderNatAt (fShift χ 0) ρ) (fun _ _ _ ↦ Nat.zero_le _)
  rw [Finset.sum_pair hne'] at this
  have := h N χ hχ
  have := hord ρ₁ h1
  have := hord ρ₂ h2
  omega

end LeanLab.PNTPort.DirichletZF

