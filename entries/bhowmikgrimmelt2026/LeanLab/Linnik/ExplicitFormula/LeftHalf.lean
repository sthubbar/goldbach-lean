module

public import LeanLab.Linnik.ExplicitFormula.Defs
public import LeanLab.PNTPort.ZetaZeros.Digamma2

/-!
# The left half plane for primitive `L(s, χ)`, Davenport ch. 9, 12 and 16

AI wrote the Lean code. Binary Goldbach is OPEN.
From Mathlib's functional equation `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`:
in `-1/2 ≤ Re s ≤ 0` the only possible zero is the trivial zero `s = 0` of an even character, it is
simple, there is no zero on `Re s = -1/2`, and on that line `|L'/L| ≪ log(q(|t| + 2))` uniformly.
Lab inputs: `LeanLab.HardyLittlewood1923.U1482` `fe_strip`, `G`; `LeanLab.PNTPort.ZetaZeros.Digamma`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex

/-- elementary: the gamma factor of a Dirichlet character is nonzero on `Re s > 0`. -/
lemma gf_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]; apply Gammaℝ_ne_zero_of_re_pos; simp; linarith

/-- Davenport ch. 9: `Λ(s, χ) = L(s, χ) γ(s, χ)` where the gamma factor is finite and nonzero. -/
lemma completed_eq_L_mul_gf {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : s ≠ 0 ∨ q ≠ 1) (hΓ : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DirichletCharacter.completedLFunction χ s =
      χ.LFunction s * DirichletCharacter.gammaFactor χ s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s h, div_mul_cancel₀ _ hΓ]

/-- elementary: a primitive character mod `q ≠ 1` is nontrivial. -/
lemma ne_one_of_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) : χ ≠ 1 := by
  intro h; apply hq
  rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hχ
  exact hχ.symm

/-- Davenport ch. 9: the root number of a primitive character is nonzero, from the functional
equation and `Λ(2, χ) ≠ 0`. -/
lemma rootNumber_ne_zero' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    DirichletCharacter.rootNumber χ ≠ 0 := by
  rcases eq_or_ne q 1 with rfl | hN
  · rw [DirichletCharacter.rootNumber_modOne]; exact one_ne_zero
  have hne := ne_one_of_primitive hχ hN
  intro hRoot
  have h := hχ.completedLFunction_one_sub (-1 : ℂ)
  rw [hRoot, mul_zero, zero_mul] at h
  have h2 : DirichletCharacter.completedLFunction χ (2 : ℂ) = 0 := by
    convert h using 2; ring
  have hΓ := gf_ne_zero_of_re_pos χ (s := 2) (by norm_num)
  rw [completed_eq_L_mul_gf χ (Or.inr hN) hΓ] at h2
  exact mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
    (by norm_num)) hΓ h2

/-- Davenport ch. 9: for primitive `χ`, `Λ(s, χ) ≠ 0` on `Re s ≤ 0`, by the functional equation
and the nonvanishing of `L(s, χ̄)` on `Re s ≥ 1`; the point `s = 0` needs `χ ≠ 1`. -/
lemma completed_ne_zero_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) (h : s ≠ 0 ∨ χ ≠ 1) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hfe := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  rw [hfe]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have h1 : 0 < (1 - s).re := by simp; linarith
  have h1' : 1 - s ≠ 0 := by intro e; rw [e] at h1; simp at h1
  have hΓ := gf_ne_zero_of_re_pos χ⁻¹ h1
  refine mul_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hq0)) (rootNumber_ne_zero' hχ)) ?_
  rw [completed_eq_L_mul_gf χ⁻¹ (Or.inl h1') hΓ]
  refine mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ ?_ (by simp; linarith))
    hΓ
  rcases h with h | h
  · right; intro e; apply h; linear_combination -e
  · left; exact inv_ne_one.mpr h

/-- Davenport ch. 9: the gamma factor is nonzero in `-1/2 ≤ Re s ≤ 0` away from `s = 0`. -/
lemma gf_ne_zero_left {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (hs : s ≠ 0) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · apply hs; simpa using hn
    · have := congrArg Complex.re hn
      simp at this
      have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      linarith
  · rw [hχ.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Davenport ch. 9 and 12: for primitive `χ`, a zero with `-1/2 ≤ Re ρ ≤ 0` is `ρ = 0`. -/
theorem zero_left_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : χ.LFunction ρ = 0) (h1 : -1 / 2 ≤ ρ.re) (h2 : ρ.re ≤ 0) : ρ = 0 := by
  by_contra hne
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hne)] at hρ
  exact div_ne_zero (completed_ne_zero_of_re_nonpos hχ h2 (Or.inl hne))
    (gf_ne_zero_left χ h1 hne) hρ

/-- Davenport ch. 9: the trivial zero at `0` is at most simple. -/
theorem mult_zero_le_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    mult χ 0 ≤ 1 := by
  rcases eq_or_ne q 1 with rfl | hN
  · have h0 : analyticOrderAt χ.LFunction 0 = 0 := by
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannZeta_zero]; norm_num))
    simp only [mult, analyticOrderNatAt]; rw [h0]; simp
  have hne := ne_one_of_primitive hχ hN
  have hc0 := completed_ne_zero_of_re_nonpos hχ (s := 0) (by simp) (Or.inr hne)
  have hL : χ.LFunction = fun s => DirichletCharacter.completedLFunction χ s /
      DirichletCharacter.gammaFactor χ s :=
    funext fun s => DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN)
  have hdc := DirichletCharacter.differentiable_completedLFunction hne
  rcases χ.even_or_odd with he | ho
  · -- even: `L(s) = s g(s)` with `g(0) = Λ(0)/2 ≠ 0`
    set g : ℂ → ℂ := fun s => DirichletCharacter.completedLFunction χ s *
      ((Real.pi : ℂ) ^ (-s / 2))⁻¹ * (Gamma (s / 2 + 1))⁻¹ / 2 with hg
    have hga : AnalyticAt ℂ g 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hd : Differentiable ℂ g := by
        intro s
        have h1 : DifferentiableAt ℂ (fun s : ℂ => ((Real.pi : ℂ) ^ (-s / 2))⁻¹) s :=
          (((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi))).inv
            (cpow_ne_zero_iff.mpr (Or.inl hpi))
        have h2 : DifferentiableAt ℂ (fun s : ℂ => (Gamma (s / 2 + 1))⁻¹) s :=
          by
            have ha : DifferentiableAt ℂ (fun s : ℂ => s / 2 + 1) s :=
              (differentiableAt_id.div_const 2).add_const 1
            exact DifferentiableAt.comp (g := fun s : ℂ => (Gamma s)⁻¹) s
              (differentiable_one_div_Gamma (s / 2 + 1)) ha
        exact (((hdc s).mul h1).mul h2).div_const 2
      exact hd.analyticAt 0
    have hord : analyticOrderAt χ.LFunction 0 = (1 : ℕ) := by
      have hLa : AnalyticAt ℂ χ.LFunction 0 :=
        (DirichletCharacter.differentiable_LFunction hne).analyticAt 0
      rw [hLa.analyticOrderAt_eq_natCast]
      refine ⟨g, hga, ?_, Filter.Eventually.of_forall fun s => ?_⟩
      · simp only [hg, neg_zero, zero_div, cpow_zero, inv_one, mul_one, zero_add,
          Gamma_one]
        exact div_ne_zero hc0 two_ne_zero
      · rw [hL]
        simp only [he.gammaFactor_def, Gammaℝ_def, hg, sub_zero, pow_one, smul_eq_mul]
        rcases eq_or_ne s 0 with rfl | hs
        · simp [Gamma_zero]
        · have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
          rw [Gamma_add_one _ hs2]
          field_simp
    simp only [mult, analyticOrderNatAt]; rw [hord]; simp
  · -- odd: `L(0) = Λ(0)/Γℝ(1) ≠ 0`
    have h0 : analyticOrderAt χ.LFunction 0 = 0 := by
      refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
      rw [hL]
      refine div_ne_zero hc0 ?_
      rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp)
    simp only [mult, analyticOrderNatAt]; rw [h0]; simp

/-- No zero on the line `Re s = -1/2`. -/
theorem no_zero_left_line {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (t : ℝ) : χ.LFunction (-1 / 2 + t * I) ≠ 0 := by
  intro h
  have := zero_left_strip hχ h (by simp) (by simp; norm_num)
  have h' := congrArg Complex.re this
  simp at h'

/-- elementary: the gamma factor is differentiable wherever it is nonzero, since its inverse
is entire. -/
lemma gf_diff_of_ne {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with he | ho
  · have e : DirichletCharacter.gammaFactor χ = fun s => ((Gammaℝ s)⁻¹)⁻¹ := by
      funext s; rw [he.gammaFactor_def, inv_inv]
    rw [he.gammaFactor_def] at h
    rw [e]; exact (differentiable_Gammaℝ_inv s).inv (inv_ne_zero h)
  · have e : DirichletCharacter.gammaFactor χ = fun s => ((Gammaℝ (s + 1))⁻¹)⁻¹ := by
      funext s; rw [ho.gammaFactor_def, inv_inv]
    rw [ho.gammaFactor_def] at h
    rw [e]
    have hd : DifferentiableAt ℂ (fun s : ℂ => (Gammaℝ (s + 1))⁻¹) s :=
      DifferentiableAt.comp (g := fun s : ℂ => (Gammaℝ s)⁻¹) s (differentiable_Gammaℝ_inv _)
        (differentiableAt_id.add_const 1)
    exact hd.inv (inv_ne_zero h)

/-- Davenport ch. 9, the functional equation differentiated logarithmically on `Re s = -1/2`:
`L'/L(s, χ) = -log q - γ'/γ(1 - s, χ̄) - γ'/γ(s, χ) - L'/L(1 - s, χ̄)`, with `1 - s = 3/2 - it`. -/
theorem logDeriv_fe_left {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (t : ℝ) :
    deriv χ.LFunction (-1 / 2 + t * I) / χ.LFunction (-1 / 2 + t * I) =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (3 / 2 + (-t : ℝ) * I)
        - logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)
        - logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I) := by
  set s0 : ℂ := -1 / 2 + t * I with hs0
  have h1s : 1 - s0 = 3 / 2 + (-t : ℝ) * I := by rw [hs0]; push_cast; ring
  have hre0 : s0.re = -1 / 2 := by simp [hs0]
  have hs0ne : s0 ≠ 0 := by intro e; rw [e] at hre0; norm_num at hre0
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  set A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ * (q : ℂ) ^ ((1 - s) - 1 / 2) with hA
  set ref : ℂ → ℂ := fun s => 1 - s with href
  set B : ℂ → ℂ := DirichletCharacter.gammaFactor χ⁻¹ ∘ ref with hB
  set Cc : ℂ → ℂ := (χ⁻¹).LFunction ∘ ref with hCc
  have hev : χ.LFunction =ᶠ[nhds s0] A * B * Cc / DirichletCharacter.gammaFactor χ := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show s0.re < 0 by rw [hre0]; norm_num)] with s hs
    have hs : s.re < 0 := hs
    have hsne : s ≠ 0 := by intro e; rw [e] at hs; simp at hs
    have hr1 : 0 < (1 - s).re := by simp; linarith
    have h1ne : 1 - s ≠ 0 := by intro e; rw [e] at hr1; simp at hr1
    have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne), hfe,
      completed_eq_L_mul_gf χ⁻¹ (Or.inl h1ne) (gf_ne_zero_of_re_pos χ⁻¹ hr1)]
    simp only [Pi.mul_apply, Pi.div_apply, hA, hB, hCc, href, Function.comp_apply]
    ring
  have hr1 : 0 < (1 - s0).re := by rw [Complex.sub_re, Complex.one_re, hre0]; norm_num
  have hrefd : DifferentiableAt ℂ ref s0 := (differentiableAt_const _).sub differentiableAt_id
  have hderef : deriv ref s0 = -1 := by
    have hd : HasDerivAt ref (-1) s0 := by
      simpa using (hasDerivAt_id s0).const_sub (1 : ℂ)
    exact hd.deriv
  have hgfi := gf_ne_zero_of_re_pos χ⁻¹ hr1
  have hgfid : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ⁻¹) (ref s0) :=
    gf_diff_of_ne χ⁻¹ hgfi
  have hL1 : (1 - s0) ≠ 1 := by intro e; apply hs0ne; linear_combination -e
  have hLi : (χ⁻¹).LFunction (ref s0) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr hL1)
      (by show 1 ≤ (1 - s0).re; rw [Complex.sub_re, Complex.one_re, hre0]; norm_num)
  have hLid : DifferentiableAt ℂ (χ⁻¹).LFunction (ref s0) :=
    DirichletCharacter.differentiableAt_LFunction χ⁻¹ _ (Or.inl hL1)
  have hgf0 := gf_ne_zero_left χ (s := s0) (by rw [hre0]) hs0ne
  have hgf0d := gf_diff_of_ne χ hgf0
  have hAne : A s0 ≠ 0 := mul_ne_zero (rootNumber_ne_zero' hχ) (cpow_ne_zero_iff.mpr (Or.inl hq0))
  have hAd : HasDerivAt A (DirichletCharacter.rootNumber χ *
      ((q : ℂ) ^ ((1 - s0) - 1 / 2) * Complex.log q * (-1))) s0 := by
    have h1 : HasDerivAt (fun s : ℂ => (1 - s) - 1 / 2) (-1) s0 := by
      simpa using ((hasDerivAt_id s0).const_sub (1 : ℂ)).sub_const (1 / 2 : ℂ)
    exact (h1.const_cpow (Or.inl hq0)).const_mul _
  have hBne : B s0 ≠ 0 := hgfi
  have hCne : Cc s0 ≠ 0 := hLi
  have hBd : DifferentiableAt ℂ B s0 := hgfid.comp s0 hrefd
  have hCd : DifferentiableAt ℂ Cc s0 := hLid.comp s0 hrefd
  have hlogA : logDeriv A s0 = -(Real.log q : ℂ) := by
    rw [logDeriv_apply, hAd.deriv, Complex.natCast_log]
    simp only [hA]
    have hc : (q : ℂ) ^ ((1 - s0) - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hq0)
    rw [div_eq_iff (mul_ne_zero (rootNumber_ne_zero' hχ) hc)]
    ring
  rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_div (f := A * B * Cc) (g := DirichletCharacter.gammaFactor χ) s0 (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
      ((hAd.differentiableAt.mul hBd).mul hCd) hgf0d,
    logDeriv_mul (f := A * B) (g := Cc) s0 (mul_ne_zero hAne hBne) hCne (hAd.differentiableAt.mul hBd) hCd,
    logDeriv_mul (f := A) (g := B) s0 hAne hBne hAd.differentiableAt hBd, hlogA,
    hB, hCc, logDeriv_comp hgfid hrefd, logDeriv_comp hLid hrefd, hderef]
  simp only [href, h1s]
  ring

/-- Davenport ch. 16: `|L'/L(3/2 + it, χ)| ≤ -ζ'/ζ(3/2) = Σ Λ(n) n^(-3/2)`, uniformly in `χ`. -/
theorem logDeriv_L_three_half_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ), ‖logDeriv χ.LFunction (3 / 2 + t * I)‖ ≤ C := by
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsumN : Summable fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.mpr hsum
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun q _ χ t => ?_⟩
  set s : ℂ := 3 / 2 + t * I with hs
  have hre : 1 < s.re := by simp [hs]; norm_num
  have hconv : -deriv χ.LFunction s / χ.LFunction s =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
    convert h.symm using 3
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  have hpt : ∀ n, ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · exact le_rfl
    · have hsr : s.re = (3 / 2 : ℂ).re := by simp [hs]
      rw [hsr]
      gcongr
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum2 : Summable fun n =>
      ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumN
  rw [logDeriv_apply, ← norm_neg, ← neg_div, hconv, LSeries]
  exact (norm_tsum_le_tsum_norm hsum2).trans (hsum2.tsum_le_tsum hpt hsumN)

/-- Davenport ch. 10: `Γℝ'/Γℝ(s) = -(log π)/2 + ψ(s/2)/2` away from the poles. -/
lemma logDeriv_Gammaℝ {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    logDeriv Gammaℝ s = -(Complex.log (Real.pi : ℂ)) / 2 + digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hP : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have h1 : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const (2 : ℂ)
    exact h1.const_cpow (Or.inl hpi)
  have hPne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hh : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const 2
  have hGd : DifferentiableAt ℂ Gamma (s / 2) := differentiableAt_Gamma _ hs
  have hGne : Gamma (s / 2) ≠ 0 := Gamma_ne_zero hs
  have e : Gammaℝ = (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) * (Gamma ∘ fun s : ℂ => s / 2) := by
    funext s; simp [Gammaℝ_def]
  have hdh : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
    have : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℂ)
    exact this.deriv
  rw [e, logDeriv_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) (g := Gamma ∘ fun s : ℂ => s / 2)
    s hPne hGne hP.differentiableAt (hGd.comp s hh), logDeriv_comp (f := Gamma) (g := fun s : ℂ => s / 2) hGd hh, hdh, logDeriv_apply,
    hP.deriv, ← digamma_def]
  field_simp

/-- elementary: `ψ(conj z) = conj ψ(z)`, from `Γ(conj z) = conj Γ(z)`. -/
lemma digamma_conj' (z : ℂ) : digamma (starRingEnd ℂ z) = starRingEnd ℂ (digamma z) := by
  have hG : (starRingEnd ℂ ∘ Gamma ∘ starRingEnd ℂ) = Gamma := by
    funext w; simp [Function.comp, Gamma_conj]
  have h1 := congrFun (deriv_conj_conj (f := Gamma)) z
  rw [hG] at h1
  simp only [Function.comp_apply] at h1
  have hd : deriv Gamma (starRingEnd ℂ z) = starRingEnd ℂ (deriv Gamma z) := by
    rw [h1, Complex.conj_conj]
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hd, Gamma_conj, map_div₀]

/-- elementary: the four lines avoid the poles of `Γ`, in the open strip `|Re z - σ| < 1/8`. -/
lemma not_pole_of_near {σ : ℝ} (hσ : σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) {z : ℂ}
    (hz : |z.re - σ| < 1 / 8) : ∀ m : ℕ, z ≠ -m := by
  intro m hm
  rw [hm] at hz
  simp at hz
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_lt] at hz
  rcases hσ with h | h | h | h <;> rw [h] at hz
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; norm_num at hz
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
      linarith [hz.1, hz.2]
  all_goals linarith [hz.1, hz.2]

/-- elementary, by compactness: `ψ` is bounded on the segment `σ + iu`, `|u| ≤ 1`. -/
lemma digamma_bdd_segment {σ : ℝ} (hσ : σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) :
    ∃ M : ℝ, ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖digamma ((σ : ℂ) + u * I)‖ ≤ M := by
  set U : Set ℂ := {z | |z.re - σ| < 1 / 8} with hU
  have hUo : IsOpen U :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
  have hd : DifferentiableOn ℂ Gamma U := fun z hz =>
    (differentiableAt_Gamma z (not_pole_of_near hσ hz)).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv Gamma) U := hd.deriv hUo
  have hcont : ∀ z ∈ U, ContinuousAt digamma z := by
    intro z hz
    have e : digamma = fun w => deriv Gamma w / Gamma w := by
      funext w; rw [digamma_def, logDeriv_apply]
    rw [e]
    exact ((hdd.differentiableAt (hUo.mem_nhds hz)).continuousAt).div
      ((hd.differentiableAt (hUo.mem_nhds hz)).continuousAt)
      (Gamma_ne_zero (not_pole_of_near hσ hz))
  have hcon : ContinuousOn (fun u : ℝ => digamma ((σ : ℂ) + u * I)) (Set.Icc (-1 : ℝ) 1) := by
    intro u _
    have hm : (σ : ℂ) + u * I ∈ U := by simp [hU]
    have hl : Continuous fun u : ℝ => (σ : ℂ) + u * I := by fun_prop
    exact (ContinuousAt.comp (f := fun u : ℝ => (σ : ℂ) + u * I) (hcont _ hm)
      hl.continuousAt).continuousWithinAt
  exact isCompact_Icc.exists_bound_of_continuousOn hcon

/-- Davenport ch. 10, Stirling, on one of the four lines. -/
lemma digamma_line_bound {σ : ℝ} (hσ : σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 2) := by
  obtain ⟨Ks, hKs, hst⟩ := LeanLab.PNTPort.ZetaZeros.digamma_strip
  obtain ⟨M, hM⟩ := digamma_bdd_segment hσ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hσ1 : -1 ≤ σ ∧ σ ≤ 2 := by
    rcases hσ with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  set K := max M 0 / Real.log 2 + 2 * Ks + 2 / Real.log 2 with hK
  refine ⟨K, by positivity, ?_⟩
  have pos : ∀ u : ℝ, 1 ≤ u → ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 2) := by
    intro u hu
    have h := hst u hu σ hσ1.1 hσ1.2
    rw [abs_of_nonneg (by linarith)]
    have hl : Real.log 2 ≤ Real.log (u + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h3 : Real.log (u + 3) ≤ 2 * Real.log (u + 2) := by
      rw [show 2 * Real.log (u + 2) = Real.log ((u + 2) ^ 2) by rw [Real.log_pow]; norm_num]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h2 : 2 ≤ 2 / Real.log 2 * Real.log (u + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
    have hM0 : 0 ≤ max M 0 / Real.log 2 * Real.log (u + 2) :=
      mul_nonneg (by positivity) (hl2.le.trans hl)
    calc _ ≤ Ks * Real.log (u + 3) + 2 := h
      _ ≤ Ks * (2 * Real.log (u + 2)) + 2 / Real.log 2 * Real.log (u + 2) := by gcongr
      _ ≤ K * Real.log (u + 2) := by rw [hK]; nlinarith
  intro u
  rcases le_or_gt 1 u with hu | hu
  · exact pos u hu
  rcases le_or_gt u (-1) with hu' | hu'
  · have e : (σ : ℂ) + u * I = starRingEnd ℂ ((σ : ℂ) + ((-u : ℝ) : ℂ) * I) := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [e, digamma_conj', Complex.norm_conj]
    have := pos (-u) (by linarith)
    rwa [abs_neg] at this
  · have hm := hM u ⟨hu'.le, hu.le⟩
    have hl : Real.log 2 ≤ Real.log (|u| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg u])
    have h1 : max M 0 ≤ max M 0 / Real.log 2 * Real.log (|u| + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hl (le_max_right _ _)
    have hL0 : 0 ≤ Real.log (|u| + 2) := hl2.le.trans hl
    have h2 : 0 ≤ (2 * Ks + 2 / Real.log 2) * Real.log (|u| + 2) := by positivity
    calc _ ≤ max M 0 := hm.trans (le_max_left _ _)
      _ ≤ K * Real.log (|u| + 2) := by rw [hK]; nlinarith

/-- Davenport ch. 10, Stirling: `|ψ(σ + iu)| ≤ K log(|u| + 2)` on the four vertical lines
`σ = -1/4, 1/4, 3/4, 5/4`, which avoid the poles of `ψ`. -/
theorem digamma_vert_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ,
    (σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) → ∀ u : ℝ,
      ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 2) := by
  obtain ⟨K1, h1, b1⟩ := digamma_line_bound (σ := -1 / 4) (Or.inl rfl)
  obtain ⟨K2, h2, b2⟩ := digamma_line_bound (σ := 1 / 4) (Or.inr (Or.inl rfl))
  obtain ⟨K3, h3, b3⟩ := digamma_line_bound (σ := 3 / 4) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨K4, h4, b4⟩ := digamma_line_bound (σ := 5 / 4) (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨K1 + K2 + K3 + K4, by positivity, fun σ hσ u => ?_⟩
  have hL : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
  rcases hσ with rfl | rfl | rfl | rfl
  · exact (b1 u).trans (by nlinarith)
  · exact (b2 u).trans (by nlinarith)
  · exact (b3 u).trans (by nlinarith)
  · exact (b4 u).trans (by nlinarith)

/-- Davenport ch. 10 and 16, Stirling for the digamma function: the log derivative of the gamma
factor at `Re s = -1/2` and at `Re s = 3/2` is `O(log(|t| + 2))`, uniformly in `χ`. -/
theorem logDeriv_gf_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    ‖logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖ ≤ C * Real.log (|t| + 2) ∧
    ‖logDeriv (DirichletCharacter.gammaFactor χ) (3 / 2 + t * I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨K, hK, hb⟩ := digamma_vert_bound
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  refine ⟨2 / Real.log 2 + K, by positivity, fun q χ t => ?_⟩
  have ht2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hhalf : Real.log (|t / 2| + 2) ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  -- the generic estimate at a point `w` with `w/2 = σ + i t/2`
  have key : ∀ w : ℂ, ∀ σ : ℝ, (σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) →
      w / 2 = (σ : ℂ) + ((t / 2 : ℝ) : ℂ) * I →
      ‖logDeriv Gammaℝ w‖ ≤ (2 / Real.log 2 + K) * Real.log (|t| + 2) := by
    intro w σ hσ hw
    have hnp : ∀ m : ℕ, w / 2 ≠ -m := by
      intro m hm
      have := congrArg Complex.re (hw.symm.trans hm)
      simp at this
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rcases hσ with h | h | h | h <;> rw [h] at this
      · have : (m : ℝ) = 1 / 4 := by linarith
        have h4 : (4 * m : ℝ) = 1 := by linarith
        have : 4 * m = 1 := by exact_mod_cast h4
        omega
      all_goals linarith
    rw [logDeriv_Gammaℝ hnp, hw]
    have hd := hb σ hσ (t / 2)
    calc _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖digamma ((σ : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖ :=
          norm_add_le _ _
      _ ≤ 3 / 2 + K * Real.log (|t| + 2) / 2 := by
          rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
          gcongr
          exact hd.trans (mul_le_mul_of_nonneg_left hhalf hK)
      _ ≤ (2 / Real.log 2 + K) * Real.log (|t| + 2) := by
          have h1 : 2 ≤ 2 / Real.log 2 * Real.log (|t| + 2) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
          have h0 : 0 ≤ K * Real.log (|t| + 2) :=
            mul_nonneg hK (le_trans hl2.le ht2)
          nlinarith
  rcases χ.even_or_odd with he | ho
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [e]
    refine ⟨key _ (-1 / 4) (Or.inl rfl) ?_, key _ (3 / 4) (Or.inr (Or.inr (Or.inl rfl))) ?_⟩ <;>
      push_cast <;> ring
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ ∘ fun s => s + 1 :=
      funext ho.gammaFactor_def
    have hGd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Gammaℝ z := fun z hz => by
      have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) z :=
        (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
      simpa only [inv_inv] using h
    have hcomp : ∀ w : ℂ, 0 < (w + 1).re → logDeriv (DirichletCharacter.gammaFactor χ) w =
        logDeriv Gammaℝ (w + 1) := by
      intro w hw
      rw [e, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + 1) (hGd _ hw)
        (differentiableAt_id.add_const 1)]
      simp
    refine ⟨?_, ?_⟩
    · rw [hcomp _ (by simp; norm_num)]
      exact key _ (1 / 4) (Or.inr (Or.inl rfl)) (by push_cast; ring)
    · rw [hcomp _ (by simp; norm_num)]
      exact key _ (5 / 4) (Or.inr (Or.inr (Or.inr rfl))) (by push_cast; ring)

/-- Davenport ch. 16 via the functional equation: `|L'/L(-1/2 + it, χ)| ≤ C log(q(|t| + 2))`,
uniformly in the primitive character. -/
theorem logDeriv_left_line : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ t : ℝ,
      ‖deriv χ.LFunction (-1 / 2 + t * I) / χ.LFunction (-1 / 2 + t * I)‖ ≤
        C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C2, hC2, h2⟩ := logDeriv_L_three_half_le
  obtain ⟨C3, hC3, h3⟩ := logDeriv_gf_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 2 * C3 + C2 / Real.log 2, by positivity, fun q _ χ hχ t => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  set L := Real.log (q * (|t| + 2)) with hL
  have hlq : Real.log q ≤ L := Real.log_le_log (by linarith) (by nlinarith)
  have hlt : Real.log (|t| + 2) ≤ L := Real.log_le_log (by linarith) (by nlinarith)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [logDeriv_fe_left hχ t]
  have e1 : ‖(Real.log q : ℂ)‖ = Real.log q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlq0]
  have a1 := (h3 q χ⁻¹ (-t)).2
  have a2 := (h3 q χ t).1
  have a3 := h2 q χ⁻¹ (-t)
  rw [abs_neg] at a1
  have hC2L : C2 ≤ C2 / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; exact mul_le_mul_of_nonneg_left hL2 hC2
  calc _ ≤ ‖-(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (3 / 2 + (-t : ℝ) * I) - logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖
          + ‖logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I)‖ := norm_sub_le _ _
    _ ≤ ‖-(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (3 / 2 + (-t : ℝ) * I)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖
          + ‖logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ ‖-(Real.log q : ℂ)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (3 / 2 + (-t : ℝ) * I)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖
          + ‖logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.log q + C3 * Real.log (|t| + 2) + C3 * Real.log (|t| + 2) + C2 := by
        rw [norm_neg, e1]; gcongr
    _ ≤ L + C3 * L + C3 * L + C2 / Real.log 2 * L := by gcongr
    _ = (1 + 2 * C3 + C2 / Real.log 2) * L := by ring

end LeanLab.Linnik.ExplicitFormula
