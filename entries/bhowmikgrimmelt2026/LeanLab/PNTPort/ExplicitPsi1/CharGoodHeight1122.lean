module

public import LeanLab.PNTPort.ExplicitPsi1.Edges
public import LeanLab.PNTPort.ZetaZeros.GoodHeight
public import LeanLab.HardyLittlewood1923.U1503LogDeriv
public import LeanLab.Linnik.ExplicitFormula.LeftHalf
public import LeanLab.BhowmikGrimmelt2026.RouteWindow508

/-!
# Good heights for primitive Dirichlet L-functions, uniform in the modulus

Unit P1122-0013, ROUTE BURST burst-20261122 session S2, port step 3 of the half weighted
truncated explicit formula for primitive nonprincipal characters, Davenport, Multiplicative
Number Theory, chapter 19, pages 115 to 118. AI wrote the Lean code. Binary Goldbach is OPEN.

Character analogue of `good_height_pm` of Edges.lean. Davenport chapter 19 page 116 says: "In the
choice of a modified value of T, we have to appeal to the lemma of §16 instead of that of §15,
and accordingly we get L'/L(σ ± iT, χ) = O(log² qT) for -1 ≤ σ ≤ 2." We prove this on
`-1/2 ≤ σ ≤ 2`, the strip the rectangle of the explicit formula needs, with a constant
uniform in `q` and `χ`, for every primitive `χ`, the case `q = 1` being `good_height_pm`.

Ingredients, all proved in the lab, no cited input:
* the window count, Davenport chapter 16 page 102 display (3), as
  `BhowmikGrimmelt2026.zero_window_count_full508`, uniform in `q`;
* the local expansion of `L'/L`, Davenport chapter 16 page 102 display (4), in the form of
  the Borel-Caratheodory bound `HardyLittlewood1923.U1503.logDeriv_L_wide`, uniform in `q`;
* the pigeonhole of Davenport chapter 17 page 108, `ZetaZeros.exists_far`;
* on `Re s < 1/2`, the functional equation differentiated logarithmically, Davenport chapter 9,
  and Stirling for the digamma function, chapter 10: `logDeriv_fe_strip1122` and
  `logDeriv_gf_strip1122` are copies, renamed, of `logDeriv_fe_strip` and `logDeriv_gf_strip`
  of `Linnik/ExplicitFormula/Heights.lean`, whose import closure is not built in this
  worktree; that file only proved the non uniform version `good_heights`, with a constant
  depending on `χ`.

Main results:
* `window_count1122`, `near_ordinates1122`: the zero ordinates near height `T` lie in a finite set
  of `O(log qT)` reals, uniformly in `q`.
* `char_good_height_right1122`: one `T'` serving `χ` and `χ⁻¹` at `±T'` on `1/2 ≤ σ ≤ 2`, for
  every nonprincipal `χ`, primitive or not.
* `char_good_height_pm1122`: the full statement on `-1/2 ≤ σ ≤ 2` for every primitive `χ`.
-/

@[expose] public section

namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Set
open LeanLab.Linnik.ExplicitFormula (gf_ne_zero_of_re_pos completed_eq_L_mul_gf
  ne_one_of_primitive rootNumber_ne_zero' gf_diff_of_ne digamma_conj')
open LeanLab.PNTPort.DirichletZF (Z one_le_Z)
open LeanLab.PNTPort.DirichletZF.U1482 (cen)
open LeanLab.HardyLittlewood1923.U1503 (KW KW_pos lZ lZ_pos logDeriv_L_wide)

/-- elementary: the gamma factor is nonzero off the real axis, its zeros being none and
`Gammaℝ` vanishing only at nonpositive even integers. -/
theorem gf_ne_zero_of_im_ne1122 {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h : s.im ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    intro h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    apply h; rw [hn]; simp
  · rw [hχ.gammaFactor_def]
    intro h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    apply h
    have : s = -(2 * n) - 1 := by rw [← hn]; ring
    rw [this]; simp

/-- Davenport ch. 9: for primitive `χ`, `Re s ≤ 1/2` and `Im s ≠ 0`, if `L(1 - s, χ̄) ≠ 0` then
`L(s, χ) ≠ 0` and `L'/L(s, χ) = -log q - γ'/γ(1 - s, χ̄) - γ'/γ(s, χ) - L'/L(1 - s, χ̄)`. -/
theorem logDeriv_fe_strip1122 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hre : s.re ≤ 1 / 2) (him : s.im ≠ 0) (h : (χ⁻¹).LFunction (1 - s) ≠ 0) :
    χ.LFunction s ≠ 0 ∧ deriv χ.LFunction s / χ.LFunction s =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)
        - logDeriv (DirichletCharacter.gammaFactor χ) s
        - deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s) := by
  set s0 := s with hs0def
  have hs0ne : s0 ≠ 0 := by intro e; apply him; rw [e]; simp
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  set A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ * (q : ℂ) ^ ((1 - s) - 1 / 2) with hA
  set ref : ℂ → ℂ := fun s => 1 - s with href
  set B : ℂ → ℂ := DirichletCharacter.gammaFactor χ⁻¹ ∘ ref with hB
  set Cc : ℂ → ℂ := (χ⁻¹).LFunction ∘ ref with hCc
  have hev : χ.LFunction =ᶠ[nhds s0] A * B * Cc / DirichletCharacter.gammaFactor χ := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show s0.re < 1 by linarith),
      (isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds him] with s hs hsi
    have hs : s.re < 1 := hs
    have hsi : s.im ≠ 0 := hsi
    have hsne : s ≠ 0 := by intro e; apply hsi; rw [e]; simp
    have hr1 : 0 < (1 - s).re := by simp; linarith
    have h1ne : 1 - s ≠ 0 := by intro e; rw [e] at hr1; simp at hr1
    have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne), hfe,
      completed_eq_L_mul_gf χ⁻¹ (Or.inl h1ne) (gf_ne_zero_of_re_pos χ⁻¹ hr1)]
    simp only [Pi.mul_apply, Pi.div_apply, hA, hB, hCc, href, Function.comp_apply]
    ring
  have hr1 : 0 < (1 - s0).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hrefd : DifferentiableAt ℂ ref s0 := (differentiableAt_const _).sub differentiableAt_id
  have hderef : deriv ref s0 = -1 := by
    have hd : HasDerivAt ref (-1) s0 := by
      simpa using (hasDerivAt_id s0).const_sub (1 : ℂ)
    exact hd.deriv
  have hgfi := gf_ne_zero_of_re_pos χ⁻¹ hr1
  have hgfid : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ⁻¹) (ref s0) :=
    gf_diff_of_ne χ⁻¹ hgfi
  have hL1 : (1 - s0) ≠ 1 := by intro e; apply hs0ne; linear_combination -e
  have hLi : (χ⁻¹).LFunction (ref s0) ≠ 0 := h
  have hLid : DifferentiableAt ℂ (χ⁻¹).LFunction (ref s0) :=
    DirichletCharacter.differentiableAt_LFunction χ⁻¹ _ (Or.inl hL1)
  have hgf0 := gf_ne_zero_of_im_ne1122 χ him
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
  refine ⟨?_, ?_⟩
  · rw [hev.eq_of_nhds]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
  rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_div (f := A * B * Cc) (g := DirichletCharacter.gammaFactor χ) s0
      (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
      ((hAd.differentiableAt.mul hBd).mul hCd) hgf0d,
    logDeriv_mul (f := A * B) (g := Cc) s0 (mul_ne_zero hAne hBne) hCne
      (hAd.differentiableAt.mul hBd) hCd,
    logDeriv_mul (f := A) (g := B) s0 hAne hBne hAd.differentiableAt hBd, hlogA,
    hB, hCc, logDeriv_comp hgfid hrefd, logDeriv_comp hLid hrefd, hderef]
  simp only [href, logDeriv_apply]
  ring

/-- Davenport ch. 10, Stirling for the digamma function: the log derivative of the gamma factor
is `O(log(|t| + 2))` on `-1/2 ≤ σ ≤ 3/2`, `|t| ≥ 1`, uniformly in `χ`. -/
theorem logDeriv_gf_strip1122 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (σ t : ℝ),
    σ ∈ Icc (-1 / 2 : ℝ) (3 / 2) → 2 ≤ |t| →
      ‖logDeriv (DirichletCharacter.gammaFactor χ) (σ + t * I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨K, hK, hb⟩ := LeanLab.PNTPort.ZetaZeros.digamma_strip
  -- both signs of the height, by `ψ(conj z) = conj ψ(z)`
  have hb' : ∀ σ u : ℝ, -1 ≤ σ → σ ≤ 2 → 1 ≤ |u| →
      ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 3) + 2 := by
    intro σ u h1 h2 hu
    rcases le_or_gt 0 u with h0 | h0
    · rw [abs_of_nonneg h0] at hu ⊢; exact hb u hu σ h1 h2
    · rw [abs_of_neg h0] at hu ⊢
      have e : (σ : ℂ) + u * I = starRingEnd ℂ ((σ : ℂ) + ((-u : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [e, digamma_conj', Complex.norm_conj]
      exact hb (-u) hu σ h1 h2
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  refine ⟨K + 4 / Real.log 4, by positivity, fun q χ σ t hσ ht => ?_⟩
  have ht4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hhalf : Real.log (|t / 2| + 3) ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith
  have key : ∀ w : ℂ, ∀ σ' : ℝ, -1 ≤ σ' → σ' ≤ 2 →
      w / 2 = (σ' : ℂ) + ((t / 2 : ℝ) : ℂ) * I →
      ‖logDeriv Gammaℝ w‖ ≤ (K + 4 / Real.log 4) * Real.log (|t| + 2) := by
    intro w σ' h1 h2 hw
    have hnp : ∀ m : ℕ, w / 2 ≠ -m := by
      intro m hm
      have := congrArg Complex.im (hw.symm.trans hm)
      simp at this
      rw [this, abs_zero] at ht; linarith
    rw [LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ hnp, hw]
    have hd := hb' σ' (t / 2) h1 h2 (by rw [abs_div, abs_two]; linarith)
    calc _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
          ‖digamma ((σ' : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖ := norm_add_le _ _
      _ ≤ 3 / 2 + (K * Real.log (|t| + 2) + 2) / 2 := by
          rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
          gcongr
          exact hd.trans (by gcongr)
      _ ≤ (K + 4 / Real.log 4) * Real.log (|t| + 2) := by
          have h1 : 4 ≤ 4 / Real.log 4 * Real.log (|t| + 2) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hl4]; linarith
          have h0 : 0 ≤ K * Real.log (|t| + 2) := mul_nonneg hK.le (le_trans hl4.le ht4)
          nlinarith
  rcases χ.even_or_odd with he | ho
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [e]
    exact key _ (σ / 2) (by linarith [hσ.1]) (by linarith [hσ.2]) (by push_cast; ring)
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ ∘ fun s => s + 1 :=
      funext ho.gammaFactor_def
    have hGd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Gammaℝ z := fun z hz => by
      have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) z :=
        (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
      simpa only [inv_inv] using h
    have hw : 0 < ((σ : ℂ) + t * I + 1).re := by simp; linarith [hσ.1]
    rw [e, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + 1) (hGd _ hw)
      (differentiableAt_id.add_const 1)]
    simp only [deriv_add_const', deriv_id'', mul_one]
    exact key _ ((σ + 1) / 2) (by linarith [hσ.1]) (by linarith [hσ.2]) (by push_cast; ring)

/-- Davenport chapter 16 page 102, the zeros counted in display (3) have multiplicity at least
one: for `ψ ≠ 1`, `L(s, ψ)` is entire and not identically zero, so at a zero its analytic order
is finite and positive. -/
theorem one_le_mult1122 {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {ρ : ℂ}
    (hρ : ψ.LFunction ρ = 0) : 1 ≤ analyticOrderNatAt ψ.LFunction ρ := by
  have hent : AnalyticOnNhd ℂ ψ.LFunction Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hψ).analyticAt z
  have h2 : analyticOrderAt ψ.LFunction 2 ≠ ⊤ := by
    rw [(hent 2 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (by norm_num))]
    simp
  have htop : analyticOrderAt ψ.LFunction ρ ≠ ⊤ :=
    hent.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ 2) (Set.mem_univ ρ) h2
  have h0 : analyticOrderAt ψ.LFunction ρ ≠ 0 := by
    rw [ne_eq, analyticOrderAt_eq_zero]
    push Not
    exact ⟨hent ρ (Set.mem_univ _), hρ⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
  rw [← hn] at h0
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h0)

/-- Davenport chapter 16 page 102 display (3), in the form of a window count: for `ψ ≠ 1` mod
`q`, the zeros of `L(s, ψ)` in the open critical strip with `|γ - c| ≤ 1` form a finite set
of at most `A log (q (|c| + 2))` elements, `A` absolute. From the multiplicity count
`BhowmikGrimmelt2026.zero_window_count_full508` and `one_le_mult1122`. -/
theorem window_count1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
    ψ ≠ 1 → ∀ c : ℝ,
      ∃ hf : {ρ : ℂ | ψ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - c| ≤ 1}.Finite,
        (hf.toFinset.card : ℝ) ≤ A * Real.log ((q : ℝ) * (|c| + 2)) := by
  obtain ⟨A, hA0, hA⟩ := LeanLab.BhowmikGrimmelt2026.zero_window_count_full508
  refine ⟨A, hA0, fun q _ ψ hψ c => ?_⟩
  set S := {ρ : ℂ | ψ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - c| ≤ 1} with hS
  have hcard : ∀ W : Finset ℂ, (↑W : Set ℂ) ⊆ S →
      (W.card : ℝ) ≤ A * Real.log ((q : ℝ) * (|c| + 2)) := by
    intro W hW
    have hsum := hA q ψ c W (fun ρ hρ => hW hρ)
    refine le_trans ?_ hsum
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have h1 := one_le_mult1122 hψ (hW hρ).1
    have h2 : (1 : ℝ) ≤ (LeanLab.BhowmikGrimmelt2026.mult ψ ρ : ℝ) := Nat.one_le_cast.mpr h1
    simpa using h2
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨W, hWS, hWc⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈A * Real.log ((q : ℝ) * (|c| + 2))⌉₊ + 1)
    have h1 := hcard W hWS
    rw [hWc] at h1
    push_cast at h1
    have := Nat.le_ceil (A * Real.log ((q : ℝ) * (|c| + 2)))
    linarith
  exact ⟨hfin, hcard _ (by simp)⟩

/-- elementary: for `q ≥ 1`, `T ≥ 5` and `0 ≤ u ≤ T + 4`, `log (q u) ≤ 2 log (q T)`, and
`1 ≤ log (q T)`. -/
theorem log_qT_facts1122 {q : ℕ} [NeZero q] {T : ℝ} (hT : 5 ≤ T) :
    1 ≤ Real.log ((q : ℝ) * T) ∧ ∀ u : ℝ, 0 < u → u ≤ T + 4 →
      Real.log ((q : ℝ) * u) ≤ 2 * Real.log ((q : ℝ) * T) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨?_, fun u hu hu4 => ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  · rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    have e : ((q : ℝ) * T) ^ (2 : ℝ) = (q * T) ^ 2 := by norm_cast
    rw [e]
    have hT4 : T + 4 ≤ T ^ 2 := by nlinarith
    have : u ≤ T ^ 2 := by linarith
    have hqq : (q : ℝ) ≤ q ^ 2 := by nlinarith
    calc (q : ℝ) * u ≤ q * T ^ 2 := by gcongr
      _ ≤ q ^ 2 * T ^ 2 := by gcongr
      _ = (q * T) ^ 2 := by ring

/-- Davenport chapter 17 page 108 with chapter 16 page 102 display (3): for `ψ ≠ 1` mod `q`
and `T ≥ 5`, the absolute ordinates `|γ|` of the zeros `ρ` of `L(s, ψ)` in the open critical
strip with `||γ| - (T + 1/2)| ≤ 83/50` lie in a finite set of at most `8 A log (qT)` reals,
`A` absolute. Four windows of `window_count1122`. -/
theorem near_ordinates1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ T : ℝ, 5 ≤ T → ∃ F : Finset ℝ,
      (F.card : ℝ) ≤ 8 * A * Real.log ((q : ℝ) * T) ∧
      ∀ ρ : ℂ, ψ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        |(|ρ.im|) - (T + 1 / 2)| ≤ 83 / 50 → |ρ.im| ∈ F := by
  classical
  obtain ⟨A, hA0, hW⟩ := window_count1122
  refine ⟨A, hA0, fun q _ ψ hψ T hT => ?_⟩
  obtain ⟨hℓ1, hℓu⟩ := log_qT_facts1122 (q := q) hT
  obtain ⟨f1, b1⟩ := hW q ψ hψ (T + 1 / 2 - 4 / 5)
  obtain ⟨f2, b2⟩ := hW q ψ hψ (T + 1 / 2 + 4 / 5)
  obtain ⟨f3, b3⟩ := hW q ψ hψ (-(T + 1 / 2 - 4 / 5))
  obtain ⟨f4, b4⟩ := hW q ψ hψ (-(T + 1 / 2 + 4 / 5))
  have hlc : ∀ c : ℝ, |c| ≤ T + 2 → A * Real.log ((q : ℝ) * (|c| + 2)) ≤
      A * (2 * Real.log ((q : ℝ) * T)) := fun c hc =>
    mul_le_mul_of_nonneg_left (hℓu _ (by positivity) (by linarith)) hA0
  have a1 : |T + 1 / 2 - 4 / 5| ≤ T + 2 := by rw [abs_le]; constructor <;> linarith
  have a2 : |T + 1 / 2 + 4 / 5| ≤ T + 2 := by rw [abs_le]; constructor <;> linarith
  have a3 : |-(T + 1 / 2 - 4 / 5)| ≤ T + 2 := by rw [abs_neg]; exact a1
  have a4 : |-(T + 1 / 2 + 4 / 5)| ≤ T + 2 := by rw [abs_neg]; exact a2
  refine ⟨(f1.toFinset ∪ f2.toFinset ∪ f3.toFinset ∪ f4.toFinset).image
    (fun ρ : ℂ => |ρ.im|), ?_, ?_⟩
  · have h1 := Finset.card_image_le (s := f1.toFinset ∪ f2.toFinset ∪ f3.toFinset ∪ f4.toFinset)
      (f := fun ρ : ℂ => |ρ.im|)
    have h2 := Finset.card_union_le (f1.toFinset ∪ f2.toFinset ∪ f3.toFinset) f4.toFinset
    have h3 := Finset.card_union_le (f1.toFinset ∪ f2.toFinset) f3.toFinset
    have h4 := Finset.card_union_le f1.toFinset f2.toFinset
    have h5 : ((((f1.toFinset ∪ f2.toFinset ∪ f3.toFinset ∪ f4.toFinset).image
        (fun ρ : ℂ => |ρ.im|)).card : ℕ) : ℝ) ≤
        (f1.toFinset.card : ℝ) + f2.toFinset.card + f3.toFinset.card + f4.toFinset.card := by
      exact_mod_cast h1.trans (h2.trans (by omega))
    linarith [b1.trans (hlc _ a1), b2.trans (hlc _ a2), b3.trans (hlc _ a3),
      b4.trans (hlc _ a4)]
  · intro ρ hz h0 h1 hρ
    rw [Finset.mem_image]
    refine ⟨ρ, ?_, rfl⟩
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [abs_le] at hρ
    rcases le_or_gt 0 ρ.im with hs | hs
    · rw [abs_of_nonneg hs] at hρ
      by_cases hc : ρ.im ≤ T + 1 / 2
      · left; left; left
        exact ⟨hz, h0, h1, by rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2]⟩
      · left; left; right
        exact ⟨hz, h0, h1, by rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2]⟩
    · rw [abs_of_neg hs] at hρ
      by_cases hc : -(T + 1 / 2) ≤ ρ.im
      · left; right
        exact ⟨hz, h0, h1, by rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2]⟩
      · right
        exact ⟨hz, h0, h1, by rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2]⟩

/-- Davenport chapter 19 page 116, the choice of a modified `T` by the lemma of §16, in the
half `1/2 ≤ σ ≤ 2`, following chapter 17 page 108: among the ordinates of the zeros near
height `T`, which number `O(log qT)` by chapter 16 page 102 display (3), there is a gap, so for
some `T'` in `[T, T + 1]` every zero is at distance `≫ (log qT)⁻¹` from `±T'`, and then by
chapter 16 page 102 display (4) each of the `O(log qT)` terms of the local expansion is
`O(log qT)`. One `T'` serves `χ` and `χ⁻¹` at both `T'` and `-T'`, for every nonprincipal
`χ` mod `q`, primitive or not, with an absolute constant. -/
theorem char_good_height_right1122 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
      ∀ ψ ∈ ({χ, χ⁻¹} : Set (DirichletCharacter ℂ q)), ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
        ∀ τ ∈ ({T', -T'} : Set ℝ), ψ.LFunction (σ + τ * I) ≠ 0 ∧
          ‖deriv ψ.LFunction (σ + τ * I) / ψ.LFunction (σ + τ * I)‖ ≤
            C * Real.log ((q : ℝ) * T) ^ 2 := by
  classical
  obtain ⟨A, hA0, hN⟩ := near_ordinates1122
  have hKW := KW_pos
  have hlZ := lZ_pos
  have hZ := one_le_Z
  have hK1p : 0 ≤ Real.log (20 * Z) + 2 := by
    have : 0 ≤ Real.log (20 * Z) := Real.log_nonneg (by linarith)
    linarith
  refine ⟨(KW + 2 / lZ + 32 * A / lZ) * (Real.log (20 * Z) + 2), by positivity,
    fun q _ χ hχ T hT => ?_⟩
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨hℓ1, hℓu⟩ := log_qT_facts1122 (q := q) hT
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓ] at hℓ1 hℓu ⊢
  obtain ⟨F1, hF1c, hF1⟩ := hN q χ hχ T hT
  obtain ⟨F2, hF2c, hF2⟩ := hN q χ⁻¹ hχi T hT
  rw [← hℓ] at hF1c hF2c
  have hGcard : ((F1 ∪ F2).card : ℝ) ≤ 16 * A * ℓ := by
    have h1 : ((F1 ∪ F2).card : ℝ) ≤ F1.card + F2.card := by
      exact_mod_cast Finset.card_union_le F1 F2
    linarith
  obtain ⟨T', hT'I, hfar⟩ := LeanLab.PNTPort.ZetaZeros.exists_far (F1 ∪ F2) T
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (2 * (((F1 ∪ F2).card : ℝ) + 1)) := ⟨_, rfl⟩
  rw [← hδ] at hfar
  have hδpos : 0 < δ := by rw [hδ]; positivity
  refine ⟨T', hT'I, fun ψ hψ σ hσ τ hτ => ?_⟩
  have hψ1 : ψ ≠ 1 := by rcases hψ with rfl | rfl; exacts [hχ, hχi]
  have hmem : ∀ ρ : ℂ, ψ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |(|ρ.im|) - (T + 1 / 2)| ≤ 83 / 50 → |ρ.im| ∈ F1 ∪ F2 := by
    intro ρ hz h0 h1 hρ
    rcases hψ with rfl | rfl
    · exact Finset.mem_union_left _ (hF1 ρ hz h0 h1 hρ)
    · exact Finset.mem_union_right _ (hF2 ρ hz h0 h1 hρ)
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  have hτabs : |τ| = T' := by
    rcases hτ with h | h
    · rw [h]; exact abs_of_nonneg (by linarith [hT'I.1])
    · rw [h, abs_neg]; exact abs_of_nonneg (by linarith [hT'I.1])
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = σ + τ * I := ⟨_, rfl⟩
  rw [← hs]
  have hsc : ‖s - cen τ‖ ≤ 29 / 20 * (7 / 10) := by
    have e : s - cen τ = ((σ - 3 / 2 : ℝ) : ℂ) := by rw [hs, cen]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hfarρ : ∀ ρ : ℂ, ψ.LFunction ρ = 0 → ‖ρ - cen τ‖ ≤ 29 / 20 * (4 / 5) →
      δ ≤ |τ - ρ.im| := by
    intro ρ hz hd
    have hre : |(ρ - cen τ).re| ≤ ‖ρ - cen τ‖ := Complex.abs_re_le_norm _
    have him : |(ρ - cen τ).im| ≤ ‖ρ - cen τ‖ := Complex.abs_im_le_norm _
    have ere : (ρ - cen τ).re = ρ.re - 3 / 2 := by simp [cen]
    have eim : (ρ - cen τ).im = ρ.im - τ := by simp [cen]
    rw [ere] at hre; rw [eim] at him
    have hre' := abs_le.mp (hre.trans hd)
    have hre1 : ρ.re < 1 := by
      by_contra hc; push Not at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) hc hz
    have h3 := abs_abs_sub_abs_le ρ.im τ
    rw [hτabs] at h3
    have hnear : |(|ρ.im|) - (T + 1 / 2)| ≤ 83 / 50 := by
      have h4 := him.trans hd
      rw [abs_le] at h3 ⊢
      constructor <;> linarith [hT'I.1, hT'I.2, h3.1, h3.2]
    have hfa := hfar _ (hmem ρ hz (by linarith [hre'.1]) hre1 hnear)
    have h5 := abs_abs_sub_abs_le τ ρ.im
    rw [hτabs] at h5
    linarith
  have hsim : s.im = τ := by rw [hs]; simp
  have hne : ψ.LFunction s ≠ 0 := by
    intro hz
    have := hfarρ s hz (hsc.trans (by norm_num))
    rw [hsim, sub_self, abs_zero] at this
    linarith
  refine ⟨hne, ?_⟩
  have hd : ∀ ρ : ℂ, ψ.LFunction ρ = 0 → ‖ρ - cen τ‖ ≤ 29 / 20 * (4 / 5) →
      δ ≤ ‖s - ρ‖ := by
    intro ρ hz hdd
    have h1 := hfarρ ρ hz hdd
    have h2 : |(s - ρ).im| ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    have e : (s - ρ).im = τ - ρ.im := by rw [Complex.sub_im, hsim]
    rw [e] at h2; linarith
  have hb' := logDeriv_L_wide hψ1 τ hsc hne hδpos hd
  refine hb'.trans ?_
  have hlog1 : Real.log (20 * q * (|τ| + 3) * Z) ≤ (Real.log (20 * Z) + 2) * ℓ := by
    have e : (20 : ℝ) * q * (|τ| + 3) * Z = (20 * Z) * (q * (|τ| + 3)) := by ring
    have hZ0 : (0 : ℝ) < 20 * Z := by linarith
    rw [e, Real.log_mul hZ0.ne' (by positivity)]
    have h1 : Real.log ((q : ℝ) * (|τ| + 3)) ≤ 2 * ℓ :=
      hℓu _ (by positivity) (by rw [hτabs]; linarith [hT'I.2])
    have h0 : 0 ≤ Real.log (20 * Z) := Real.log_nonneg (by linarith)
    nlinarith
  have hinv : 1 / (lZ * δ) = 2 * (((F1 ∪ F2).card : ℝ) + 1) / lZ := by
    rw [hδ, mul_one_div, one_div_div]
  have hfac : KW + 1 / (lZ * δ) ≤ (KW + 2 / lZ + 32 * A / lZ) * ℓ := by
    rw [hinv]
    have e1 : 2 * (((F1 ∪ F2).card : ℝ) + 1) / lZ =
        2 / lZ + 2 * ((F1 ∪ F2).card : ℝ) / lZ := by ring
    rw [e1]
    have h2 : 2 * ((F1 ∪ F2).card : ℝ) / lZ ≤ 32 * A / lZ * ℓ := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hlZ.le
      linarith
    have h3 : KW + 2 / lZ ≤ (KW + 2 / lZ) * ℓ := by
      have : 0 ≤ KW + 2 / lZ := by positivity
      nlinarith
    have e2 : (KW + 2 / lZ + 32 * A / lZ) * ℓ = (KW + 2 / lZ) * ℓ + 32 * A / lZ * ℓ := by
      ring
    rw [e2]; linarith
  have hfac0 : 0 ≤ KW + 1 / (lZ * δ) := by positivity
  have hlog0 : 0 ≤ Real.log (20 * q * (|τ| + 3) * Z) := Real.log_nonneg (by
    have h3 : (1 : ℝ) ≤ |τ| + 3 := by linarith [abs_nonneg τ]
    have h20 : (1 : ℝ) ≤ 20 * q := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h20 h3) hZ)
  have hℓ0 : 0 ≤ ℓ := by linarith
  calc (KW + 1 / (lZ * δ)) * Real.log (20 * q * (|τ| + 3) * Z)
      ≤ ((KW + 2 / lZ + 32 * A / lZ) * ℓ) * ((Real.log (20 * Z) + 2) * ℓ) :=
        mul_le_mul hfac hlog1 hlog0 (by positivity)
    _ = (KW + 2 / lZ + 32 * A / lZ) * (Real.log (20 * Z) + 2) * ℓ ^ 2 := by ring

/-- **Good heights for primitive characters, uniform in `q`.** Davenport chapter 19 page 116:
"In the choice of a modified value of T, we have to appeal to the lemma of §16 instead of that
of §15, and accordingly we get L'/L(σ ± iT, χ) = O(log² qT)", here on `-1/2 ≤ σ ≤ 2`. There
is an absolute `C > 0` such that for every `q`, every primitive `χ` mod `q` and every `T ≥ 5`,
some `T'` in `[T, T + 1]` has `L(σ ± iT', χ) ≠ 0` and `‖L'/L(σ ± iT', χ)‖ ≤ C log² (qT)` for all
`σ` in `[-1/2, 2]`. The case `q = 1` is `good_height_pm`; for `q ≠ 1` the half `σ ≥ 1/2` is
`char_good_height_right1122` and the half `σ < 1/2` follows from it for `χ⁻¹` at `1 - s` by the
functional equation, Davenport chapter 9, and Stirling, chapter 10. -/
theorem char_good_height_pm1122 : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
      ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤
          C * Real.log ((q : ℝ) * T) ^ 2 := by
  obtain ⟨Cz, hCz, hz⟩ := good_height_pm
  obtain ⟨CR, hCR, hR⟩ := char_good_height_right1122
  obtain ⟨CG, hCG, hGm⟩ := logDeriv_gf_strip1122
  refine ⟨Cz + CR + 1 + 4 * CG, by positivity, fun q _ χ hχ T hT => ?_⟩
  rcases eq_or_ne q 1 with rfl | hq
  · -- `q = 1`: the zeta function
    obtain ⟨T', hT', hb⟩ := hz T hT
    refine ⟨T', hT', fun σ hσ τ hτ => ?_⟩
    obtain ⟨hne, hle⟩ := hb σ hσ τ hτ
    rw [DirichletCharacter.LFunction_modOne_eq]
    refine ⟨hne, hle.trans ?_⟩
    rw [Nat.cast_one, one_mul]
    have h0 : 0 ≤ Real.log T ^ 2 := sq_nonneg _
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨hℓ1, hℓu⟩ := log_qT_facts1122 (q := q) hT
  set ℓ := Real.log ((q : ℝ) * T) with hℓ
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hχ hq
  obtain ⟨T', hT'I, hb⟩ := hR q χ hχ1 T hT
  refine ⟨T', hT'I, fun σ hσ τ hτ => ?_⟩
  have hL2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hτabs : |τ| = T' := by
    rcases hτ with rfl | rfl
    · exact abs_of_nonneg (by linarith [hT'I.1])
    · rw [abs_neg]; exact abs_of_nonneg (by linarith [hT'I.1])
  have hτ1 : 2 ≤ |τ| := by rw [hτabs]; linarith [hT'I.1]
  have hτT : |τ| ≤ T + 1 := by rw [hτabs]; exact hT'I.2
  have htau : Real.log (|τ| + 2) ≤ 2 * ℓ ^ 2 := by
    have h1 : Real.log (|τ| + 2) ≤ Real.log ((q : ℝ) * (|τ| + 2)) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hq1)
    have h2 := hℓu (|τ| + 2) (by positivity) (by linarith)
    linarith
  by_cases hσ2 : 1 / 2 ≤ σ
  · obtain ⟨hne, hle⟩ := hb χ (by simp) σ ⟨hσ2, hσ.2⟩ τ hτ
    refine ⟨hne, hle.trans ?_⟩
    have : 0 ≤ (Cz + 1 + 4 * CG) * ℓ ^ 2 := by positivity
    nlinarith
  · push Not at hσ2
    set s : ℂ := σ + τ * I with hs
    have hre : s.re = σ := by simp [hs]
    have him : s.im = τ := by simp [hs]
    have h1s : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hτ' : -τ ∈ ({T', -T'} : Set ℝ) := by
      rcases hτ with rfl | rfl
      · right; rfl
      · left; simp
    obtain ⟨hne', hle'⟩ := hb χ⁻¹ (by simp) (1 - σ) ⟨by linarith, by linarith [hσ.1]⟩ (-τ) hτ'
    rw [← h1s] at hne' hle'
    have himne : s.im ≠ 0 := by rw [him]; intro h0; rw [h0, abs_zero] at hτ1; linarith
    obtain ⟨hne, heq⟩ := logDeriv_fe_strip1122 hχ (by rw [hre]; exact hσ2.le) himne hne'
    refine ⟨hne, ?_⟩
    rw [heq]
    have hg1 : ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ ≤
        CG * (2 * ℓ ^ 2) := by
      rw [h1s]
      refine (hGm q χ⁻¹ (1 - σ) (-τ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
        (by rw [abs_neg]; exact hτ1)).trans ?_
      rw [abs_neg]
      exact mul_le_mul_of_nonneg_left htau hCG
    have hg2 : ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤ CG * (2 * ℓ ^ 2) :=
      (hGm q χ σ τ ⟨hσ.1, by linarith⟩ hτ1).trans (mul_le_mul_of_nonneg_left htau hCG)
    have hlogq : ‖(-(Real.log q : ℂ))‖ ≤ 1 * ℓ ^ 2 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg q)]
      have : Real.log q ≤ ℓ := Real.log_le_log (by positivity)
        (le_mul_of_one_le_right (by positivity) (by linarith))
      linarith
    have hfin : (1 * ℓ ^ 2 + CG * (2 * ℓ ^ 2) + CG * (2 * ℓ ^ 2)) + CR * ℓ ^ 2 ≤
        (Cz + CR + 1 + 4 * CG) * ℓ ^ 2 := by
      have : 0 ≤ Cz * ℓ ^ 2 := by positivity
      nlinarith
    refine le_trans ?_ hfin
    calc _ ≤ ‖-(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)
            - logDeriv (DirichletCharacter.gammaFactor χ) s‖ +
          ‖deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s)‖ := norm_sub_le _ _
      _ ≤ (‖-(Real.log q : ℂ)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖) +
          ‖deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s)‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ (1 * ℓ ^ 2 + CG * (2 * ℓ ^ 2) + CG * (2 * ℓ ^ 2)) + CR * ℓ ^ 2 := by gcongr

end LeanLab.PNTPort.ExplicitPsi1
