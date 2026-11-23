module

public import LeanLab.HelfgottMajor.Conjugate669
public import LeanLab.HelfgottMajor.Laurent669
public import LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

/-!
Local logarithmic derivative computations for the general residue at zero.
Source P0014 page 33, displays 4.8 and 4.9.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.LogResidue669
open Real Complex Filter Set Classical
open LeanLab.Linnik.ExplicitFormula
open scoped Topology

/-- P0014 page 33, display 4.8, before removing the gamma factors. The logarithmic
functional equation for the completed L function at zero and one. -/
theorem completed_logDeriv_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    logDeriv (DirichletCharacter.completedLFunction χ) 0 =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 1 := by
  have hn : χ ≠ 1 := ne_one_of_primitive hχ hq
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hn
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hroot := rootNumber_ne_zero' hχ
  let A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ *
    (q : ℂ) ^ ((1 - s) - 1 / 2)
  let ref : ℂ → ℂ := fun s => 1 - s
  let B : ℂ → ℂ := DirichletCharacter.completedLFunction χ⁻¹ ∘ ref
  have heq : DirichletCharacter.completedLFunction χ = A * B := by
    funext s
    have h := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at h
    simpa only [A, B, ref, Pi.mul_apply, Function.comp_apply, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hA0 : A 0 ≠ 0 := mul_ne_zero hroot (cpow_ne_zero_iff.mpr (Or.inl hq0))
  have hB0 : B 0 ≠ 0 := by
    simp only [B, ref, Function.comp_apply, sub_zero]
    rw [completed_eq_L_mul_gf χ⁻¹ (Or.inr hq)
      (gf_ne_zero_of_re_pos χ⁻¹ (by norm_num : 0 < (1 : ℂ).re))]
    exact mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl hi) (by norm_num)) (gf_ne_zero_of_re_pos χ⁻¹ (by norm_num))
  have hRef : HasDerivAt ref (-1) 0 := (hasDerivAt_id (0 : ℂ)).const_sub 1
  have hExp : HasDerivAt (fun s : ℂ => (1 - s) - 1 / 2) (-1) 0 := by
    simpa using hRef.sub_const (1 / 2 : ℂ)
  have hAd : HasDerivAt A (A 0 * Complex.log q * (-1)) 0 := by
    simpa only [A, mul_assoc] using (hExp.const_cpow (Or.inl hq0)).const_mul
      (DirichletCharacter.rootNumber χ)
  have hBd : DifferentiableAt ℂ B 0 :=
    ((DirichletCharacter.differentiable_completedLFunction hi) _).comp 0 hRef.differentiableAt
  have hlogA : logDeriv A 0 = -(Real.log q : ℂ) := by
    rw [logDeriv_apply, hAd.deriv, Complex.natCast_log, div_eq_iff hA0]
    ring
  calc
    logDeriv (DirichletCharacter.completedLFunction χ) 0 = logDeriv (A * B) 0 :=
      congrArg (fun f => logDeriv f 0) heq
    _ = -(Real.log q : ℂ) - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 1 := by
      rw [logDeriv_mul (f := A) (g := B) 0 hA0 hB0 hAd.differentiableAt hBd,
        hlogA]
      change -(Real.log q : ℂ) +
        logDeriv (DirichletCharacter.completedLFunction χ⁻¹ ∘ ref) 0 = _
      rw [logDeriv_comp ((DirichletCharacter.differentiable_completedLFunction hi) _)
          hRef.differentiableAt, hRef.deriv]
      simp only [ref, sub_zero]
      ring

/-- P0014 page 33, displays 4.8 and 4.9. The gamma logarithmic derivative at one,
with its two parity values written out. -/
theorem gammaFactor_logDeriv_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    logDeriv (DirichletCharacter.gammaFactor χ) 1 =
      if χ.Even then
        ((-(Real.log π + 2 * Real.log 2 + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ)
      else ((-(Real.log π + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) := by
  have hn1 : ∀ m : ℕ, (1 : ℂ) / 2 ≠ -m := by
    intro m hm
    have h := congrArg Complex.re hm
    norm_num at h
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hn2 : ∀ m : ℕ, (2 : ℂ) / 2 ≠ -m := by
    intro m hm
    have h := congrArg Complex.re hm
    norm_num at h
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hlog2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    simpa using (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rcases χ.even_or_odd with he | ho
  · have hg : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [if_pos he, hg, logDeriv_Gammaℝ hn1, digamma_one_half,
      ← Complex.ofReal_log pi_pos.le, hlog2]
    push_cast
    ring
  · have hg : DirichletCharacter.gammaFactor χ = Gammaℝ ∘ (fun s : ℂ => s + 1) :=
      funext ho.gammaFactor_def
    have hd : DifferentiableAt ℂ Gammaℝ ((1 : ℂ) + 1) := by
      convert (differentiable_Gammaℝ_inv ((1 : ℂ) + 1)).inv
        (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num))) using 1
      funext z
      simp only [Pi.inv_apply, inv_inv]
    have hlin : deriv (fun s : ℂ => s + 1) 1 = 1 := by
      simpa only [id_eq] using ((hasDerivAt_id (1 : ℂ)).add_const 1).deriv
    rw [if_neg ho.not_even, hg, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + 1) hd
      ((differentiableAt_id (x := (1 : ℂ))).add_const 1),
      hlin]
    norm_num only [show (1 : ℂ) + 1 = 2 by norm_num, one_mul, mul_one]
    rw [logDeriv_Gammaℝ hn2]
    norm_num only [show (2 : ℂ) / 2 = 1 by norm_num, digamma_one]
    rw [← Complex.ofReal_log pi_pos.le]
    push_cast
    ring

/-- P0014 page 33, display 4.9. For even chi, adding one over s removes the gamma
factor logarithmic derivative pole at zero. -/
theorem gammaFactor_regular_even {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even) :
    Tendsto (fun s : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) s + 1 / s)
      (𝓝[≠] 0) (𝓝 (((-(Real.log π + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ))) := by
  have hGamma : AnalyticAt ℂ Complex.Gamma 1 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (0 : ℝ) < (1 : ℂ).re)] with s hs
    apply Complex.differentiableAt_Gamma s
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hh
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hpsi : ContinuousAt digamma 1 :=
    (hGamma.deriv.div hGamma (by rw [Complex.Gamma_one]; exact one_ne_zero)).continuousAt
  have harg : Tendsto (fun s : ℂ => s / 2 + 1) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun s : ℂ => s / 2 + 1) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℂ))).tendsto
  have hlim := ((hpsi.tendsto.comp harg).div_const (2 : ℂ)).const_add
    (-(Complex.log (π : ℂ)) / 2)
  have hv : -(Complex.log (π : ℂ)) / 2 + digamma 1 / 2 =
      (((-(Real.log π + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ)) := by
    rw [digamma_one, ← Complex.ofReal_log pi_pos.le]
    push_cast
    ring
  have hlim' : Tendsto (fun s : ℂ => -(Complex.log (π : ℂ)) / 2 + digamma (s / 2 + 1) / 2)
      (𝓝 0) (𝓝 (((-(Real.log π + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ))) := by
    simpa only [hv, Function.comp_apply] using! hlim
  refine (hlim'.mono_left nhdsWithin_le_nhds).congr' ?_
  have hsmall : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -1 / 2 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hs hsr
  change s ≠ 0 at hs
  have hn : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · apply hs
      simpa using hm
    · have hh := congrArg Complex.re hm
      simp only [div_ofNat_re, neg_re, natCast_re] at hh
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
      linarith
  have hg : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
  rw [hg, logDeriv_Gammaℝ hn, digamma_apply_add_one (s / 2) hn]
  field_simp
  <;> ring

/-- P0014 page 33, display 4.9. For odd chi the gamma logarithmic derivative is
regular at zero with the stated constant value. -/
theorem gammaFactor_regular_odd {q : ℕ} (χ : DirichletCharacter ℂ q) (ho : χ.Odd) :
    Tendsto (fun s : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) s)
      (𝓝[≠] 0)
      (𝓝 (((-(Real.log π + 2 * Real.log 2 + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ))) := by
  have h0 : DirichletCharacter.gammaFactor χ 0 ≠ 0 := by
    rw [ho.gammaFactor_def]
    simp only [zero_add]
    exact Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hne : ∀ᶠ s in 𝓝 (0 : ℂ), DirichletCharacter.gammaFactor χ s ≠ 0 :=
    (gf_diff_of_ne χ h0).continuousAt.tendsto.eventually (isOpen_ne.mem_nhds h0)
  have ha : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hne] with s hs
    exact gf_diff_of_ne χ hs
  have hc : ContinuousAt (logDeriv (DirichletCharacter.gammaFactor χ)) 0 :=
    (ha.deriv.div ha h0).continuousAt
  have hv : logDeriv (DirichletCharacter.gammaFactor χ) 0 =
      (((-(Real.log π + 2 * Real.log 2 + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ)) := by
    have hn : ∀ m : ℕ, (1 : ℂ) / 2 ≠ -m := by
      intro m hm
      have h := congrArg Complex.re hm
      norm_num at h
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    have hg : DirichletCharacter.gammaFactor χ = Gammaℝ ∘ (fun s : ℂ => s + 1) :=
      funext ho.gammaFactor_def
    have hd : DifferentiableAt ℂ Gammaℝ ((0 : ℂ) + 1) := by
      convert (differentiable_Gammaℝ_inv ((0 : ℂ) + 1)).inv
        (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num))) using 1
      funext z
      simp only [Pi.inv_apply, inv_inv]
    have hlin : deriv (fun s : ℂ => s + 1) 0 = 1 := by
      simpa only [id_eq] using ((hasDerivAt_id (0 : ℂ)).add_const 1).deriv
    rw [hg, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + 1) hd
        ((differentiableAt_id (x := (0 : ℂ))).add_const 1),
      hlin]
    simp only [zero_add, mul_one]
    have hlog2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      simpa using (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [logDeriv_Gammaℝ hn, digamma_one_half,
      ← Complex.ofReal_log pi_pos.le, hlog2]
    push_cast
    ring
  simpa only [hv] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- P0014 page 33, displays 4.8 and 4.9. After subtracting the parity pole, the
logarithmic derivative tends to the corrected constant term with the inverse character. -/
theorem logDeriv_regular_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    Tendsto (fun s : ℂ => logDeriv (DirichletCharacter.LFunction χ) s -
      (if χ.Even then 1 / s else 0)) (𝓝[≠] 0)
      (𝓝 ((((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ)) -
        (starRingEnd ℂ) (logDeriv (DirichletCharacter.LFunction χ) 1))) := by
  have hn : χ ≠ 1 := ne_one_of_primitive hχ hq
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hn
  have hC := DirichletCharacter.differentiable_completedLFunction hn
  have hCi := DirichletCharacter.differentiable_completedLFunction hi
  have hC0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    completed_ne_zero_of_re_nonpos hχ (by norm_num) (Or.inr hn)
  have hCa := hC.analyticAt 0
  have hCc : ContinuousAt (logDeriv (DirichletCharacter.completedLFunction χ)) 0 :=
    (hCa.deriv.div hCa hC0).continuousAt
  have hCne : ∀ᶠ s in 𝓝 (0 : ℂ), DirichletCharacter.completedLFunction χ s ≠ 0 :=
    hCa.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds hC0)
  have hquot (ψ : DirichletCharacter ℂ q) :
      DirichletCharacter.LFunction ψ =
        DirichletCharacter.completedLFunction ψ / DirichletCharacter.gammaFactor ψ :=
    funext fun s => DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inr hq)
  have hlocal : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      logDeriv (DirichletCharacter.LFunction χ) s =
        logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.gammaFactor χ) s := by
    have hsmall : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -1 / 2 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      hCne.filter_mono nhdsWithin_le_nhds] with s hs hsr hcs
    change s ≠ 0 at hs
    have hgf := gf_ne_zero_left χ hsr.le hs
    calc
      logDeriv (DirichletCharacter.LFunction χ) s =
          logDeriv (DirichletCharacter.completedLFunction χ /
            DirichletCharacter.gammaFactor χ) s := congrArg (fun f => logDeriv f s) (hquot χ)
      _ = _ := logDeriv_div s hcs hgf (hC s) (gf_diff_of_ne χ hgf)
  have hgammalim : Tendsto (fun s : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) s +
      (if χ.Even then 1 / s else 0)) (𝓝[≠] 0)
      (𝓝 (if χ.Even then
        (((-(Real.log π + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ)) else
        (((-(Real.log π + 2 * Real.log 2 + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ)))) := by
    by_cases he : χ.Even
    · simpa only [if_pos he] using gammaFactor_regular_even χ he
    · have ho := χ.even_or_odd.resolve_left he
      simpa only [if_neg he, add_zero] using gammaFactor_regular_odd χ ho
  have hg1 : DirichletCharacter.gammaFactor χ⁻¹ 1 ≠ 0 :=
    gf_ne_zero_of_re_pos χ⁻¹ (by norm_num)
  have hCi1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 := by
    rw [completed_eq_L_mul_gf χ⁻¹ (Or.inr hq) hg1]
    exact mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl hi) (by norm_num)) hg1
  have hcompleted1 : logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 1 =
      logDeriv (DirichletCharacter.LFunction χ⁻¹) 1 +
        logDeriv (DirichletCharacter.gammaFactor χ⁻¹) 1 := by
    have hdiv : logDeriv (DirichletCharacter.LFunction χ⁻¹) 1 =
        logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 1 -
          logDeriv (DirichletCharacter.gammaFactor χ⁻¹) 1 := by
      calc
        logDeriv (DirichletCharacter.LFunction χ⁻¹) 1 =
            logDeriv (DirichletCharacter.completedLFunction χ⁻¹ /
              DirichletCharacter.gammaFactor χ⁻¹) 1 :=
          congrArg (fun f => logDeriv f 1) (hquot χ⁻¹)
        _ = _ := logDeriv_div 1 hCi1 hg1 (hCi 1) (gf_diff_of_ne χ⁻¹ hg1)
    linear_combination -hdiv
  have heiff : (χ⁻¹).Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one]
  have hgamma1 := gammaFactor_logDeriv_one χ⁻¹
  simp only [heiff] at hgamma1
  have hconj : logDeriv (DirichletCharacter.LFunction χ⁻¹) 1 =
      (starRingEnd ℂ) (logDeriv (DirichletCharacter.LFunction χ) 1) :=
    Conjugate669.logDeriv_inv_one χ hn
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlog : Real.log (2 * π / q) = Real.log 2 + Real.log π - Real.log q := by
    rw [Real.log_div (by positivity) hqpos.ne', Real.log_mul (by norm_num) pi_ne_zero]
  have hv : logDeriv (DirichletCharacter.completedLFunction χ) 0 -
      (if χ.Even then (((-(Real.log π + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ)) else
        (((-(Real.log π + 2 * Real.log 2 + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ))) =
      (((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ)) -
        (starRingEnd ℂ) (logDeriv (DirichletCharacter.LFunction χ) 1) := by
    rw [completed_logDeriv_zero χ hχ hq, hcompleted1, hgamma1, hconj, hlog]
    split_ifs <;> push_cast <;> ring
  have hlim := (hCc.tendsto.mono_left nhdsWithin_le_nhds).sub hgammalim
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [hlocal] with s hs
  rw [hs]
  ring

end LeanLab.HelfgottMajor.LogResidue669
