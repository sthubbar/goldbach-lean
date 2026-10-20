module

public import LeanLab.PNTPort.ZetaZeros.SmallT
public import LeanLab.PNTPort.StrongPNT.ZetaConj

/-!
# Under RH, `ζ'/ζ` on a vertical line just right of `1/2`

Lab proof, unit U-5266, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
CONDITIONAL ON Mathlib's `RiemannHypothesis` as a hypothesis, no other input.

`logDeriv_vline_RH`: an absolute `C` such that for `1/2 < σ ≤ 3/4` and every real `t`,
`ζ(σ + it) ≠ 0` and `‖ζ'/ζ(σ + it)‖ ≤ C log(|t| + 5) (1 + 1/(σ - 1/2))`. At `σ = 1/2 + 1/log X`
this is `≪ log(|t| + 5) log X`, the bound a contour at that abscissa needs for
`RH ⇒ ψ(X) = X + O(√X log³ X)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology ComplexConjugate

local notation "ζ" => riemannZeta

lemma rh_re {ρ : ℂ} (hRH : RiemannHypothesis) (hz : ζ ρ = 0) (hre : 0 < ρ.re) :
    ρ.re = 1 / 2 := by
  have h1 : ρ ≠ 1 := by
    intro h; rw [h] at hz; exact riemannZeta_one_ne_zero hz
  refine hRH ρ hz ?_ h1
  rintro ⟨n, rfl⟩
  simp at hre
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Under RH**, the vertical line `Re s = σ`, `1/2 < σ ≤ 3/4`. -/
theorem logDeriv_vline_RH (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 / 2 < σ →
    σ ≤ 3 / 4 → ∀ t : ℝ, ζ (σ + t * I) ≠ 0 ∧
      ‖deriv ζ (σ + t * I) / ζ (σ + t * I)‖ ≤
        C * Real.log (|t| + 5) * (1 + 1 / (σ - 1 / 2)) := by
  obtain ⟨C1, hC1, hbig⟩ := logDeriv_bound_RH hRH
  obtain ⟨K, hK, hsmall⟩ := logDeriv_small
  have hl5 : 1 < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  refine ⟨C1 + K + 4, by positivity, fun σ hσ1 hσ2 t => ?_⟩
  have hd : 0 < σ - 1 / 2 := by linarith
  have hinv : 0 ≤ 1 / (σ - 1 / 2) := by positivity
  have hlog5 : Real.log 5 ≤ Real.log (|t| + 5) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog0 : 0 ≤ Real.log (|t| + 5) := by linarith
  -- the large positive case, also used for negative `t` by conjugation
  have big : ∀ u : ℝ, 5 ≤ u → ζ (σ + u * I) ≠ 0 ∧
      ‖deriv ζ (σ + u * I) / ζ (σ + u * I)‖ ≤ (C1 + K + 4) * Real.log (u + 5) *
        (1 + 1 / (σ - 1 / 2)) := by
    intro u hu
    obtain ⟨hne, hb⟩ := hbig u hu σ hσ1 (by linarith)
    have e : (σ : ℂ) + I * u = σ + u * I := by ring
    rw [e] at hne hb
    refine ⟨hne, hb.trans ?_⟩
    have hlu : Real.log u ≤ Real.log (u + 5) := Real.log_le_log (by linarith) (by linarith)
    have hlu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ 1 + 1 / (σ - 1 / 2) := by linarith
    calc C1 * Real.log u * (1 + 1 / (σ - 1 / 2))
        ≤ C1 * Real.log (u + 5) * (1 + 1 / (σ - 1 / 2)) := by gcongr
      _ ≤ (C1 + K + 4) * Real.log (u + 5) * (1 + 1 / (σ - 1 / 2)) := by
          gcongr <;> linarith
  rcases le_or_gt 5 t with ht | ht
  · rw [abs_of_nonneg (by linarith)]; exact big t ht
  rcases le_or_gt t (-5) with ht' | ht'
  · obtain ⟨hne, hb⟩ := big (-t) (by linarith)
    have hconj : (σ : ℂ) + t * I = conj ((σ : ℂ) + (-t : ℝ) * I) := by
      simp [Complex.ext_iff]
    rw [abs_of_neg (by linarith), hconj]
    refine ⟨?_, ?_⟩
    · rw [riemannZeta_conj]; exact (map_ne_zero _).mpr hne
    · have := logDerivZeta_conj ((σ : ℂ) + (-t : ℝ) * I)
      simp only [Pi.div_apply] at this
      rw [this, Complex.norm_conj]; exact hb
  -- `|t| < 5`
  have hts : |t| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hfin, hcount, hloc⟩ := hsmall t hts
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; linarith
  have hsc : ‖s - cen t‖ ≤ 1 := by
    have e : s - cen t = ((σ - 3 / 2 : ℝ) : ℂ) := by simp only [hs, cen]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hzs : ζ s ≠ 0 := by
    intro hz
    have := rh_re hRH hz (by rw [hsre]; linarith)
    rw [hsre] at this; linarith
  refine ⟨hzs, ?_⟩
  have hb := hloc s hsc hs1 hzs
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤ (analyticOrderNatAt ζ ρ : ℝ) / (σ - 1 / 2) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hre0 : 0 < ρ.re := by
      have h1 := Complex.abs_re_le_norm (ρ - cen t)
      have e : (ρ - cen t).re = ρ.re - 3 / 2 := by simp [cen]
      rw [e] at h1
      have := hρ.2.2
      rw [abs_le] at h1; linarith [h1.1]
    have hρre := rh_re hRH hρ.1 hre0
    have hn : σ - 1 / 2 ≤ ‖s - ρ‖ := by
      have : |(s - ρ).re| ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
      have e2 : (s - ρ).re = σ - 1 / 2 := by simp [hsre, hρre]
      rw [e2, abs_of_pos hd] at this; exact this
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hn
  have hsum : ‖∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤
      K / (σ - 1 / 2) := by
    calc _ ≤ ∑ ρ ∈ hfin.toFinset, ‖(analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ) / (σ - 1 / 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) / (σ - 1 / 2) := by
          rw [Finset.sum_div]
      _ ≤ K / (σ - 1 / 2) := div_le_div_of_nonneg_right hcount hd.le
  have hpole : ‖1 / (s - 1)‖ ≤ 4 := by
    have : 1 / 4 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      have e : (s - 1).re = σ - 1 := by simp [hsre]
      rw [e, abs_of_neg (by linarith)] at h; linarith
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have htri : ‖deriv ζ s / ζ s‖ ≤ K + 4 + K / (σ - 1 / 2) := by
    have e : deriv ζ s / ζ s = (deriv ζ s / ζ s + 1 / (s - 1) -
        ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)) - 1 / (s - 1) +
        ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ) := by ring
    rw [e]
    calc _ ≤ ‖(deriv ζ s / ζ s + 1 / (s - 1) -
          ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)) - 1 / (s - 1)‖ +
          ‖∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ := norm_add_le _ _
      _ ≤ (K + 4) + K / (σ - 1 / 2) := by
          gcongr
          exact (norm_sub_le _ _).trans (by linarith)
  have hKd : K / (σ - 1 / 2) = K * (1 / (σ - 1 / 2)) := by ring
  calc ‖deriv ζ s / ζ s‖ ≤ K + 4 + K / (σ - 1 / 2) := htri
    _ ≤ (C1 + K + 4) * 1 * (1 + 1 / (σ - 1 / 2)) := by rw [hKd]; nlinarith
    _ ≤ (C1 + K + 4) * Real.log (|t| + 5) * (1 + 1 / (σ - 1 / 2)) := by
        gcongr <;> linarith

end LeanLab.PNTPort.ZetaZeros

