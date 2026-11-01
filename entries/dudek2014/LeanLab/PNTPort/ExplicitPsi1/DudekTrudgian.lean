module

public import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4
public import LeanLab.PNTPort.ExplicitPsi1.Nontrivial
public import LeanLab.Dudek2014.SigmaTrudgian

/-!
# The zero ordinates `gZ` and the zero sum of Dudek's Lemma 4

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6552. AI wrote this file. Known mathematics.

`gZ` is the family of ordinates of the nontrivial zeros of ζ with multiplicity, indexed by
`Σ ρ : Zall, Fin m(ρ)`. `Zr_eq_Zreal`: under RH the ordinate family sum `Zr gZ` of
`Dudek2014/SigmaTrudgian.lean` is the zero sum `Zreal` of `DudekLemma4.lean`.

This entry's copy keeps only these declarations. The lab file also derives Theorem 2 from the
`N(T)` bound of Trudgian 2014, whose constant is reported to be in error, and Schoenfeld's
bounds; that route is not used here and is removed with its imports.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex
open LeanLab.PNTPort.ExplicitPsi1

local notation "ζ" => riemannZeta

/-- The nontrivial zeros of ζ with multiplicity, as an index type. -/
abbrev ZIdx := Σ ρ : Zall, Fin (analyticOrderNatAt ζ (ρ : ℂ))

/-- Their ordinates. -/
noncomputable def gZ (i : ZIdx) : ℝ := ((i.1 : ℂ)).im

lemma re_half_of_RH (hRH : RiemannHypothesis) (ρ : Zall) : (ρ : ℂ).re = 1 / 2 := by
  have h : (ρ : ℂ) ∈ {ρ : ℂ | ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by rw [← Zall_eq]; exact ρ.2
  obtain ⟨hz, h0, h1⟩ := h
  apply hRH _ hz
  · rintro ⟨n, hn⟩
    rw [hn] at h0
    simp at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro h; rw [h] at h1; simp at h1

lemma rhoF_gZ (hRH : RiemannHypothesis) (i : ZIdx) :
    LeanLab.Dudek2014.SigmaT.rhoF (gZ i) = (i.1 : ℂ) := by
  unfold LeanLab.Dudek2014.SigmaT.rhoF gZ
  apply Complex.ext <;> simp [re_half_of_RH hRH i.1]

/-- `y^{ρ+1}/(ρ(ρ + 1))`. -/
noncomputable def gq (y : ℝ) (ρ : ℂ) : ℂ := (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

lemma y_zterm {y : ℝ} (hy : 0 < y) (ρ : ℂ) :
    (y : ℂ) * zterm y ρ = (analyticOrderNatAt ζ ρ : ℂ) * gq y ρ := by
  unfold zterm gq
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_add _ _ hy0, Complex.cpow_one]
  ring

lemma norm_y_zterm {y : ℝ} (hy : 0 < y) (ρ : ℂ) :
    (analyticOrderNatAt ζ ρ : ℝ) * ‖gq y ρ‖ = y * ‖zterm y ρ‖ := by
  have := congr_arg norm (y_zterm hy ρ)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy,
    Complex.norm_natCast] at this
  linarith

/-- **Under RH, the ordinate family sum of `SigmaTrudgian.lean` is the zero sum `Zreal`.** -/
theorem Zr_eq_Zreal (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y) :
    LeanLab.Dudek2014.SigmaT.Zr gZ y = Zreal y := by
  unfold LeanLab.Dudek2014.SigmaT.Zr Zreal
  congr 1
  have hf : ∀ i : ZIdx, LeanLab.Dudek2014.SigmaT.fz (LeanLab.Dudek2014.SigmaT.rhoF (gZ i)) y =
      gq y (i.1 : ℂ) := by
    intro i
    rw [rhoF_gZ hRH i]
    rfl
  simp_rw [hf]
  -- summability over the sigma type
  have hzn : Summable (fun ρ : Zall => ‖zterm y ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => norm_zterm_le hy ρ.2)
      (summable_hw.mul_left (Xb y))
  have hfib : ∀ ρ : Zall, ∑' c : Fin (analyticOrderNatAt ζ (ρ : ℂ)), ‖gq y (ρ : ℂ)‖ =
      y * ‖zterm y ρ‖ := by
    intro ρ
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      norm_y_zterm hy]
  have hsn : Summable (fun i : ZIdx => ‖gq y (i.1 : ℂ)‖) := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun ρ => Summable.of_finite, ?_⟩
    simp_rw [hfib]
    exact hzn.mul_left y
  have hs : Summable (fun i : ZIdx => gq y (i.1 : ℂ)) := hsn.of_norm
  rw [hs.tsum_sigma' (fun ρ => Summable.of_finite), ← tsum_mul_left]
  apply tsum_congr
  intro ρ
  rw [tsum_fintype]
  show ∑ _b : Fin (analyticOrderNatAt ζ (ρ : ℂ)), gq y (ρ : ℂ) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, y_zterm hy]

end LeanLab.PNTPort.ExplicitPsi1.Trivial
