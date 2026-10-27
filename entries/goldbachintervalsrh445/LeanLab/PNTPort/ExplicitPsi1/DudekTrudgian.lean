module

public import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4
public import LeanLab.PNTPort.ExplicitPsi1.Nontrivial
public import LeanLab.Dudek2014.SigmaTrudgianDownstream
public import LeanLab.RamareSaouter2003.Theorem1Lemma4

/-!
# Dudek 2014 Theorem 2 from RH, Trudgian's `N(T)` bound and Schoenfeld, with Lemma 4 proved

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6552. AI wrote this file. Known mathematics.

`Dudek2014/SigmaTrudgian.lean`, CLOUD 20261020T1415Z-cloud44, proves the page 5 bound `SigmaBd`
for the zero sum `Zr γ y = Re Σᵢ y^{ρᵢ+1}/(ρᵢ(ρᵢ + 1))`, `ρᵢ = 1/2 + iγᵢ`, of any ordinate family
`γ` satisfying Trudgian's `N(T)` bound `TrudgianN70 γ`. Here `γ` is the family of the nontrivial
zeros of ζ with multiplicity, `gZ`, indexed by `Σ ρ : Zall, Fin m(ρ)`, and under RH
`Zr gZ = Zreal`, the zero sum of `DudekLemma4.lean`: `Zr_eq_Zreal`. So

* `theorem2_of_RH_trudgian`: under RH, a prime in `(x - (4/π)√x log x, x]` for every `x ≥ 2`,
  CONDITIONAL ON Trudgian 2014's `N(T)` bound for the zeros and Schoenfeld 1976's `ψ - θ` bounds;
* `RamareSaouter2003.theorem1_of_RH_trudgian`: Ramaré-Saouter 2003 Theorem 1 on the same inputs.
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

/-- **Dudek 2014 Theorem 2 under RH**, CONDITIONAL ON Trudgian's `N(T)` bound for the nontrivial
zeros and Schoenfeld's `ψ - θ` bounds; Lemma 4 and the page 5 bound are proved. -/
theorem theorem2_of_RH_trudgian (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x := by
  apply theorem2_of_sigmaBd _ hSch
  have hS := LeanLab.Dudek2014.SigmaT.sigmaBd_of_trudgian hN
  intro x hx
  obtain ⟨h0, h1⟩ := LeanLab.Dudek2014.Section22.hD_small hx
  have := hS x hx
  simp only at this ⊢
  rwa [Zr_eq_Zreal hRH (by linarith), Zr_eq_Zreal hRH (by linarith),
    Zr_eq_Zreal hRH (by linarith)] at this

end LeanLab.PNTPort.ExplicitPsi1.Trivial

namespace LeanLab.RamareSaouter2003

/-- **Ramaré-Saouter 2003 Theorem 1 under RH**, CONDITIONAL ON Trudgian's `N(T)` bound for the
nontrivial zeros and Schoenfeld's `ψ - θ` bounds. -/
theorem theorem1_of_RH_trudgian (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x :=
  theorem1_of_dudek (LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_trudgian hRH hN hSch)

end LeanLab.RamareSaouter2003
