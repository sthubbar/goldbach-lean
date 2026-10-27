module

public import LeanLab.PNTPort.ExplicitPsi1.PsiSchoenfeldLarge
public import LeanLab.ChebyshevExplicit.Psi30Upper

/-!
# `|θ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^11`, under RH

I-5250, unit U-6659, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics.

* `psiF_eq_psi`: the Dudek file's `psiF` is Mathlib's `Chebyshev.psi`;
* `psi_le_real`: `ψ(y) ≤ 1.1062 y + 2 log² y + 160` for `y ≥ 1`, from cloud27's `psi_le_11062`;
* `psi_sub_theta_large`: `ψ(x) - θ(x) ≤ 1.2 √x` for `x ≥ 10^11`, from Mathlib's
  `ψ - θ ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`, no cited input;
* `theta_schoenfeld_large`: `|θ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^11`, from
  `psi_schoenfeld_large_slack`, under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`.
This is Schoenfeld 1976 Corollary 1, cited in the lab as `ChirreHagen2025.SchoenfeldTheta` and
`DERZ1997.SchoenfeldCor1` for `x ≥ 599`, on the range `x ≥ 10^11`. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real Chebyshev
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)

lemma psiF_eq_psi (x : ℝ) : psiF x = ψ x := by
  rw [psi_eq_sum_Icc]; unfold psiF; rfl

lemma psi_le_real {y : ℝ} (hy : 1 ≤ y) : ψ y ≤ 1.1062 * y + 2 * log y ^ 2 + 160 := by
  rw [psi_eq_psi_coe_floor]
  have h := LeanLab.ChebyshevExplicit.psi_le_11062 ⌊y⌋₊
  have hf : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hf1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.floor_eq_zero] at h0; linarith)
  have hl : log ⌊y⌋₊ ≤ log y := Real.log_le_log (by linarith) hf
  have hl0 : 0 ≤ log (⌊y⌋₊ : ℝ) := Real.log_nonneg hf1
  have : log (⌊y⌋₊ : ℝ) ^ 2 ≤ log y ^ 2 := by gcongr
  linarith

/-- **`ψ(x) - θ(x) ≤ 1.2 √x` for `x ≥ 10^11`**, no cited input. -/
theorem psi_sub_theta_large {x : ℝ} (hx : 10 ^ 11 ≤ x) : ψ x - θ x ≤ 1.2 * √x := by
  obtain ⟨hs1, hL, hL2, -, -, hLs⟩ := large_facts hx
  have hx0 : 0 < x := by linarith
  set s := √x with hsdef
  set L := log x
  have hs0 : 0 < s := by linarith
  have hb := psi_sub_theta_le_psi_add_psi_add_psi x
  have e2 : x ^ (2 : ℝ)⁻¹ = s := by rw [hsdef, Real.sqrt_eq_rpow]; norm_num
  -- x^{1/3} and x^{1/5} are at most s/68
  have hx3 : x ^ (3 : ℝ)⁻¹ ≤ s / 68 := by
    have e : x ^ (3 : ℝ)⁻¹ * x ^ (6 : ℝ)⁻¹ = s := by
      rw [← Real.rpow_add hx0, hsdef, Real.sqrt_eq_rpow]; norm_num
    have h6 : 68 ≤ x ^ (6 : ℝ)⁻¹ := by
      have : (68 : ℝ) = (68 ^ (6 : ℝ)) ^ (6 : ℝ)⁻¹ := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      have : (68 : ℝ) ^ (6 : ℝ) = 68 ^ 6 := by norm_cast
      rw [this]; norm_num; linarith
    have hp : 0 ≤ x ^ (3 : ℝ)⁻¹ := Real.rpow_nonneg hx0.le _
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hx5 : x ^ (5 : ℝ)⁻¹ ≤ x ^ (3 : ℝ)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h1x3 : 1 ≤ x ^ (5 : ℝ)⁻¹ := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog3 : log (x ^ (3 : ℝ)⁻¹) ≤ L := by
    rw [Real.log_rpow hx0]; have : 0 < L := by linarith
    nlinarith
  have hlog5 : log (x ^ (5 : ℝ)⁻¹) ≤ L := by
    rw [Real.log_rpow hx0]; have : 0 < L := by linarith
    nlinarith
  have hlogs : log s ≤ L := by rw [hLs]; have : 0 ≤ log s := Real.log_nonneg (by linarith); linarith
  have p2 := psi_le_real (y := s) (by linarith)
  have p3 := psi_le_real (y := x ^ (3 : ℝ)⁻¹) (by linarith)
  have p5 := psi_le_real (y := x ^ (5 : ℝ)⁻¹) h1x3
  have q3 : log (x ^ (3 : ℝ)⁻¹) ^ 2 = L ^ 2 / 9 := by rw [Real.log_rpow hx0]; ring
  have q5 : log (x ^ (5 : ℝ)⁻¹) ^ 2 = L ^ 2 / 25 := by rw [Real.log_rpow hx0]; ring
  have qs : log s ^ 2 = L ^ 2 / 4 := by
    have : log s = L / 2 := by linarith
    rw [this]; ring
  rw [e2] at hb
  linarith

set_option maxHeartbeats 1000000 in
/-- **`|θ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^11`**, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14` and `Ordinates14` for the zeros. -/
theorem theta_schoenfeld_large (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 10 ^ 11 ≤ x) :
    |θ x - x| ≤ √x * log x ^ 2 / (8 * π) := by
  have h1 := psi_schoenfeld_large_slack hRH hN hH h14 hx
  rw [psiF_eq_psi] at h1
  have h2 := psi_sub_theta_large hx
  have h3 := theta_le_psi x
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- `ChirreHagen2025.SchoenfeldTheta` and `DERZ1997.SchoenfeldCor1` on `x ≥ 10^11`. -/
theorem schoenfeldTheta_from_large (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ u : ℝ, 10 ^ 11 ≤ u → |θ u - u| ≤ √u * Real.log u ^ 2 / (8 * π) :=
  fun _ hu => theta_schoenfeld_large hRH hN hH h14 hu

end LeanLab.PNTPort.ExplicitPsi1.Trivial
