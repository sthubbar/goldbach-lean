module

public import LeanLab.PNTPort.Gallagher.GaussMV
public import LeanLab.PNTPort.Gallagher.GaussZeros
public import LeanLab.PNTPort.ZetaZeros.GoodHeight

/-!
# A mean value theorem for sums over zeta zeros

Lab proof, unit U-5861, CLOUD 20261020T0014Z-cloud30, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, Selberg 1943 in Gaussian form, no cited input.

`zero_mean_value`: there is `C` such that for every finite set `S` of zeros of `ζ` with
`|Im ρ| ≥ 4`, every choice of complex `a ρ` and every centre `U`,

  `∫_ℝ ‖∑_{ρ ∈ S} a ρ e^{i (Im ρ) u}‖² e^{-(u - U)²/2} du ≤ C ∑_{ρ ∈ S} ‖a ρ‖² log(|Im ρ| + 4)`.

With `u = log x` and `a ρ` the coefficients of a truncated explicit formula, this is the step
that makes the RH mean square of `ψ` in short intervals `≪ h x log² x` rather than the trivial
bound; `gauss_mean_value` plus `gauss_zero_sum` with `ZetaZeros.ord_pos`, `m(ρ) ≥ 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Gallagher

open Complex Finset
open LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

theorem zero_mean_value : ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℂ), (∀ ρ ∈ S, ζ ρ = 0 ∧ 4 ≤ |ρ.im|) →
    ∀ (a : ℂ → ℂ) (U : ℝ),
    ∫ u : ℝ, ‖∑ ρ ∈ S, a ρ * cexp (ρ.im * u * I)‖ ^ 2 * gw U u
      ≤ C * ∑ ρ ∈ S, ‖a ρ‖ ^ 2 * Real.log (|ρ.im| + 4) := by
  obtain ⟨C₁, hC₁, hZ⟩ := gauss_zero_sum
  refine ⟨(2 * Real.pi) ^ (1 / 2 : ℝ) * C₁, by positivity, fun S hS a U => ?_⟩
  refine (gauss_mean_value S a (fun ρ => ρ.im) U).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  rw [mul_comm C₁, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc ∑ k ∈ S, Real.exp (-(j.im - k.im) ^ 2 / 2)
      ≤ ∑ k ∈ S, (analyticOrderNatAt ζ k : ℝ) * Real.exp (-(j.im - k.im) ^ 2 / 2) := by
        refine sum_le_sum fun k hk => ?_
        have hk1 : k ≠ 1 := by
          intro h; have := (hS k hk).2; rw [h] at this; norm_num at this
        have h1 : (1 : ℝ) ≤ analyticOrderNatAt ζ k := by exact_mod_cast ord_pos (hS k hk).1 hk1
        exact le_mul_of_one_le_left (Real.exp_pos _).le h1
    _ ≤ C₁ * Real.log (|j.im| + 4) := hZ j.im S hS
    _ = Real.log (|j.im| + 4) * C₁ := mul_comm _ _

end LeanLab.PNTPort.Gallagher

