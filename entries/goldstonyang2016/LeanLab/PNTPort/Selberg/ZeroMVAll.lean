module

public import LeanLab.PNTPort.Selberg.Count
public import LeanLab.PNTPort.Gallagher.ZeroMV

/-!
# The zero mean value theorem over all nontrivial zeros

Lab proof, unit U-5920, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input, unconditional.

`zero_mean_value_all`: there is `C` such that for every finite set `S` of nontrivial zeros of
`ζ`, every choice of complex `a ρ` and every centre `U`,

  `∫_ℝ ‖∑_{ρ ∈ S} a ρ e^{i (Im ρ) u}‖² e^{-(u - U)²/2} du ≤ C ∑_{ρ ∈ S} ‖a ρ‖² log(‖ρ‖ + 4)`.

The lab's `Gallagher.zero_mean_value` needs `|Im ρ| ≥ 4`; the lab has no proof that no zero
lies below height `4`, so the low zeros are counted with `sum_mz_low`, at most `30 B` of them
with multiplicity, and each contributes at most `1` to the inner Gaussian sum.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

theorem zero_mean_value_all : ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℂ), (∀ ρ ∈ S, NZ ρ) →
    ∀ (a : ℂ → ℂ) (U : ℝ),
    ∫ u : ℝ, ‖∑ ρ ∈ S, a ρ * cexp (ρ.im * u * I)‖ ^ 2 * gw U u
      ≤ C * ∑ ρ ∈ S, ‖a ρ‖ ^ 2 * Real.log (‖ρ‖ + 4) := by
  obtain ⟨C₁, hC₁, hZ⟩ := gauss_zero_sum
  obtain ⟨B, hB0, hB⟩ := sum_mz_low
  refine ⟨(2 * Real.pi) ^ (1 / 2 : ℝ) * (C₁ + 30 * B), by positivity, fun S hS a U => ?_⟩
  refine (gauss_mean_value S a (fun ρ => ρ.im) U).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  have hL1 := one_le_log_add_four (norm_nonneg j)
  have hLj : Real.log (|j.im| + 4) ≤ Real.log (‖j‖ + 4) :=
    Real.log_le_log (by positivity) (by linarith [abs_im_le_norm j])
  -- the inner sum, split at height 4
  have hin : ∑ k ∈ S, Real.exp (-(j.im - k.im) ^ 2 / 2) ≤ (C₁ + 30 * B) * Real.log (‖j‖ + 4) := by
    rw [← sum_filter_add_sum_filter_not S (fun k => 4 ≤ |k.im|)]
    have h1 : ∑ k ∈ S.filter (fun k => 4 ≤ |k.im|), Real.exp (-(j.im - k.im) ^ 2 / 2)
        ≤ C₁ * Real.log (|j.im| + 4) := by
      refine le_trans ?_ (hZ j.im (S.filter (fun k => 4 ≤ |k.im|)) fun k hk => by
        rw [mem_filter] at hk; exact ⟨(hS k hk.1).1, hk.2⟩)
      refine sum_le_sum fun k hk => ?_
      rw [mem_filter] at hk
      have hk1 : k ≠ 1 := by
        intro h; have := hk.2; rw [h] at this; norm_num at this
      have h1 : (1 : ℝ) ≤ analyticOrderNatAt ζ k := by exact_mod_cast ord_pos (hS k hk.1).1 hk1
      exact le_mul_of_one_le_left (Real.exp_pos _).le h1
    have h2 : ∑ k ∈ S.filter (fun k => ¬ 4 ≤ |k.im|), Real.exp (-(j.im - k.im) ^ 2 / 2)
        ≤ 30 * B := by
      have hlow := hB 4 (by norm_num) (S.filter (fun k => ¬ 4 ≤ |k.im|)) fun k hk => by
        rw [mem_filter] at hk; exact ⟨hS k hk.1, (not_le.mp hk.2).le⟩
      refine le_trans (sum_le_sum fun k hk => ?_) (hlow.trans_eq (by ring))
      rw [mem_filter] at hk
      have hk1 : k ≠ 1 := by
        intro h; have := (hS k hk.1).2.2; rw [h, one_re] at this; exact lt_irrefl _ this
      have h1 : (1 : ℝ) ≤ mz k := by
        unfold mz; exact_mod_cast ord_pos (hS k hk.1).1 hk1
      have : Real.exp (-(j.im - k.im) ^ 2 / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (j.im - k.im)]
      linarith
    have : C₁ * Real.log (|j.im| + 4) ≤ C₁ * Real.log (‖j‖ + 4) := by gcongr
    nlinarith
  calc ‖a j‖ ^ 2 * ∑ k ∈ S, Real.exp (-(j.im - k.im) ^ 2 / 2)
      ≤ ‖a j‖ ^ 2 * ((C₁ + 30 * B) * Real.log (‖j‖ + 4)) := by gcongr
    _ = (C₁ + 30 * B) * (‖a j‖ ^ 2 * Real.log (‖j‖ + 4)) := by ring

end LeanLab.PNTPort.Selberg

