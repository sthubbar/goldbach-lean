module

public import LeanLab.Perelli1996.Principal320
public import LeanLab.Perelli1996.Ramanujan103

/-!
Perelli 1996, page 481 equation 2 and page 486 equation 27.
The full principal coefficient and the reciprocal kernel tail give a central arc estimate.
The inclusive zero endpoint contributes one unit.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.PrincipalTail320
open Finset MeasureTheory
noncomputable section

/-- The principal coefficient over the centered full period still equals m plus one.
Pages 481 and 486, the inclusive zero endpoint variant of the principal extraction. -/
theorem centered_coefficient (M m : ℕ) (hm : m ≤ M) :
    (∫ α in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) = (m + 1 : ℂ) := by
  have hT (α : ℝ) : Kernel.T 0 (M + 1) (α + 1) = Kernel.T 0 (M + 1) α := by
    unfold Kernel.T
    apply Finset.sum_congr rfl
    intro n hn
    simp only [zero_add]
    rw [mul_add, mul_one, Parseval103.e_add, Ramanujan103.e_nat, mul_one]
  have he (α : ℝ) : Kernel.e (-(m : ℝ) * (α + 1)) = Kernel.e (-(m : ℝ) * α) := by
    rw [mul_add, mul_one, Parseval103.e_add, ← Parseval103.conj_e (m : ℝ), Ramanujan103.e_nat]
    simp
  have hper : Function.Periodic
      (fun α : ℝ => Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) 1 := by
    intro α
    dsimp only
    rw [hT, he]
  have h := hper.intervalIntegral_add_eq (-1 / 2) 0
  norm_num only [zero_add, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
  rw [neg_div, h, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  exact Principal320.full_coefficient M m hm

/-- Removing the two geometric kernel tails costs at most one over twice the radius.
Pages 481 and 486, principal extraction with the explicit one unit endpoint error. -/
theorem central_coefficient_error (M m : ℕ) (hm : m ≤ M) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    ‖(∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) - (m : ℂ)‖ ≤
      1 + 1 / (2 * δ) := by
  let f : ℝ → ℂ := fun α => Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)
  have hcont : Continuous f := by dsimp [f]; unfold Kernel.T Kernel.e; fun_prop
  have hnorm (α : ℝ) : ‖f α‖ = ‖Kernel.T 0 (M + 1) α‖ ^ 2 := by
    dsimp [f]
    rw [norm_mul, norm_pow]
    simp [Kernel.e, Complex.norm_exp]
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (-1 / 2) (-δ)) (hcont.intervalIntegrable (-δ) δ)
  have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (-1 / 2) δ) (hcont.intervalIntegrable δ (1 / 2))
  have hs : ((∫ α in (-1 / 2 : ℝ)..(-δ), f α) + ∫ α in (-δ)..δ, f α) +
      (∫ α in δ..(1 / 2 : ℝ), f α) = (m + 1 : ℂ) := by
    rw [h12, h23]
    exact centered_coefficient M m hm
  have heq : (∫ α in (-δ)..δ, f α) - (m : ℂ) =
      1 - ((∫ α in (-1 / 2 : ℝ)..(-δ), f α) + ∫ α in δ..(1 / 2 : ℝ), f α) := by
    linear_combination hs
  have hl := intervalIntegral.norm_integral_le_integral_norm
    (f := f) (μ := volume) (by linarith : (-1 / 2 : ℝ) ≤ -δ)
  have hr := intervalIntegral.norm_integral_le_integral_norm
    (f := f) (μ := volume) hhalf
  simp_rw [hnorm] at hl hr
  have htail := Kernel.integral_norm_T_sq_two_tails 0 (M + 1) hδ hhalf
  change ‖(∫ α in (-δ)..δ, f α) - (m : ℂ)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(∫ α in (-1 / 2 : ℝ)..(-δ), f α) +
        ∫ α in δ..(1 / 2 : ℝ), f α‖ := norm_sub_le _ _
    _ ≤ 1 + (‖∫ α in (-1 / 2 : ℝ)..(-δ), f α‖ +
        ‖∫ α in δ..(1 / 2 : ℝ), f α‖) := by
      rw [norm_one]
      have hnormadd := norm_add_le (∫ α in (-1 / 2 : ℝ)..(-δ), f α)
        (∫ α in δ..(1 / 2 : ℝ), f α)
      linarith
    _ ≤ 1 + ((∫ α in (-1 / 2 : ℝ)..(-δ), ‖Kernel.T 0 (M + 1) α‖ ^ 2) +
        ∫ α in δ..(1 / 2 : ℝ), ‖Kernel.T 0 (M + 1) α‖ ^ 2) := by linarith
    _ ≤ _ := by linarith

end
end LeanLab.Perelli1996.PrincipalTail320
