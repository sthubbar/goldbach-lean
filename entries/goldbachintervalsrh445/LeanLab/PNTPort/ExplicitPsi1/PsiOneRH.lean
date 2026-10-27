module

public import LeanLab.PNTPort.ExplicitPsi1.DudekCorollaries

/-!
# An explicit RH bound for `ψ₁`

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6554. AI wrote this file. Known mathematics,
with a crude constant.

Under RH and Trudgian's `N(T)` bound for the zeros, the zero sum is at most `y^{3/2} Σ 1/|ρ(ρ+1)|`,
and `Σ 1/|ρ(ρ+1)| ≤ 128` by cloud44's `split_bound` at `T = 70`. The true sum is about 0.046, so
the constant is far from sharp. Together with `psi1_formula` and `error_bound`:

`psi1_explicit_RH`: `|ψ₁(y) - y²/2 + y log 2π| ≤ 128 y^{3/2} + 2.393` for `y > 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open LeanLab.Dudek2014.SigmaT

/-- `Σ 1/|ρ(ρ+1)| ≤ 128` from Trudgian's `N(T)` bound. -/
lemma tsum_wgt_le {ι : Type*} {γ : ι → ℝ} (hN : TrudgianN70 γ) : ∑' i, wgt γ i ≤ 128 := by
  have hb : ∀ s : Finset ι, ∑ i ∈ s, wgt γ i ≤
      70 * Real.log 70 / Real.pi * (4 / 3) + 1 * (Real.log 70 / (Real.pi * 70)) :=
    fun s => split_bound hN (a := 4 / 3) (b := 1) (le_refl 70) (by norm_num) (by norm_num) (wgt γ)
      (fun i _ => wgt_le γ i) (fun i hi => wgt_le_inv_sq γ (ne_of_large (le_refl 70) hi)) s
  refine ((summable_wgt hN).tsum_le_of_sum_le hb).trans ?_
  have h1 := log_70
  have h0 : 0 ≤ Real.log 70 := Real.log_nonneg (by norm_num)
  have hp := Real.pi_gt_d2
  have e1 : 70 * Real.log 70 / Real.pi * (4 / 3) ≤ 70 * 4.3 / 3.14 * (4 / 3) := by
    gcongr
  have e2 : 1 * (Real.log 70 / (Real.pi * 70)) ≤ 4.3 / (3.14 * 70) := by
    rw [one_mul]; gcongr
  norm_num at e1 e2 ⊢
  linarith

/-- **`|ψ₁(y) - y²/2 + y log 2π| ≤ 128 y^{3/2} + 2.393` for `y > 1`**, under RH, CONDITIONAL ON
Trudgian's `N(T)` bound for the zeros. -/
theorem psi1_explicit_RH (hRH : RiemannHypothesis) (hN : TrudgianN70 gZ) {y : ℝ} (hy : 1 < y) :
    |LeanLab.Dudek2014.Section22.psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))| ≤
      128 * y ^ (3 / 2 : ℝ) + 2.393 := by
  have hy0 : 0 < y := by linarith
  have hZ : |Zreal y| ≤ 128 * y ^ (3 / 2 : ℝ) := by
    rw [← Zr_eq_Zreal hRH hy0]
    unfold Zr
    have hs := summable_fz hN hy0
    have hn : Summable (fun i => ‖fz (rhoF (gZ i)) y‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_fz_le' (gZ i) hy0)
        ((summable_wgt hN).mul_left (y ^ (3 / 2 : ℝ)))
    calc |(∑' i, fz (rhoF (gZ i)) y).re| ≤ ‖∑' i, fz (rhoF (gZ i)) y‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' i, ‖fz (rhoF (gZ i)) y‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' i, y ^ (3 / 2 : ℝ) * wgt gZ i :=
          hn.tsum_le_tsum (fun i => norm_fz_le' (gZ i) hy0) ((summable_wgt hN).mul_left _)
      _ = y ^ (3 / 2 : ℝ) * ∑' i, wgt gZ i := tsum_mul_left
      _ ≤ y ^ (3 / 2 : ℝ) * 128 := by
          gcongr; exact tsum_wgt_le hN
      _ = 128 * y ^ (3 / 2 : ℝ) := by ring
  have hE := error_bound hy
  rw [psi1_formula hy]
  have e : y ^ 2 / 2 - y * Real.log (2 * Real.pi) - Zreal y +
      (deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n -
      (y ^ 2 / 2 - y * Real.log (2 * Real.pi)) =
      -Zreal y + ((deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n) := by ring
  rw [e]
  calc _ ≤ |-Zreal y| + |(deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n| :=
        abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; linarith

end LeanLab.PNTPort.ExplicitPsi1.Trivial
