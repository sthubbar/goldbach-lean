module

public import LeanLab.PNTPort.ExplicitPsi1.PsiOneRH

/-!
# `|ψ₁(y) - y²/2| ≤ 133 y^{3/2}` for `y > 1`, under RH

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6556. AI wrote this file. Known mathematics,
crude constant, from `psi1_explicit_RH`, `log 2π ≤ 2` and `y ≤ y^{3/2}`, `1 ≤ y^{3/2}` for `y ≥ 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

theorem psi1_RH_simple (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 gZ) {y : ℝ} (hy : 1 < y) :
    |LeanLab.Dudek2014.Section22.psi1 y - y ^ 2 / 2| ≤ 133 * y ^ (3 / 2 : ℝ) := by
  have h := psi1_explicit_RH hRH hN hy
  have hy0 : 0 ≤ y := by linarith
  have hl : Real.log (2 * Real.pi) ≤ 2 := LeanLab.PNTPort.ZetaZeros.log_two_pi_le
  have hl0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hp1 : y ≤ y ^ (3 / 2 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one y]
    exact Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)
  have hp0 : 1 ≤ y ^ (3 / 2 : ℝ) := Real.one_le_rpow hy.le (by norm_num)
  have e : LeanLab.Dudek2014.Section22.psi1 y - y ^ 2 / 2 =
      (LeanLab.Dudek2014.Section22.psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))) -
        y * Real.log (2 * Real.pi) := by ring
  rw [e]
  have hyl : y * Real.log (2 * Real.pi) ≤ 2 * y ^ (3 / 2 : ℝ) := by nlinarith
  have hyl0 : 0 ≤ y * Real.log (2 * Real.pi) := mul_nonneg hy0 hl0
  calc _ ≤ |LeanLab.Dudek2014.Section22.psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))| +
        |y * Real.log (2 * Real.pi)| := abs_sub _ _
    _ ≤ (128 * y ^ (3 / 2 : ℝ) + 2.393) + 2 * y ^ (3 / 2 : ℝ) := by
        rw [abs_of_nonneg hyl0]; linarith
    _ ≤ 133 * y ^ (3 / 2 : ℝ) := by linarith

end LeanLab.PNTPort.ExplicitPsi1.Trivial
