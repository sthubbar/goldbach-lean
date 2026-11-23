module

public import LeanLab.PNTPort.ExplicitPsi1.FirstDiffHSW
public import LeanLab.PNTPort.ExplicitPsi1.PsiUnsmooth

/-!
# An explicit RH bound for `ψ` of Schoenfeld's shape, general form

I-5250, unit U-6657, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics,
Schoenfeld's method of one unsmoothing.

Under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` counts and `Ordinates14`, for any
`h > 0` and `T ≥ 70`, with `c = log 2π`, `S₁, S₂` of FirstDiffHSW.lean:
* `psi_upper_gen`: `ψ(x) ≤ x + h/2 - c + 4.786/h + (x + h)^{1/2} S₁(T) + 2 (x + h)^{3/2} S₂(T)/h`;
* `psi_lower_gen`: `ψ(x) ≥ x - h/2 - c - 4.786/h - x^{1/2} S₁(T) - 2 x^{3/2} S₂(T)/h`, `x - h > 1`.
With `h ≈ √x log x/π` and `T ≈ 2π √x/log x` the right sides are `x ± √x log² x/(8π)` plus
lower order terms. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14 S1 S2 zdiff_le)

/-- `|Z(y + h) - Z(y)| ≤ h (y + h)^{1/2} S₁(T) + 2 (y + h)^{3/2} S₂(T)` under RH. -/
lemma zreal_diff (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {y h T : ℝ} (hy : 0 < y) (hh : 0 ≤ h) (hT : 70 ≤ T) :
    |Zreal (y + h) - Zreal y| ≤ h * (y + h) ^ (1 / 2 : ℝ) * S1 T + 2 * (y + h) ^ (3 / 2 : ℝ) * S2 T := by
  rw [← Zr_eq_Zreal hRH (by linarith), ← Zr_eq_Zreal hRH hy]
  unfold LeanLab.Dudek2014.SigmaT.Zr
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (zdiff_le hN hH h14 hy hh hT)

/-- `ψ₁(y) = y²/2 - y c - Z(y) + D(y)` with `|D(y)| ≤ 2.393`, for `y > 1`. -/
lemma psi1_split {y : ℝ} (hy : 1 < y) :
    |psi1 y - (y ^ 2 / 2 - y * Real.log (2 * π) - Zreal y)| ≤ 2.393 := by
  rw [psi1_formula hy]
  have := error_bound hy
  have e : y ^ 2 / 2 - y * Real.log (2 * π) - Zreal y + (deriv riemannZeta (-1) / riemannZeta (-1)).re -
      y * ∑' n, tb y n - (y ^ 2 / 2 - y * Real.log (2 * π) - Zreal y) =
      (deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n := by ring
  rw [e]; exact this

/-- **Upper bound for `ψ(x)`**, under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem psi_upper_gen (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x h T : ℝ} (hx : 1 < x) (hh : 0 < h) (hT : 70 ≤ T) :
    psiF x ≤ x + h / 2 - Real.log (2 * π) + 4.786 / h + (x + h) ^ (1 / 2 : ℝ) * S1 T +
      2 * (x + h) ^ (3 / 2 : ℝ) * S2 T / h := by
  obtain ⟨u1, -⟩ := psi1_diff_bounds (by linarith : (0 : ℝ) ≤ x) hh
  have a1 := abs_le.1 (psi1_split (by linarith : 1 < x + h))
  have a0 := abs_le.1 (psi1_split hx)
  have z := abs_le.1 (zreal_diff hRH hN hH h14 (by linarith : (0 : ℝ) < x) hh.le hT)
  have key : h * psiF x ≤ h * (x + h / 2 - Real.log (2 * π) + 4.786 / h + (x + h) ^ (1 / 2 : ℝ) * S1 T +
      2 * (x + h) ^ (3 / 2 : ℝ) * S2 T / h) := by
    have e : h * (x + h / 2 - Real.log (2 * π) + 4.786 / h + (x + h) ^ (1 / 2 : ℝ) * S1 T +
        2 * (x + h) ^ (3 / 2 : ℝ) * S2 T / h) = x * h + h ^ 2 / 2 - h * Real.log (2 * π) + 4.786 +
        (h * (x + h) ^ (1 / 2 : ℝ) * S1 T + 2 * (x + h) ^ (3 / 2 : ℝ) * S2 T) := by
      field_simp; ring
    rw [e]
    have e2 : (x + h) ^ 2 / 2 - (x + h) * Real.log (2 * π) = x ^ 2 / 2 - x * Real.log (2 * π) + (x * h + h ^ 2 / 2 - h * Real.log (2 * π)) := by ring
    linarith
  exact le_of_mul_le_mul_left key hh

/-- **Lower bound for `ψ(x)`**, under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem psi_lower_gen (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x h T : ℝ} (hx : 1 < x - h) (hh : 0 < h) (hT : 70 ≤ T) :
    x - h / 2 - Real.log (2 * π) - 4.786 / h - x ^ (1 / 2 : ℝ) * S1 T -
      2 * x ^ (3 / 2 : ℝ) * S2 T / h ≤ psiF x := by
  obtain ⟨-, u2⟩ := psi1_diff_bounds (by linarith : (0 : ℝ) ≤ x - h) hh
  rw [sub_add_cancel] at u2
  have a1 := abs_le.1 (psi1_split (by linarith : 1 < x))
  have a0 := abs_le.1 (psi1_split hx)
  have z := abs_le.1 (zreal_diff hRH hN hH h14 (by linarith : (0 : ℝ) < x - h) hh.le hT)
  rw [sub_add_cancel] at z
  have key : h * (x - h / 2 - Real.log (2 * π) - 4.786 / h - x ^ (1 / 2 : ℝ) * S1 T -
      2 * x ^ (3 / 2 : ℝ) * S2 T / h) ≤ h * psiF x := by
    have e : h * (x - h / 2 - Real.log (2 * π) - 4.786 / h - x ^ (1 / 2 : ℝ) * S1 T -
        2 * x ^ (3 / 2 : ℝ) * S2 T / h) = x * h - h ^ 2 / 2 - h * Real.log (2 * π) - 4.786 -
        (h * x ^ (1 / 2 : ℝ) * S1 T + 2 * x ^ (3 / 2 : ℝ) * S2 T) := by
      field_simp; ring
    rw [e]
    have e2 : (x - h) ^ 2 / 2 - (x - h) * Real.log (2 * π) = x ^ 2 / 2 - x * Real.log (2 * π) - (x * h - h ^ 2 / 2 - h * Real.log (2 * π)) := by ring
    linarith
  exact le_of_mul_le_mul_left key hh

end LeanLab.PNTPort.ExplicitPsi1.Trivial
