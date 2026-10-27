module

public import LeanLab.HardyLittlewood1923.U1482ZeroCount

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T1603Z-23862, unit U-1489, paper P0004.

# Hardy-Littlewood 1923, Theorem A from a WEAKER cited explicit formula `TruncExplicitPrimB`

U-1485 VERIFY asked whether the printed remainder of Davenport ch. 19 carries an extra
`x^{1/4} log x`. It does in Davenport's simplified form, where the exceptional zero `1 - β₁`
near `0` is pulled out of the zero sum and `(x^{1-β₁} - 1)/(1 - β₁) ≪ x^{1/4} log x` is put into
the remainder (the same structure is reproduced in Kedlaya's notes, ch. 11, with `x^c log x`).
U-1479's `TruncExplicitPrim` instead keeps the low-zero sum `Σ_{|γ| ≤ 1} m/|ρ|` in the remainder,
which is Montgomery-Vaughan Theorem 12.10 with the bound on its constant `C(χ)`; it needs no
`x^{1/4}` term. To make the chain safe under BOTH readings, this file states

* `TruncExplicitPrimB`: `TruncExplicitPrim` with `A x^{1/4} log x` added to the remainder.

It is implied by `TruncExplicitPrim` (`truncExplicitPrimB_of_trunc`, PROVED) and also by
Davenport's printed form, since `x^{δ}/δ ≤ 1/δ + x^{1/4} log x` for `0 < δ ≤ 1/4`.

PROVED from it, everything else unconditional:
* `psiChiPrimBound_of_B`: `PsiChiPrimBound Θ` for `1/4 ≤ Θ < 1` on `NoZerosRightPrim Θ`.
* `psiPowerLog_of_B`: U-1453's `PsiPowerLog Θ` for `1/4 ≤ Θ` on `NoZerosRight Θ`.
* `printedA_form_all_U1489`: eq 3.113 p. 21, every `r ≥ 3`, `47/64 ≤ Θ < 3/4`,
  CONDITIONAL ON `TruncExplicitPrimB` only. The final assembly repeats the short argument of
  U-1468 `printedA_form_all_U1468` with `PsiPowerLog Θ` in place of the full `ExplicitFormulaLog`,
  since `TruncExplicitPrimB` yields `PsiPowerLog Θ` only for `Θ ≥ 1/4`.

Every proof is complete, no axiom. Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1489

open Real Finset
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.HardyLittlewood1923.U1444 (singR)
open LeanLab.HardyLittlewood1923.U1453 (PsiPowerLog)
open LeanLab.HardyLittlewood1923.U1463
open LeanLab.HardyLittlewood1923.U1468
open LeanLab.HardyLittlewood1923.U1473 (NoZerosRightPrim PsiChiPrimBound)
open LeanLab.HardyLittlewood1923.U1479 (IsNTZero mult mult_nonneg
  sum_inv_norm_le zero_re_bounds)
open LeanLab.PNTPort.BV (psiChi)

/-- `x^{1/4} log x ≤ x^Θ (log x)² / log 2` for `x ≥ 2`, `Θ ≥ 1/4`. -/
lemma quarter_le {x Θ : ℝ} (hx : 2 ≤ x) (hΘ : 1 / 4 ≤ Θ) :
    x ^ (1 / 4 : ℝ) * Real.log x ≤ 1 / Real.log 2 * (x ^ Θ * Real.log x ^ 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hp : x ^ (1 / 4 : ℝ) ≤ x ^ Θ := Real.rpow_le_rpow_of_exponent_le (by linarith) hΘ
  have hp0 : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  have h1 : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2, sq]; exact mul_le_mul_of_nonneg_left hlx (by linarith)
  calc x ^ (1 / 4 : ℝ) * Real.log x ≤ x ^ Θ * (Real.log x ^ 2 / Real.log 2) :=
        mul_le_mul hp h1 (by linarith) (by positivity)
    _ = 1 / Real.log 2 * (x ^ Θ * Real.log x ^ 2) := by ring

/-! ### Vacuity -/

end LeanLab.HardyLittlewood1923.U1489
