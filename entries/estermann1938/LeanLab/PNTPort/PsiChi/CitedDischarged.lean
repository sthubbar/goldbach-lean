module

public import LeanLab.PNTPort.PsiChi.Unconditional
public import LeanLab.ExceptionalSet.BhowmikGrimmelt2026

/-!
# Cited statements of the lab that are now proved

Lab proof, unit U-5211, CLOUD 20261019T0514Z-cloud17. AI wrote the Lean code. Each theorem has
exactly the type of a statement the lab carries as a cited `sorry`; it cannot replace that
`sorry` in place, since this file imports the modules that state them. No lab proof calls those
cited statements, grep of 2026-10-19.

* `Ternary.vinogradov`, `∃ C, TernaryAbove C`: `ternary_vinogradov`;
* `Ternary.hardyLittlewood`, its GRH form: `ternary_hardyLittlewood`;
* `ExceptionalSet.vanDerCorput` and `chudakov`, `DensityZero`: `exceptional_densityZero`;
* `ExceptionalSet.vanDerCorput_chudakov_strong`, `estermann`, `BG2026.theorem43`,
  `LogPowerSaving`: `exceptional_logPowerSaving`.
-/

@[expose] public section


namespace LeanLab.PNTPort.PsiChi

theorem ternary_vinogradov : ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C := vinogradov_three_primes

/-- `Ternary.hardyLittlewood`, the GRH form, holds without GRH. -/
theorem ternary_hardyLittlewood : LeanLab.DERZ1997.GRH → ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C :=
  fun _ => vinogradov_three_primes

theorem exceptional_densityZero : LeanLab.ExceptionalSet.DensityZero := goldbach_densityZero

theorem exceptional_logPowerSaving : LeanLab.ExceptionalSet.LogPowerSaving :=
  goldbach_logPowerSaving

end LeanLab.PNTPort.PsiChi
