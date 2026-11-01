module

public import Mathlib
public import LeanLab.Dudek2014.SmallRange
public import LeanLab.Dudek2014.Section22

/-!
P0100 Dudek 2014, Theorem 2 for every x ≥ 2, CONDITIONAL ON the page 6 display only:
the kernel scan `small_range` below 67001, with no RH, and `theorem2_large_of` above 66799.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Section22

/-- **Theorem 2: a prime in `(x - (4/π)√x log x, x]` for every `x ≥ 2`, CONDITIONAL ON
`Display22`**, the one analytic input the paper derives from RH. -/
theorem theorem2_of_display (hd : Display22) :
    ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  theorem2_of_large (fun _ hx => theorem2_large_of hd hx)

/-- Lemma 4's proof, QUESTION from the U-5109 VERIFY: integrating `-log 2π` from 2 to x leaves the
boundary term `+2 log 2π`, which the printed list of error pieces does not show; the constant
piece of the true `ε` is `-2 + 2 log 2π`. It is at most `2` in absolute value, so the printed
term `2` already covers it and the bound `12/5` stands. PROVED: `0 ≤ 2 log 2π - 2 ≤ 2`. -/
theorem lemma4_boundary : 0 ≤ 2 * Real.log (2 * Real.pi) - 2 ∧ 2 * Real.log (2 * Real.pi) - 2 ≤ 2 := by
  have h2 : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) (by linarith [Real.pi_gt_three])
  have := log_pi_lt; have := log_pi_gt
  have := Real.log_two_gt_d9; have := Real.log_two_lt_d9
  constructor <;> linarith

end LeanLab.Dudek2014.Section22

