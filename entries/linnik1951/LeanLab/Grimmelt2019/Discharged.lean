module

public import LeanLab.Grimmelt2019.Bookkeeping
public import LeanLab.PNTPort.PsiChi.CitedDischarged

/-!
P0074 L. Grimmelt 2019, arXiv 1910.05187. Unit U-6753, run 20261020T2317Z-cloud53.

The full interval input of `Bookkeeping.lean`, `LeanLab.ExceptionalSet.LogPowerSaving`, is
discharged by the lab's unconditional `LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving`.
What remains is CONDITIONAL ON the analytic core of Section 5 only: the estimate (1) at the
single length of Lemma 5.1.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019

/-- CONDITIONAL ON `ExactLengthLogSaving c` only: the single length estimate gives the estimate
(1) for every `H > X^{c+ε}`. -/
theorem logSaving_of_exactLength' {c : ℝ} (hc : 0 ≤ c) (hcore : ExactLengthLogSaving c) :
    ShortIntervalLogSaving c :=
  logSaving_of_exactLength hc hcore LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving

/-- CONDITIONAL ON the Lemma 5.1 core only: the estimate (1) at `H = Y^{1/9+2ε}`,
`Y = X^{21/40+ε}`, for every `ε > 0`, gives Theorem 1.1 as stated. -/
theorem thm1_1_of_lemma51_core'
    (hcore : ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (EXH X ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) : ℝ)
        ≤ C * (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) / Real.log X ^ A) :
    ShortIntervalLogSaving (7 / 120) :=
  thm1_1_of_lemma51_core hcore LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving

end LeanLab.Grimmelt2019
