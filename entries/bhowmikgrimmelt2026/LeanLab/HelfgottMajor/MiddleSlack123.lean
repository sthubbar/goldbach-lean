module

public import LeanLab.HelfgottMajor.Gaussian123Base

/-!
P0014 Lemma 4.4, pages 39 and 40, display 4.32: the middle mass bound with two units of
proved slack for T at least 100. This is not a printed statement. It is used to pay for the
log x of the corrected Lemma 4.1.
The proof repeats the large height case of Decomp526a.middle_mass_large and keeps the slack
in the final scalar absorption.
CONDITIONAL ON the shared lab count ZeroCount1623.book_zero_count, as
Decomp526a.middle_mass_bound is, and on nothing else. Route burst 2026-11-15, step p6.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.MiddleSlack123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open MeasureTheory LeanLab.HelfgottMajor LeanLab.HelfgottMajor.Decomp389b
  LeanLab.HelfgottMajor.Decomp526a Set

/-- PROVED. Scalar absorption of the finite upper endpoint into the page 40 budget of P0014
Lemma 4.4, with two units of slack kept when s is at least 10. Derived arithmetic from the
norms of display 4.42 on page 43, not a printed statement. -/
theorem finite_endpoint_absorption_slack (s L lq : ℝ) (hs : 10 ≤ s) (hL : 0 ≤ L)
    (hlq : 0 ≤ lq) :
    (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) * s * L +
      11.497 * sqrt Sec45.nLog * s + 2.15581 * (0.3 * lq + 6.778) +
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * (0.15 * L + 3.389) ≤
    (sqrt Sec45.nTwo + sqrt Sec45.nLog) * s * L +
      (17.21 * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * s +
      2.15581 * (0.5 * lq + 17.7) - 2 := by
  have hN0 := sqrt_nonneg Sec45.nTwo
  have hL0 := sqrt_nonneg Sec45.nLog
  have hNlo := Sec45.sqrt_nTwo_gt
  have hNhi := Sec45.sqrt_nTwo_lt
  have hLlo := sqrt_nLog_lower
  have hLhi := Sec45.sqrt_nLog_lt
  have hC := BookP1617.K_bds
  have hprod := mul_le_mul hC.2.le hNhi.le hN0 (by norm_num)
  have hA : (0.9 : ℝ) ≤ sqrt Sec45.nTwo + sqrt Sec45.nLog -
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) := by linarith
  have hB : (4 : ℝ) ≤ 17.21 * sqrt Sec45.nLog -
      log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo - 11.497 * sqrt Sec45.nLog := by
    nlinarith
  have hEL : 3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 0.15 ≤ (1.25 : ℝ) := by
    linarith
  have hEC : 3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 3.389 ≤ (28.1 : ℝ) := by
    linarith
  have hAs := mul_le_mul_of_nonneg_right hA (show 0 ≤ s by linarith)
  have hBs := mul_le_mul_of_nonneg_right hB (show 0 ≤ s by linarith)
  have hAL : 0 ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog -
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog)) * s -
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 0.15 := by linarith
  have hp := mul_nonneg hAL hL
  nlinarith

end LeanLab.HelfgottMajor.MiddleSlack123
