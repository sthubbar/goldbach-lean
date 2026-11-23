module

public import LeanLab.HelfgottMajor.Sec45

/-!
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Prop. 4.8, pages 46
and 47, the smoothing `η(t) = t² e^{-t²/2}`: its norms (4.50) and the coefficients of (4.52) that
come from Lemma 4.4's bound (4.29). Unit U-6062, CLOUD 20261020T0516Z-cloud35; Python in
numerics/sec45_check.py.

FINDING, cosmetic: (4.29) with (4.50) gives the coefficient `17.21 |η · log|₂ − log(2π√e) |η|₂`
of `√T₀` equal to 5.05585, while Prop. 4.8 prints 5.053; `coef_sqrtT0_gt` proves it exceeds 5.055,
so the printed 5.053 does not follow. The book version, arXiv 1501.05438, prints 5.056 in the
proposition, `coef_sqrtT0_le` proves that one, but still writes 5.053 in its Section 9.6 display.
The Theorem 1.2 constant survives: `thm12_survives`, against `printed_275263_fails`.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Sec48
open Real LeanLab.HelfgottMajor.Sec45

/-- `|η|₂² = 3√π/8` for `η(t) = t² e^{-t²/2}`, (4.50). -/
noncomputable def mTwo : ℝ := 3 * √π / 8

/-- `|η · log|₂²` in closed form, (4.50). -/
noncomputable def mLog : ℝ :=
  √π / 64 * (8 * (3 * eulerMascheroniConstant - 8) * log 2 + 3 * π ^ 2 +
    6 * eulerMascheroniConstant ^ 2 + 24 * log 2 ^ 2 + 16 - 32 * eulerMascheroniConstant)

lemma mLog_bounds : 0.1636203 ≤ mLog ∧ mLog ≤ 0.16364096 := by
  unfold mLog
  have hp := pi_lt_d20
  have hp' := pi_gt_d20
  have hg := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
  have hg' := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
  have hl := log_two_lt_d9
  have hl' := log_two_gt_d9
  have hs := sqrt_pi_lt
  have hs0 := sqrt_pi_gt
  set γ := eulerMascheroniConstant
  set L := log 2
  have a1 : 9.6022671 ≤ 24 * γ * L := by nlinarith
  have a2 : 24 * γ * L ≤ 9.60229 := by nlinarith
  have b1 : 29.6088132 ≤ 3 * π ^ 2 := by nlinarith
  have b2 : 3 * π ^ 2 ≤ 29.6088133 := by nlinarith
  have c1 : 1.999058 ≤ 6 * γ ^ 2 := by nlinarith
  have c2 : 6 * γ ^ 2 ≤ 1.9990676 := by nlinarith
  have d1 : 11.5308723 ≤ 24 * L ^ 2 := by nlinarith
  have d2 : 24 * L ^ 2 ≤ 11.5308724 := by nlinarith
  have e : 8 * (3 * γ - 8) * L + 3 * π ^ 2 + 6 * γ ^ 2 + 24 * L ^ 2 + 16 - 32 * γ =
      24 * γ * L - 64 * L + 3 * π ^ 2 + 6 * γ ^ 2 + 24 * L ^ 2 + 16 - 32 * γ := by ring
  rw [e]
  have hlo : 5.90868 ≤ 24 * γ * L - 64 * L + 3 * π ^ 2 + 6 * γ ^ 2 + 24 * L ^ 2 + 16 - 32 * γ := by
    linarith
  have hhi : 24 * γ * L - 64 * L + 3 * π ^ 2 + 6 * γ ^ 2 + 24 * L ^ 2 + 16 - 32 * γ ≤ 5.90877 := by
    linarith
  constructor <;> nlinarith

/-- Square-root bounds from `mLog_bounds`; the value of `mLog` is 0.16363964, the printed bound
0.16364 of (4.50) MATCH by Python; the lab's γ bounds give only `mLog ≤ 0.16364096` in Lean. -/
lemma sqrt_mLog : 0.4045 < √mLog ∧ √mLog < 0.4045256 := by
  obtain ⟨h1, h2⟩ := mLog_bounds
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

lemma sqrt_mTwo : 0.815273 < √mTwo ∧ √mTwo < 0.8152732 := by
  have hs := sqrt_pi_lt; have hs0 := sqrt_pi_gt
  unfold mTwo
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

lemma log_two_pi_sqrt_e : 2.337862 < log (2 * π * √(exp 1)) ∧ log (2 * π * √(exp 1)) < 2.3379472 := by
  rw [log_mul (by positivity) (by positivity), Real.log_sqrt (exp_pos 1).le, log_exp,
    log_mul (by norm_num) (by positivity)]
  have := log_two_pi_gt; have := LeanLab.Dudek2014.Section22.log_pi_lt; have := log_two_lt_d9
  constructor
  · rw [← log_mul (by norm_num) (by positivity)]; linarith
  · linarith

/-- **Prop. 4.8, coefficient of `√T₀ log qT₀`: `|η|₂ + |η · log|₂ ≤ 1.22`**, MATCH, 1.219797. -/
theorem coef_sqrtT0_log : √mTwo + √mLog ≤ 1.22 := by
  have := sqrt_mLog.2; have := sqrt_mTwo.2; linarith

/-- **Prop. 4.8, coefficient of `√T₀` from (4.29): more than 5.055**, so the printed 5.053 does not
follow; value 5.055849. -/
theorem coef_sqrtT0_gt : 5.055 < 17.21 * √mLog - log (2 * π * √(exp 1)) * √mTwo := by
  have h1 := sqrt_mLog.1; have h2 := sqrt_mTwo.2; have h3 := log_two_pi_sqrt_e.2
  have h0 : 0 ≤ √mTwo := Real.sqrt_nonneg _
  nlinarith

/-- **The book's 5.056 holds.** -/
theorem coef_sqrtT0_le : 17.21 * √mLog - log (2 * π * √(exp 1)) * √mTwo ≤ 5.056 := by
  have h1 := sqrt_mLog.2; have h2 := sqrt_mTwo.1; have h3 := log_two_pi_sqrt_e.1
  nlinarith

/-- **Prop. 4.8, `log q` and constant terms: `1.32 · 1.07791 ≤ 1.423`, `34.5 · 1.07791 ≤ 37.188`**,
with the printed `|η/√t|₁ ≤ 1.07791`, MATCH. -/
theorem coef_logq : (1.32 : ℝ) * 1.07791 ≤ 1.423 ∧ (34.5 : ℝ) * 1.07791 ≤ 37.188 := by
  constructor <;> norm_num

lemma log_1e8 : 18.420678 < log (10 ^ 8 : ℝ) ∧ log (10 ^ 8 : ℝ) < 18.420684 := by
  rw [log_pow]; have := log_ten_gt; have := log_ten_lt; push_cast
  constructor <;> linarith

/-- **Section 4.6, the `1/√q` coefficient at `T₀ = 10⁸/q`**: with the true coefficient above 5.055,
`1.22 · 10⁴ log 10⁸ + c · 10⁴` exceeds the printed 275263 ... -/
theorem printed_275263_fails {c : ℝ} (hc : 5.055 < c) :
    275263 < 1.22 * 10 ^ 4 * log (10 ^ 8 : ℝ) + c * 10 ^ 4 := by
  have := log_1e8.1; nlinarith

/-- ... but with the book's 5.056 it stays below Theorem 1.2's 276600 less the 55.2 + 0.0004 + 1322
terms' room, so Theorem 1.2 survives: `1.22 · 10⁴ log 10⁸ + 5.056 · 10⁴ ≤ 275300 ≤ 276600`. -/
theorem thm12_survives : 1.22 * 10 ^ 4 * log (10 ^ 8 : ℝ) + 5.056 * 10 ^ 4 ≤ 275300 := by
  have := log_1e8.2; nlinarith

end LeanLab.HelfgottMajor.Sec48
