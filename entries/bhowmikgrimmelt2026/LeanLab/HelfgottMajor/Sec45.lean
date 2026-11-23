module

public import LeanLab.HelfgottMajor.Assembly
public import LeanLab.Helfgott2013.GammaFine
public import LeanLab.Dudek2014.Section22

/-!
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Section 4: the
constants of Prop. 4.6 and Lemma 4.10, pages 42 to 51, that Section 4.6 and `Assembly.lean` use,
2.337, 21.817, 2.85, 74.38 in Prop. 4.6 and 9.06194, 9.4612, 11.287 in Lemma 4.10. Read from the
arXiv PDF with pdftotext, cloud session 20261020T0516Z-cloud35, unit U-6061; Python with 30-digit
mpmath in numerics/sec45_check.py.

Only the arithmetic is checked. Cited and not checked here: the norm identities (4.42) by symbolic
integration, `|η♥/√t|₁ = Γ(1/4)/2^{3/4} ≤ 2.15581`, Lemma 4.4's shape (4.29), `c₁ = 3.516` of
Cor. 3.2, `|M h(ir)|₁ ≤ 16.193918` of (B.17), and the two integral bounds in the proof of Lemma 4.10.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Sec45
open Real

/-- `|η♥ · log|₂²` in closed form, (4.42): `(√π/16)(π² + 2γ² + 8γ log 2 + 8 log² 2)`. -/
noncomputable def nLog : ℝ :=
  √π / 16 * (π ^ 2 + 2 * eulerMascheroniConstant ^ 2 + 8 * eulerMascheroniConstant * log 2 +
    8 * log 2 ^ 2)

/-- `|η♥|₂² = √π/2`, (4.42). -/
noncomputable def nTwo : ℝ := √π / 2

lemma sqrt_pi_lt : √π < 1.7724539 := by
  rw [Real.sqrt_lt' (by norm_num)]; have := pi_lt_d20; nlinarith

lemma sqrt_pi_gt : 1.7724538 < √π := by
  rw [Real.lt_sqrt (by norm_num)]; have := pi_gt_d20; nlinarith

/-- **(4.42): `|η♥ · log|₂² ≤ 1.94753`**, MATCH, value 1.9475222. -/
theorem nLog_le : nLog ≤ 1.94753 := by
  unfold nLog
  have hp := pi_lt_d20
  have hp' := pi_gt_d20
  have hg := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
  have hg' := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
  have hl := log_two_lt_d9
  have hl' := log_two_gt_d9
  have hs := sqrt_pi_lt
  have hs0 := sqrt_pi_gt
  set γ := eulerMascheroniConstant
  have h1 : π ^ 2 < 9.8696045 := by nlinarith
  have h2 : 2 * γ ^ 2 < 0.66635655 := by nlinarith
  have h3 : 8 * γ * log 2 < 3.2007634 := by nlinarith
  have h4 : 8 * log 2 ^ 2 < 3.8436242 := by nlinarith
  have hsum : π ^ 2 + 2 * γ ^ 2 + 8 * γ * log 2 + 8 * log 2 ^ 2 < 17.5803487 := by linarith
  have hpos : 0 < π ^ 2 + 2 * γ ^ 2 + 8 * γ * log 2 + 8 * log 2 ^ 2 := by positivity
  nlinarith

lemma nLog_nonneg : 0 ≤ nLog := by
  unfold nLog
  have := log_two_gt_d9
  have := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
  positivity

lemma sqrt_nTwo_lt : √nTwo < 0.941397 := by
  unfold nTwo; rw [Real.sqrt_lt' (by norm_num)]; have := sqrt_pi_lt; nlinarith

lemma sqrt_nTwo_gt : 0.941396 < √nTwo := by
  unfold nTwo; rw [Real.lt_sqrt (by norm_num)]; have := sqrt_pi_gt; nlinarith

lemma sqrt_nLog_lt : √nLog < 1.39554 := by
  rw [Real.sqrt_lt' (by norm_num)]; have := nLog_le; nlinarith

/-- **Prop. 4.6, the coefficient of `√T₀ log qT₀`: `|η|₂ + |η · log|₂ ≤ 2.337`**, (4.29) with
(4.42), MATCH, value 2.336933. -/
theorem coef_sqrtT0_log : √nTwo + √nLog ≤ 2.337 := by
  have := sqrt_nTwo_lt; have := sqrt_nLog_lt; linarith

/-- **Prop. 4.6, the coefficient of `√T₀`: `17.21 |η · log|₂ − log(2π√e) |η|₂ ≤ 21.817`**, MATCH,
value 21.816315. -/
theorem coef_sqrtT0 : 17.21 * √nLog - log (2 * π * √(exp 1)) * √nTwo ≤ 21.817 := by
  have h1 := sqrt_nLog_lt
  have h2 := sqrt_nTwo_gt
  have hl : 2.337862 < log (2 * π * √(exp 1)) := by
    rw [log_mul (by positivity) (by positivity), Real.log_sqrt (exp_pos 1).le, log_exp]
    have := log_two_pi_gt; linarith
  nlinarith

/-- **Prop. 4.6, the `log q` and constant terms: `1.32 · 2.15581 ≤ 2.85`, `34.5 · 2.15581 ≤ 74.38`**,
with the paper's `|η♥/√t|₁ ≤ 2.15581`, MATCH, values 2.84567 and 74.37545. -/
theorem coef_logq : (1.32 : ℝ) * 2.15581 ≤ 2.85 ∧ (34.5 : ℝ) * 2.15581 ≤ 74.38 := by
  constructor <;> norm_num

/-- **Lemma 4.10: `c₁ |M h(ir)|₁/(2π) ≤ 9.06194`** with `c₁ = 3.516` and `|M h(ir)|₁ ≤ 16.193918`,
MATCH, value 9.0619348. -/
theorem k_le : 3.516 * 16.193918 / (2 * π) ≤ (9.06194 : ℝ) := by
  have := pi_gt_d20
  rw [div_le_iff₀ (by positivity)]; nlinarith

lemma log_105_gt : (4.65 : ℝ) < log 105 := by
  have h1 : log 105 = log (105 / 100) + 2 * log 10 := by
    rw [show (105 : ℝ) = 105 / 100 * 10 ^ 2 by norm_num, log_mul (by norm_num) (by norm_num),
      log_pow]; norm_num
  have h2 : 1 - (105 / 100 : ℝ)⁻¹ ≤ log (105 / 100) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 105 / 100 by norm_num); exact this
  have h3 := log_ten_gt
  rw [h1]; norm_num at h2 ⊢; linarith

/-- **Lemma 4.10, (4.62): `(9.06194/2π)(1/c + a/(c² · 100)) ≤ 9.4612`** at `c = 0.1598`,
`T₀ − H ≥ 100`, `a = 1/2 + (1 + 0.1598π/2)/log T₀` with `T₀ ≥ 105`, MATCH, value 9.45957. -/
theorem exp_term_le {T₀ : ℝ} (hT : 105 ≤ T₀) :
    9.06194 / (2 * π) * (1 / 0.1598 + (1 / 2 + (1 + 0.1598 * π / 2) / log T₀) / (0.1598 ^ 2 * 100))
      ≤ 9.4612 := by
  have hp := pi_gt_d20
  have hp' := pi_lt_d20
  have hl : (4.65 : ℝ) < log T₀ :=
    log_105_gt.trans_le (log_le_log (by norm_num) hT)
  have hl0 : 0 < log T₀ := by linarith
  have ha : (1 + 0.1598 * π / 2) / log T₀ ≤ (1 + 0.1598 * 3.14159266 / 2) / 4.65 := by
    apply div_le_div₀ (by positivity) (by nlinarith) (by norm_num) hl.le
  have hk : 9.06194 / (2 * π) ≤ (9.06194 : ℝ) / (2 * 3.14159265) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hb : 0 ≤ 1 / 0.1598 + (1 / 2 + (1 + 0.1598 * π / 2) / log T₀) / (0.1598 ^ 2 * 100) := by
    positivity
  calc 9.06194 / (2 * π) * (1 / 0.1598 + (1 / 2 + (1 + 0.1598 * π / 2) / log T₀) / (0.1598 ^ 2 * 100))
      ≤ (9.06194 : ℝ) / (2 * 3.14159265) *
          (1 / 0.1598 + (1 / 2 + (1 + 0.1598 * 3.14159266 / 2) / 4.65) / (0.1598 ^ 2 * 100)) := by
        apply mul_le_mul hk _ hb (by norm_num)
        gcongr
    _ ≤ 9.4612 := by norm_num

/-- **Lemma 4.10, (4.63): the Gaussian coefficient is at most 11.287** for every
`u = (T₀ − H)/(π|δ|) ≥ 4π`: `(9.06194/(8 · 0.1065))(1 + (π/2 + 1/(2 · 0.1065 u))/(u log u))
≤ 11.287`, MATCH, value 11.28630 at `u = 4π`. -/
theorem gauss_term_le {u : ℝ} (hu : 4 * π ≤ u) :
    9.06194 / (8 * 0.1065) * (1 + (π / 2 + 1 / (2 * 0.1065 * u)) / (u * log u)) ≤ 11.287 := by
  have hp := pi_gt_d20
  have hp' := pi_lt_d20
  have hu0 : (12.566 : ℝ) ≤ u := by linarith
  have hl4 : 2.531 < log (4 * π) := by
    rw [show (4 : ℝ) * π = 2 * (2 * π) by ring, log_mul (by norm_num) (by positivity)]
    have := log_two_pi_gt; have := log_two_gt_d9; linarith
  have hl : 2.531 < log u := hl4.trans_le (log_le_log (by positivity) hu)
  have hden : (12.566 : ℝ) * 2.531 ≤ u * log u := by nlinarith
  have hnum : π / 2 + 1 / (2 * 0.1065 * u) ≤ 3.14159266 / 2 + 1 / (2 * 0.1065 * 12.566) := by
    have : 1 / (2 * 0.1065 * u) ≤ 1 / (2 * 0.1065 * 12.566) :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith
  have hfrac : (π / 2 + 1 / (2 * 0.1065 * u)) / (u * log u) ≤
      (3.14159266 / 2 + 1 / (2 * 0.1065 * 12.566)) / (12.566 * 2.531) :=
    div_le_div₀ (by norm_num) hnum (by norm_num) hden
  have : (9.06194 : ℝ) / (8 * 0.1065) *
      (1 + (3.14159266 / 2 + 1 / (2 * 0.1065 * 12.566)) / (12.566 * 2.531)) ≤ 11.287 := by
    norm_num
  calc _ ≤ (9.06194 : ℝ) / (8 * 0.1065) *
        (1 + (3.14159266 / 2 + 1 / (2 * 0.1065 * 12.566)) / (12.566 * 2.531)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    _ ≤ 11.287 := this

/-- Vacuity: `T₀ = 105` and `u = 4π` meet the hypotheses. -/
theorem vacuity : (105 : ℝ) ≤ 105 ∧ 4 * π ≤ 4 * π := ⟨le_rfl, le_rfl⟩

end LeanLab.HelfgottMajor.Sec45
