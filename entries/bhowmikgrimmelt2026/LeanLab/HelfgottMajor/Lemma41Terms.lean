module

public import LeanLab.HelfgottMajor.Sec48

/-!
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4: the Lemma 4.1 terms
of Props. 4.6 and 4.8, `c₀` of (4.3) and `|η′|₂ + 2π|δ||η|₂` in (4.1). Unit U-6064, CLOUD
20261020T0516Z-cloud35.

MATCH: Prop. 4.6 `c₀ ≤ 1.4056 + 13.3466|δ|`, Prop. 4.8 `c₀ ≤ 2.138 + 10.99|δ|` and
`|η′|₂ + 2π|δ||η|₂ ≤ 0.881 + 5.123|δ|`, from the printed norms (4.42) and (4.50).

FINDING, F-5032: Prop. 4.6's proof, p. 44, prints `|η♥′|₂ + 2π|δ||η♥|₂ ≤ 0.942 + 4.183|δ| ≤ 1 + 5|δ|`
with `|η♥|₂ = 0.9414` and `|η♥′|₂ = 0.6657` swapped; the true value is `0.6657 + 5.9149|δ|`, which
exceeds `1 + 5|δ|` once `|δ| > 0.37`, `printed_fails`. So the `x^{-3/2}` term `(log q + 6)(1 + 5|δ|)`
of (4.43) does not follow; with `1 + 6|δ|`, the form of Prop. 4.8, the proof goes through,
`repaired` and `repaired_R`, and Theorem 1.1's constant 650400/√q + 112 SURVIVES, `thm11_survives`.
The book version 1501.05438 prints the same line.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Lemma41Terms
open Real LeanLab.HelfgottMajor.Sec45

/-- `c₀` of (4.3): `(2/3)(|η′/√t|₁ + |η′√t|₁ + 2π|δ|(|η/√t|₁ + |η√t|₁))`. -/
noncomputable def c0 (a b c d δ : ℝ) : ℝ := 2 / 3 * (a + b + 2 * π * δ * (c + d))

/-- **Prop. 4.6: `c₀ ≤ 1.4056 + 13.3466|δ|`** with the Gaussian norms `|η′/√t|₁ = |η√t|₁ ≤ 1.03045`,
`|η′√t|₁ ≤ 1.07791`, `|η/√t|₁ ≤ 2.15581`, MATCH, 1.40557 and 13.34658. -/
theorem c0_gauss {δ : ℝ} (hδ : 0 ≤ δ) : c0 1.03045 1.07791 2.15581 1.03045 δ ≤ 1.4056 + 13.3466 * δ := by
  unfold c0; have := pi_lt_d20; nlinarith

/-- **Prop. 4.8: `c₀ ≤ 2.138 + 10.99|δ|`** with (4.50)'s `1.48469, 1.72169, 1.07791, 1.54568`, MATCH,
2.13759 and 10.98949. -/
theorem c0_t2 {δ : ℝ} (hδ : 0 ≤ δ) : c0 1.48469 1.72169 1.07791 1.54568 δ ≤ 2.138 + 10.99 * δ := by
  unfold c0; have := pi_lt_d20; nlinarith

lemma sqrt_nTwoP : 0.66566 < √(√π / 4) ∧ √(√π / 4) < 0.66567 := by
  have hs := sqrt_pi_lt; have hs0 := sqrt_pi_gt
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

/-- **Prop. 4.8: `|η′|₂ + 2π|δ||η|₂ ≤ 0.881 + 5.123|δ|`** with `|η′|₂² = 7√π/16`, `|η|₂² = 3√π/8`,
MATCH, 0.880596 and 5.122497. -/
theorem lemma41_t2 {δ : ℝ} (hδ : 0 ≤ δ) :
    √(7 * √π / 16) + 2 * π * δ * √(3 * √π / 8) ≤ 0.881 + 5.123 * δ := by
  have hs := sqrt_pi_lt
  have h1 : √(7 * √π / 16) < 0.8806 := by rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have h2 := LeanLab.HelfgottMajor.Sec48.sqrt_mTwo.2
  unfold LeanLab.HelfgottMajor.Sec48.mTwo at h2
  have := pi_lt_d20
  nlinarith [mul_le_mul_of_nonneg_left h2.le (by positivity : (0 : ℝ) ≤ 2 * π * δ)]

/-- **F-5032: the printed `≤ 1 + 5|δ|` fails for the Gaussian once `|δ| ≥ 2/5`**:
`|η♥′|₂ + 2π|δ||η♥|₂ = 0.6657 + 5.9149|δ|`. -/
theorem printed_fails {δ : ℝ} (hδ : 2 / 5 ≤ δ) : 1 + 5 * δ < √(√π / 4) + 2 * π * δ * √nTwo := by
  have h1 := sqrt_nTwoP.1
  have h2 := sqrt_nTwo_gt
  have := pi_gt_d20
  have h3 : 2 * π * 0.941396 * δ ≤ 2 * π * δ * √nTwo := by
    nlinarith [mul_le_mul_of_nonneg_left h2.le (by positivity : (0 : ℝ) ≤ 2 * π * δ)]
  nlinarith

/-- The swapped reading is what was printed: `|η♥|₂ ≤ 0.942` and `2π |η♥′|₂ ≤ 4.183`. -/
theorem printed_is_swap : √nTwo ≤ 0.942 ∧ 2 * π * √(√π / 4) ≤ 4.183 := by
  have h1 := sqrt_nTwo_lt; have h2 := sqrt_nTwoP.2; have := pi_lt_d20
  constructor
  · linarith
  · nlinarith [mul_le_mul_of_nonneg_left h2.le (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- **Repaired**: `|η♥′|₂ + 2π|δ||η♥|₂ ≤ 1 + 6|δ|`, the form of Prop. 4.8. -/
theorem repaired {δ : ℝ} (hδ : 0 ≤ δ) : √(√π / 4) + 2 * π * δ * √nTwo ≤ 1 + 6 * δ := by
  have := sqrt_nTwoP.2; have h2 := sqrt_nTwo_lt; have := pi_lt_d20
  nlinarith [mul_le_mul_of_nonneg_left h2.le (by positivity : (0 : ℝ) ≤ 2 * π * δ)]

/-- **Repaired, the last step of Prop. 4.6**: `(6.01 − 6)(1 + 6|δ|) + 13.347|δ| + 16.695 < 14|δ| + 17`,
so (4.43) holds with `(log q + 6)(1 + 6|δ|) x^{-3/2}`. -/
theorem repaired_R {δ : ℝ} (hδ : 0 ≤ δ) : (6.01 - 6) * (1 + 6 * δ) + 13.347 * δ + 16.695 < 14 * δ + 17 := by
  nlinarith

/-- Section 4.6 with the repair: `(log q + 6)(1 + 6|δ|) ≤ 19 + 1.35 · 10⁸/q` for `1 ≤ q ≤ 3 · 10⁵`,
`|δ| ≤ 1.2 · 10⁶/q`. -/
theorem sec46_repaired {q δ : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 3e5) (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1.2e6 / q) :
    (log q + 6) * (1 + 6 * δ) ≤ 19 + 1.35e8 / q := by
  have hl := log_q_le hq1 hq
  have hl0 := log_q_nonneg hq1
  have hq0 : 0 < q := by linarith
  have hδq : δ * q ≤ 1.2e6 := by rwa [le_div_iff₀ hq0] at hδ
  rw [show (19 : ℝ) + 1.35e8 / q = (19 * q + 1.35e8) / q by field_simp, le_div_iff₀ hq0]
  nlinarith [mul_le_mul_of_nonneg_left hδq (by linarith : (0 : ℝ) ≤ log q + 6),
    mul_nonneg hl0 _hδ0]

/-- **Theorem 1.1 SURVIVES**: with `x ≥ 10⁸`, `x^{-1} ≤ 10^{-4} x^{-1/2}` and
`x^{-3/2} ≤ 10^{-8} x^{-1/2}`, the repaired terms give at most `650400/√q + 112` per `x^{-1/2}`:
`648662/√q + 111 + 55 · 10⁻⁴ + 1700/q + 19 · 10⁻⁸ + 1.35/q ≤ 650400/√q + 112`. -/
theorem thm11_survives {q : ℝ} (hq1 : 1 ≤ q) :
    648662 / √q + 111 + 55e-4 + 1700 / q + 19e-8 + 1.35 / q ≤ 650400 / √q + 112 := by
  have hs : 1 ≤ √q := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hq1
  have hsq : √q ≤ q := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ q by linarith)
    nlinarith
  have h1 : 1 / q ≤ 1 / √q := one_div_le_one_div_of_le (by linarith) hsq
  have h2 : 1700 / q + 1.35 / q ≤ 1701.35 / √q := by
    rw [← add_div]; calc (1700 + 1.35) / q = 1701.35 * (1 / q) := by ring
      _ ≤ 1701.35 * (1 / √q) := by linarith
      _ = 1701.35 / √q := by ring
  have h3 : 648662 / √q + 1701.35 / √q ≤ 650400 / √q := by
    rw [← add_div]; apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

end LeanLab.HelfgottMajor.Lemma41Terms
