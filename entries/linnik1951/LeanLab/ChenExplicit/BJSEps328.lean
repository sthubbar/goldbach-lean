module

public import LeanLab.ChenExplicit.BJSThm51

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0923.
P0009 BJS 2022, (121) at the lab's corrected Section 9 parameters `log log X₂ = 32.8`,
`X₃ = X₂^{1/8}`, `δ = 1.476`. PROVED: `pbar1_328`, `3·5·…·59 ≤ (log x₁(X₂))^δ`, so `p̄ ≥ 59` and
`ε₁ ≤ 1/57`; `pbar2_328`, `3·5·…·53 ≤ (log x₂(X₃))^δ < 3·5·…·59`, so `p̄ = 53` and `ε₂ = 1/51`.
These are the `ε₁`, `ε₂` hypotheses of Section9Link.lean.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJS328

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.BJS51

lemma exp_big' (x : ℝ) (hx : 32 ≤ x) : 7 * 10 ^ 13 ≤ exp x := by
  have h := exp_nat_ge 32
  have : exp ((32 : ℕ) : ℝ) ≤ exp x := exp_le_exp.mpr (by push_cast; linarith)
  push_cast at h this
  have h2 : (7 * 10 ^ 13 : ℝ) ≤ 2.7182818283 ^ 32 := by norm_num
  linarith

/-- `p̄ ≥ 59` for `x₁(X₂)`: `log x₁(X₂) = e^{32.8} - 5 · 32.8`. -/
theorem pbar1_328 :
    let ℓ := exp (328 / 10) - 5 * (328 / 10)
    (oddPrimorial 59 : ℝ) ≤ ℓ ^ (1.476 : ℝ) := by
  intro ℓ
  have hE := exp_big' (328 / 10) (by norm_num)
  have hpos : 0 < ℓ := by simp only [ℓ]; linarith
  have hlo : exp (328 / 10) * (999 / 1000) ≤ ℓ := by simp only [ℓ]; nlinarith
  have l2 : 328 / 10 + log (999 / 1000) ≤ log ℓ := by
    rw [← log_exp (328 / 10 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log (by positivity) hlo
  have l3 : -(1 / 999 : ℝ) ≤ log (999 / 1000) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (999 / 1000 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  rw [rpow_def_of_pos hpos, oddPrimorial_59]
  have hm : log ℓ * 1.476 = 48 + (1.476 * log ℓ - 48) := by ring
  rw [hm, exp_add]
  have a1 := exp_nat_ge 48
  push_cast at a1
  have b : 0.4 ≤ 1.476 * log ℓ - 48 := by norm_num at l3 ⊢; nlinarith
  have b2 : (1.4 : ℝ) ≤ exp (1.476 * log ℓ - 48) := by
    have := add_one_le_exp (1.476 * log ℓ - 48); linarith
  have c : (961380175077106319535 : ℝ) ≤ 2.7182818283 ^ 48 * 1.4 := by norm_num
  have := mul_le_mul a1 b2 (by norm_num) (exp_pos _).le
  push_cast; linarith

lemma bracket53' (ℓ : ℝ) (hℓ : 0 < ℓ) (h1 : 45 ≤ 1.476 * log ℓ) (h2 : 1.476 * log ℓ ≤ 46) :
    (oddPrimorial 53 : ℝ) ≤ ℓ ^ (1.476 : ℝ) ∧ ℓ ^ (1.476 : ℝ) < (oddPrimorial 59 : ℝ) := by
  rw [rpow_def_of_pos hℓ, oddPrimorial_53, oddPrimorial_59]
  have hm : log ℓ * 1.476 = 1.476 * log ℓ := mul_comm _ _
  rw [hm]
  have a1 := exp_nat_ge 45
  have a2 := exp_nat_le 46
  have b1 : exp ((45 : ℕ) : ℝ) ≤ exp (1.476 * log ℓ) := exp_le_exp.mpr (by push_cast; linarith)
  have b2 : exp (1.476 * log ℓ) ≤ exp ((46 : ℕ) : ℝ) := exp_le_exp.mpr (by push_cast; linarith)
  push_cast at a1 a2 b1 b2
  have c1 : (16294579238595022365 : ℝ) ≤ 2.7182818283 ^ 45 := by norm_num
  have c2 : (2.7182818286 : ℝ) ^ 46 < 961380175077106319535 := by norm_num
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- `p̄ = 53` for `x₂(X₃)`, `X₃ = X₂^{1/8}`: `log x₂(X₃) = e^{32.8}/8 - 15 (32.8 - 3 log 2)`. -/
theorem pbar2_328 :
    let ℓ := exp (328 / 10) / 8 - 15 * (328 / 10 - 3 * log 2)
    (oddPrimorial 53 : ℝ) ≤ ℓ ^ (1.476 : ℝ) ∧ ℓ ^ (1.476 : ℝ) < (oddPrimorial 59 : ℝ) := by
  intro ℓ
  have hE := exp_big' (328 / 10) (by norm_num)
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have hpos : 0 < ℓ := by simp only [ℓ]; nlinarith
  have hlo : exp (328 / 10) * (1 / 9) ≤ ℓ := by simp only [ℓ]; nlinarith
  have hhi : ℓ ≤ exp (328 / 10) * (1 / 8) := by simp only [ℓ]; nlinarith
  have l1 : log ℓ ≤ 328 / 10 + log (1 / 8) := by
    rw [← log_exp (328 / 10 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log hpos hhi
  have l2 : 328 / 10 + log (1 / 9) ≤ log ℓ := by
    rw [← log_exp (328 / 10 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log (by positivity) hlo
  have e8 : log (1 / 8 : ℝ) = -(3 * log 2) := by
    rw [one_div, log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; ring
  have e9 : log (1 / 9 : ℝ) = -(2 * log 3) := by
    rw [one_div, log_inv, show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]; push_cast; ring
  have l3 := log_three_lt_d9
  rw [e8] at l1; rw [e9] at l2
  norm_num at l2a l3
  exact bracket53' ℓ hpos (by nlinarith) (by nlinarith)

end LeanLab.ChenExplicit.BJS328
