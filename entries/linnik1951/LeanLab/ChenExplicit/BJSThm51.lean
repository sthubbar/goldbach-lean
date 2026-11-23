module

public import LeanLab.ChenExplicit.BJSCbar
public import LeanLab.ChenExplicit.Reductions

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0920.
P0009 Bordignon, Johnston, Starichkova, arXiv 2207.09452v6, Theorem 51, read in Claude in Chrome.

Two checks on the printed Theorem 51, FINDINGS F-0021 and F-0022.

F-0021. Theorem 51 converts the remainder `320 m(X₃)(1+ε₀) N / (3 log(1+ε₀) log² N)` into units
of `U_N N / log² N` with the factor `(2 e^{γ} ∏_{p>2}(1 - 1/(p-1)²))⁻¹`. Dividing by `U_N` needs
`U_N⁻¹`, and `U_N = 2 e^{-γ} twinC` exactly when `N` is a power of two, so `U_N⁻¹` is
`e^{2γ}` times the printed factor there. `U_two_pow` and `printed51_factor_lt` PROVE this.

F-0022. Case 2 of the proof of Theorem 51 only knows `k₂ ≥ K_δ(x₂(Y_j))` with `Y_j ≥ N^{1/8}`,
and `N > X₃⁸`, so Lemma 41 gives `ε₂` at `x₂(X₃)`, or at `x₂(X₂^{1/8})` as Section 9's own `𝓕`
writes, not at `x₂(X₃⁸)`. With `δ = 1.478`: at `Y = X₃ = exp(exp 30.62)` and at
`Y = X₂^{1/8} = exp(exp(32.7)/8)` the largest prime `p̄` of (121) is 53, so `ε₂ = 1/51`, not the
`1/57` that `x₂(X₃⁸)` gives. `pbar_X3` and `pbar_X2_eighth` PROVE `p̄ = 53` at both points.
-/

@[expose] public section

open Finset Real

noncomputable section
namespace LeanLab.ChenExplicit.BJS51

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS

/-- For `N = 2^k` there are no odd prime factors, so `U_N = 2 e^{-γ} twinC`. -/
theorem U_two_pow (k : ℕ) : U (2 ^ k) = 2 * exp (-eulerMascheroniConstant) * twinC := by
  unfold U
  have : (2 ^ k).primeFactors.filter (2 < ·) = ∅ := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.primeFactors_prime_pow hk.ne' Nat.prime_two]; decide
  rw [this, prod_empty, mul_one]

/-- **F-0021, PROVED.** At every power of two, `U_N⁻¹` is `e^{2γ}` times the printed factor
`(2 e^{γ} twinC)⁻¹` of Theorem 51, hence strictly larger. -/
theorem printed51_factor_lt (k : ℕ) :
    (U (2 ^ k))⁻¹ = exp (2 * eulerMascheroniConstant) * (2 * exp eulerMascheroniConstant * twinC)⁻¹ ∧
    (2 * exp eulerMascheroniConstant * twinC)⁻¹ < (U (2 ^ k))⁻¹ := by
  have ht := twinC_pos
  have hγ := one_half_lt_eulerMascheroniConstant
  have e : (U (2 ^ k))⁻¹ =
      exp (2 * eulerMascheroniConstant) * (2 * exp eulerMascheroniConstant * twinC)⁻¹ := by
    rw [U_two_pow]
    have h1 : exp (2 * eulerMascheroniConstant) =
        exp eulerMascheroniConstant * exp eulerMascheroniConstant := by
      rw [← exp_add]; ring_nf
    have h2 : exp (-eulerMascheroniConstant) = (exp eulerMascheroniConstant)⁻¹ := exp_neg _
    rw [h1, h2]
    have := exp_pos eulerMascheroniConstant
    field_simp
  refine ⟨e, ?_⟩
  rw [e]
  have h3 : 1 < exp (2 * eulerMascheroniConstant) := one_lt_exp_iff.mpr (by linarith)
  have h4 : 0 < (2 * exp eulerMascheroniConstant * twinC)⁻¹ := by
    have := exp_pos eulerMascheroniConstant; positivity
  nlinarith

theorem oddPrimorial_59 : oddPrimorial 59 = 961380175077106319535 := by
  unfold oddPrimorial; decide

theorem nextprime_53 : ∀ q ∈ Finset.Ioo 53 59, ¬ Nat.Prime q := by decide

lemma e_lt : exp 1 < 2.7182818286 := exp_one_lt_d9
lemma e_gt : 2.7182818283 < exp 1 := exp_one_gt_d9

lemma exp_nat_le (n : ℕ) : exp (n : ℝ) ≤ 2.7182818286 ^ n := by
  rw [← exp_one_pow]; exact pow_le_pow_left₀ (exp_pos 1).le e_lt.le n

lemma exp_nat_ge (n : ℕ) : 2.7182818283 ^ n ≤ exp (n : ℝ) := by
  rw [← exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) e_gt.le n

/-- The bracket of (121) at `δ = 1.478`: if `45.05 ≤ δ log ℓ ≤ 46`, then
`3·5·…·53 ≤ ℓ^δ < 3·5·…·59`, so `p̄ = 53` and `ε₂ = 1/51`. -/
lemma bracket53 (ℓ : ℝ) (hℓ : 0 < ℓ) (h1 : 45 ≤ 1.478 * log ℓ) (h2 : 1.478 * log ℓ ≤ 46) :
    (oddPrimorial 53 : ℝ) ≤ ℓ ^ (1.478 : ℝ) ∧ ℓ ^ (1.478 : ℝ) < (oddPrimorial 59 : ℝ) := by
  rw [rpow_def_of_pos hℓ, oddPrimorial_53, oddPrimorial_59]
  have hm : log ℓ * 1.478 = 1.478 * log ℓ := mul_comm _ _
  rw [hm]
  have a1 := exp_nat_ge 45
  have a2 := exp_nat_le 46
  have b1 : exp ((45 : ℕ) : ℝ) ≤ exp (1.478 * log ℓ) := exp_le_exp.mpr (by push_cast; linarith)
  have b2 : exp (1.478 * log ℓ) ≤ exp ((46 : ℕ) : ℝ) := exp_le_exp.mpr (by push_cast; linarith)
  push_cast at a1 a2 b1 b2
  have c1 : (16294579238595022365 : ℝ) ≤ 2.7182818283 ^ 45 := by norm_num
  have c2 : (2.7182818286 : ℝ) ^ 46 < 961380175077106319535 := by norm_num
  constructor
  · push_cast; linarith
  · push_cast; linarith

lemma exp_big (x : ℝ) (hx : 30 ≤ x) : 10 ^ 13 ≤ exp x := by
  have h := exp_nat_ge 30
  have : exp ((30 : ℕ) : ℝ) ≤ exp x := exp_le_exp.mpr (by push_cast; linarith)
  push_cast at h this
  have h2 : (10 : ℝ) ^ 13 ≤ 2.7182818283 ^ 30 := by norm_num
  linarith

/-- **F-0022, PROVED: `p̄ = 53` at `Y = X₃ = exp(exp 30.62)`.** Here
`log x₂(X₃) = e^{30.62} - 15 · 30.62`, from (75). -/
theorem pbar_X3 :
    let ℓ := exp (3062 / 100) - 15 * (3062 / 100)
    (oddPrimorial 53 : ℝ) ≤ ℓ ^ (1.478 : ℝ) ∧ ℓ ^ (1.478 : ℝ) < (oddPrimorial 59 : ℝ) := by
  intro ℓ
  have hE := exp_big (3062 / 100) (by norm_num)
  have hpos : 0 < ℓ := by simp only [ℓ]; linarith
  have hlo : exp (3062 / 100) * (9 / 10) ≤ ℓ := by simp only [ℓ]; nlinarith
  have hhi : ℓ ≤ exp (3062 / 100) := by simp only [ℓ]; linarith
  have l1 : log ℓ ≤ 3062 / 100 := by
    rw [← log_exp (3062 / 100 : ℝ)]; exact log_le_log hpos hhi
  have l2 : 3062 / 100 + log (9 / 10) ≤ log ℓ := by
    rw [← log_exp (3062 / 100 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log (by positivity) hlo
  have l3 : -(1 / 9 : ℝ) ≤ log (9 / 10) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (9 / 10 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  exact bracket53 ℓ hpos (by linarith) (by linarith)

/-- **F-0022, PROVED: `p̄ = 53` at `Y = X₂^{1/8}`, `X₂ = exp(exp 32.7)`.** Here
`log x₂(Y) = e^{32.7}/8 - 15 (32.7 - 3 log 2)`, from (75), and `log log Y = 32.7 - 3 log 2`. -/
theorem pbar_X2_eighth :
    let ℓ := exp (327 / 10) / 8 - 15 * (327 / 10 - 3 * log 2)
    (oddPrimorial 53 : ℝ) ≤ ℓ ^ (1.478 : ℝ) ∧ ℓ ^ (1.478 : ℝ) < (oddPrimorial 59 : ℝ) := by
  intro ℓ
  have hE := exp_big (327 / 10) (by norm_num)
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have hpos : 0 < ℓ := by simp only [ℓ]; nlinarith
  have hlo : exp (327 / 10) * (1 / 9) ≤ ℓ := by simp only [ℓ]; nlinarith
  have hhi : ℓ ≤ exp (327 / 10) * (1 / 8) := by simp only [ℓ]; nlinarith
  have l1 : log ℓ ≤ 327 / 10 + log (1 / 8) := by
    rw [← log_exp (327 / 10 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log hpos hhi
  have l2 : 327 / 10 + log (1 / 9) ≤ log ℓ := by
    rw [← log_exp (327 / 10 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log (by positivity) hlo
  have e8 : log (1 / 8 : ℝ) = -(3 * log 2) := by
    rw [one_div, log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; ring
  have e9 : log (1 / 9 : ℝ) = -(2 * log 3) := by
    rw [one_div, log_inv, show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]; push_cast; ring
  have l3 := log_three_lt_d9
  rw [e8] at l1; rw [e9] at l2
  norm_num at l2a l3
  exact bracket53 ℓ hpos (by nlinarith) (by nlinarith)

end LeanLab.ChenExplicit.BJS51
