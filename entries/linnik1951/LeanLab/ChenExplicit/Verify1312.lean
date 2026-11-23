module

public import LeanLab.ChenExplicit.Printed32155

/-!
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T0103Z-19411, unit U-1312, track T2,
falsifier VERIFY of U-1310, Printed32155.chen_32155_printed.

The three α-free range conditions of BJS Theorems 44, 50, 51 at X₂ = exp(exp 32.155),
X₃ = X₂^{1/8}, which U-1310 checked only numerically, P0009.txt p. 42, p. 51, p. 56:
* `loglog_x1_ge`: log log x₁(X₂) ≥ 10.4, with log x₁(X₂) = e^{32.155} − 5·32.155, (75);
* `Kdelta1_ge`: K_{δ₁}(x₁(X₂)) = log^{1.5026} x₁(X₂) ≥ 3022, (140), (76);
* `loglog_x2_ge`: log log x₂(X₃) ≥ 10.4, Theorem 51, with log x₂(X₃) = log X₃ − 15 log log X₃;
* `Kdelta2_ge3`: K_{δ₂}(x₂(X₃)) ≥ 3, Lemma 41;
* `X3_pow8`: X₃⁸ = X₂, so N > X₃⁸ of Theorem 51 is N > X₂;
* `params_ok`: 0 < δ₁, δ₂ < 2, 0 < ε₀ < 1, 0 < αP < 1/24.
Vacuity of the predicate shapes: `thm44_shape`, `thm50_shape`, `thm51_shape` show Thm44At,
Thm50At, Thm51At are satisfiable for some constant functions, so none is False by construction.
Chen's theorem is not in doubt; Goldbach is open.
-/

@[expose] public section

open Real Finset

noncomputable section
namespace LeanLab.ChenExplicit.Verify1312

open LeanLab.ChenExplicit

abbrev ll : ℝ := 32155 / 1000

lemma exp11_le : exp (11 : ℝ) ≤ 60000 := by
  have e : exp (11 : ℝ) = exp 1 ^ 11 := by rw [← exp_nat_mul]; norm_num
  have h := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 11
  have : (2.7182818286 : ℝ) ^ 11 ≤ 60000 := by norm_num
  rw [e]; linarith

/-- **log log x₁(X₂) ≥ 10.4**, Theorems 44 and 50, pp. 42, 51. -/
theorem loglog_x1_ge : (10.4 : ℝ) ≤ log (exp ll - 5 * ll) := by
  have hE := BJSm32155.exp32155_ge
  have h1 : exp (10.4 : ℝ) ≤ exp ll - 5 * ll := by
    have := exp_le_exp.mpr (show (10.4 : ℝ) ≤ 11 by norm_num)
    have := exp11_le
    norm_num at hE ⊢; linarith
  have := Real.log_le_log (exp_pos _) h1
  rwa [Real.log_exp] at this

/-- **K_{δ₁}(x₁(X₂)) ≥ 3022**, (140), at δ₁ = 1.5026. -/
theorem Kdelta1_ge : (3022 : ℝ) ≤ Eps32155.B1 := by
  have hE := BJSm32155.exp32155_ge
  have h1 : (1 : ℝ) ≤ exp ll - 5 * ll := by norm_num at hE ⊢; linarith
  have h2 : (exp ll - 5 * ll) ^ (1 : ℝ) ≤ (exp ll - 5 * ll) ^ (1.5026 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  rw [Real.rpow_one] at h2
  unfold Eps32155.B1
  have : (3022 : ℝ) ≤ exp ll - 5 * ll := by norm_num at hE ⊢; linarith
  linarith

/-- **log log x₂(X₃) ≥ 10.4**, Theorem 51, p. 56. -/
theorem loglog_x2_ge : (10.4 : ℝ) ≤ log (F0023.ℓP ll) := by
  have := BJSm32155.logℓ_bounds.1
  rw [Eps32155.ℓ_eq] at this
  linarith

/-- **K_{δ₂}(x₂(X₃)) ≥ 3**, Lemma 41, at δ₂ = 1.47088. -/
theorem Kdelta2_ge3 : (3 : ℝ) ≤ Eps32155.B2 := by
  have hb := BJSm32155.ℓ_bounds.1
  have hΛ := BJSm32155.Λ3_ge
  have h0 : (3 : ℝ) ≤ BJSm32155.ℓ := by nlinarith
  rw [Eps32155.ℓ_eq] at h0
  have h2 : F0023.ℓP Eps32155.ll ^ (1 : ℝ) ≤ F0023.ℓP Eps32155.ll ^ (1.47088 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_one] at h2
  exact le_trans h0 h2

/-- **X₃⁸ = X₂** with log X₃ = e^{32.155}/8, F0023.Λ3P. -/
theorem X3_pow8 : exp (F0023.Λ3P ll) ^ 8 = exp (exp ll) := by
  rw [← exp_nat_mul]; unfold F0023.Λ3P; congr 1; push_cast; ring

/-- The parameter ranges of Theorems 44, 50, 51 and of (76), (121). -/
theorem params_ok :
    (0 : ℝ) < 1.5026 ∧ (1.5026 : ℝ) < 2 ∧ (0 : ℝ) < 1.47088 ∧ (1.47088 : ℝ) < 2 ∧
      0 < At32155.ee0 ∧ At32155.ee0 < 1 ∧ 0 < Printed32155.αP ∧ Printed32155.αP < 1 / 24 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-! ### Vacuity of the predicate shapes -/

lemma mainTerm_pos (t : ℝ) (N : ℕ) (hN : exp (exp t) < (N : ℝ)) : 0 < mainTerm N := by
  have h1 : (1 : ℝ) < N := lt_of_le_of_lt (by have := add_one_le_exp (exp t); have := exp_pos t; linarith) hN
  have hl : 0 < Real.log N := Real.log_pos h1
  have hU := U_pos N
  unfold mainTerm
  have : (0 : ℝ) < N := by linarith
  positivity

/-- Thm44At is satisfiable: with cA ≡ −1 it holds. -/
theorem thm44_shape (t : ℝ) : Thm44At t (fun _ => -1) := by
  intro N _ hN
  have := mainTerm_pos t N hN
  have : (0 : ℝ) ≤ (SA N (zN N) : ℝ) := Nat.cast_nonneg _
  linarith

lemma SAq_le (N : ℕ) (z : ℝ) (q : ℕ) : SAq N z q ≤ N := by
  classical
  unfold SAq idxA
  exact (card_filter_le _ _).trans ((card_filter_le _ _).trans (card_range N).le)

lemma sumSAq_le (N : ℕ) (z y : ℝ) : sumSAq N z y ≤ ⌈y⌉₊ * N := by
  unfold sumSAq
  calc ∑ q ∈ qSet N z y, SAq N z q ≤ ∑ _q ∈ qSet N z y, N := sum_le_sum fun q _ => SAq_le N z q
    _ = #(qSet N z y) * N := by rw [sum_const, smul_eq_mul]
    _ ≤ ⌈y⌉₊ * N := by
        apply Nat.mul_le_mul_right
        unfold qSet
        exact (card_filter_le _ _).trans (card_range _).le

/-- Thm50At is satisfiable, with cQ N = (⌈y⌉ N + 1)/mainTerm N. -/
theorem thm50_shape (t : ℝ) :
    Thm50At t (fun N => ((⌈yN N⌉₊ * N : ℕ) + 1 : ℝ) / mainTerm N) := by
  intro N _ hN
  have hM := mainTerm_pos t N hN
  rw [div_mul_cancel₀ _ hM.ne']
  have : (sumSAq N (zN N) (yN N) : ℝ) ≤ ((⌈yN N⌉₊ * N : ℕ) : ℝ) := by
    exact_mod_cast sumSAq_le N (zN N) (yN N)
  linarith

/-- Thm51At is satisfiable, with cB N = (N + 1)/mainTerm N. -/
theorem thm51_shape (t : ℝ) : Thm51At t (fun N => ((N : ℝ) + 1) / mainTerm N) := by
  intro N _ hN
  have hM := mainTerm_pos t N hN
  rw [div_mul_cancel₀ _ hM.ne']
  have : SB N (zN N) (yN N) ≤ N := by
    classical
    unfold SB BSet
    exact (card_filter_le _ _).trans ((card_filter_le _ _).trans (card_range N).le)
  have : (SB N (zN N) (yN N) : ℝ) ≤ N := by exact_mod_cast this
  linarith

end LeanLab.ChenExplicit.Verify1312
