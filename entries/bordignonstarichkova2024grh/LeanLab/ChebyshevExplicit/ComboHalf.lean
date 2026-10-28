module

public import LeanLab.ChebyshevExplicit.LogFactorialHalf

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.
Tighten the existing five-factorial combination with half-log bounds.
This is a derivation from local proofs and not a paper transcription.
Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- The half-log bounds reduce the five-factorial combination error to 2.5 log n. -/
theorem combo_le_half (n : ℕ) (hn : 30 ≤ n) :
    log (n.factorial : ℝ) - log ((n / 2).factorial : ℝ)
      - log ((n / 3).factorial : ℝ) - log ((n / 5).factorial : ℝ)
      + log ((n / 30).factorial : ℝ) ≤ A * n + 5 / 2 * log n := by
  have hnR : (30 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have u1 := log_factorial_floor_le_half (x := (n : ℝ)) (by linarith)
  have u30 := log_factorial_floor_le_half (x := (n : ℝ) / (30 : ℕ)) (by
    push_cast
    rw [le_div_iff₀ (by norm_num)]
    simpa using hnR)
  have l2 := le_log_factorial_floor_half (x := (n : ℝ) / (2 : ℕ)) (by push_cast; linarith)
  have l3 := le_log_factorial_floor_half (x := (n : ℝ) / (3 : ℕ)) (by push_cast; linarith)
  have l5 := le_log_factorial_floor_half (x := (n : ℝ) / (5 : ℕ)) (by push_cast; linarith)
  rw [Nat.floor_natCast] at u1
  rw [Nat.floor_div_eq_div] at u30 l2 l3 l5
  push_cast at u30 l2 l3 l5
  rw [log_div hn0.ne' (by norm_num)] at u30 l2 l3 l5
  have h30 : log (30 : ℝ) = log 2 + log 3 + log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
      log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num)]
  have hl30 : 0 ≤ log (30 : ℝ) := log_nonneg (by norm_num)
  unfold A
  rw [h30] at u30 hl30
  nlinarith

/-- The improved recurrence step for psi. -/
theorem psi_sub_psi_div6_le_half (n : ℕ) (hn : 30 ≤ n) :
    ψ n - ψ ((n / 6 : ℕ) : ℝ) ≤ A * n + 5 / 2 * log n :=
  (psi_sub_le_combo n).trans (combo_le_half n hn)

end LeanLab.ChebyshevExplicit
