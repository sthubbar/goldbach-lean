module

public import LeanLab.ChebyshevExplicit.SharperConstants

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.
An exact quadratic error for the existing Chebyshev recurrence.
This bound is derived from the local recurrence, not quoted from a paper.
Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Solve the existing recurrence with its exact quadratic logarithmic error. -/
theorem psi_le_chebyshev30_refined (n : ℕ) :
    ψ n ≤ 6 / 5 * A * n + 5 / (2 * log 6) * log n ^ 2 + 5 / 2 * log n + 10 := by
  have h6 : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have hb : 0 < (5 : ℝ) / (2 * log 6) := by positivity
  have h6le : log (6 : ℝ) ≤ 2 := by
    have h : log ((6 : ℝ) ^ 3) ≤ log ((2 : ℝ) ^ 8) :=
      log_le_log (by norm_num) (by norm_num)
    rw [log_pow, log_pow] at h
    norm_num at h
    linarith [log_two_lt_d9]
  have hb125 : (5 / 4 : ℝ) ≤ 5 / (2 * log 6) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hlogn0 := log_natCast_nonneg n
    by_cases hn : n < 30
    · by_cases hn2 : n < 2
      · interval_cases n <;> simp <;> linarith [A_pos]
      have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      have hpc : Nat.primeCounting n ≤ 10 := by
        calc Nat.primeCounting n ≤ Nat.primeCounting 29 :=
              Nat.monotone_primeCounting (by omega)
          _ ≤ 10 := by decide
      have hpcR : (Nat.primeCounting n : ℝ) ≤ 10 := by exact_mod_cast hpc
      have hp : ψ n ≤ 10 * log n := (psi_le_primeCounting_mul_log n).trans
        (mul_le_mul_of_nonneg_right hpcR hlogn0)
      have hAn := mul_le_mul_of_nonneg_right A_gt.le hn0
      have hs := mul_le_mul_of_nonneg_right hb125 (sq_nonneg (log (n : ℝ)))
      nlinarith [sq_nonneg (log (n : ℝ) - 3)]
    push Not at hn
    set m := n / 6 with hm
    have hmn : m < n := by omega
    have ihm := ih m hmn
    have hstep := psi_sub_psi_div6_le n hn
    have hm1 : 1 ≤ m := by omega
    have hmR : (m : ℝ) * 6 ≤ n := by exact_mod_cast (by omega : m * 6 ≤ n)
    have hlogm0 := log_natCast_nonneg m
    have hlogm : log m ≤ log n - log 6 := by
      rw [← log_div (by positivity : (n : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0)]
      apply log_le_log (by exact_mod_cast (by omega : 0 < m))
      rw [le_div_iff₀ (by norm_num)]
      exact hmR
    have hs : log m ^ 2 ≤ (log n - log 6) ^ 2 :=
      pow_le_pow_left₀ hlogm0 hlogm 2
    have herr : 5 / (2 * log 6) * log m ^ 2 + 5 / 2 * log m + 5 * log n ≤
        5 / (2 * log 6) * log n ^ 2 + 5 / 2 * log n := by
      calc
        _ ≤ 5 / (2 * log 6) * (log n - log 6) ^ 2
            + 5 / 2 * (log n - log 6) + 5 * log n := by
          nlinarith
        _ = _ := by field_simp; ring
    have hAm : 6 / 5 * A * (m : ℝ) ≤ 1 / 5 * A * n := by
      nlinarith [A_pos]
    nlinarith

/-- The refined recurrence bound with a rational linear coefficient. -/
theorem psi_le_110556_refined (n : ℕ) :
    ψ n ≤ 1.10556 * n + 5 / (2 * log 6) * log n ^ 2 + 5 / 2 * log n + 10 := by
  have h := psi_le_chebyshev30_refined n
  have hA := A_lt_09213
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- A refined theta bound valid throughout a real Abel summation interval. -/
theorem theta_le_110556_refined_real {x : ℝ} (hx : 2 ≤ x) :
    θ x ≤ 1.10556 * x + 5 / (2 * log 6) * log x ^ 2 + 5 / 2 * log x + 10 := by
  have hf1 : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfR : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf1
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hl0 : 0 ≤ log (⌊x⌋₊ : ℝ) := log_nonneg hfR
  have hl : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log (by linarith) hfx
  have hs := pow_le_pow_left₀ hl0 hl 2
  have hb : 0 ≤ (5 : ℝ) / (2 * log 6) := by positivity
  have hbs := mul_le_mul_of_nonneg_left hs hb
  calc
    θ x = θ (⌊x⌋₊ : ℝ) := theta_eq_theta_coe_floor x
    _ ≤ ψ (⌊x⌋₊ : ℝ) := theta_le_psi _
    _ ≤ 1.10556 * (⌊x⌋₊ : ℝ) + 5 / (2 * log 6) * log (⌊x⌋₊ : ℝ) ^ 2
        + 5 / 2 * log (⌊x⌋₊ : ℝ) + 10 := psi_le_110556_refined _
    _ ≤ _ := by nlinarith

end LeanLab.ChebyshevExplicit
