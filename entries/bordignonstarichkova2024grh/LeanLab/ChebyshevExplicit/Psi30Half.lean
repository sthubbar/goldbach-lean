module

public import LeanLab.ChebyshevExplicit.ComboHalf

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.
Solve the improved recurrence from ComboHalf with half the logarithmic error.
The finite base range closes the recurrence below thirty.
Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- The sharper step halves the quadratic and linear logarithmic errors. -/
theorem psi_le_chebyshev30_half (n : ℕ) :
    ψ n ≤ 6 / 5 * A * n + 5 / (4 * log 6) * log n ^ 2 + 5 / 4 * log n + 10 := by
  have h6 : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have hb : 0 < (5 : ℝ) / (4 * log 6) := by positivity
  have h6le : log (6 : ℝ) ≤ 2 := by
    have h : log ((6 : ℝ) ^ 3) ≤ log ((2 : ℝ) ^ 8) :=
      log_le_log (by norm_num) (by norm_num)
    rw [log_pow, log_pow] at h
    norm_num at h
    linarith [log_two_lt_d9]
  have hb58 : (5 / 8 : ℝ) ≤ 5 / (4 * log 6) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hlogn0 := log_natCast_nonneg n
    by_cases hn : n < 30
    · have hAn := mul_le_mul_of_nonneg_right A_gt.le hn0
      have hs := mul_le_mul_of_nonneg_right hb58 (sq_nonneg (log (n : ℝ)))
      by_cases hn15 : n < 15
      · have hpc : Nat.primeCounting n ≤ 6 := by
          calc Nat.primeCounting n ≤ Nat.primeCounting 14 :=
                Nat.monotone_primeCounting (by omega)
            _ ≤ 6 := by decide
        have hpcR : (Nat.primeCounting n : ℝ) ≤ 6 := by exact_mod_cast hpc
        have hp : ψ n ≤ 6 * log n := (psi_le_primeCounting_mul_log n).trans
          (mul_le_mul_of_nonneg_right hpcR hlogn0)
        nlinarith [sq_nonneg (log (n : ℝ) - 4)]
      push Not at hn15
      have hn15R : (15 : ℝ) ≤ n := by exact_mod_cast hn15
      have hpc : Nat.primeCounting n ≤ 10 := by
        calc Nat.primeCounting n ≤ Nat.primeCounting 29 :=
              Nat.monotone_primeCounting (by omega)
          _ ≤ 10 := by decide
      have hpcR : (Nat.primeCounting n : ℝ) ≤ 10 := by exact_mod_cast hpc
      have hp : ψ n ≤ 10 * log n := (psi_le_primeCounting_mul_log n).trans
        (mul_le_mul_of_nonneg_right hpcR hlogn0)
      have hl15 : (7 : ℝ) / 2 * log 2 ≤ log 15 :=
        log_ge_of_pow 15 7 2 (by norm_num) (by norm_num)
      have hll : (2.4 : ℝ) ≤ log (n : ℝ) := by
        have h := log_le_log (by norm_num : (0 : ℝ) < 15) hn15R
        linarith [log_two_gt_d9]
      have hlu : log (n : ℝ) ≤ 3.4 := by
        have hh : log ((29 : ℝ) ^ 8) ≤ log ((2 : ℝ) ^ 39) :=
          log_le_log (by norm_num) (by norm_num)
        rw [log_pow, log_pow] at hh
        norm_num at hh
        have hn29R : (n : ℝ) ≤ 29 := by exact_mod_cast (by omega : n ≤ 29)
        have h := log_le_log (by linarith : (0 : ℝ) < n) hn29R
        linarith [log_two_lt_d9]
      have hs24 : (2.4 : ℝ) ^ 2 ≤ log (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hll 2
      nlinarith
    push Not at hn
    set m := n / 6 with hm
    have hmn : m < n := by omega
    have ihm := ih m hmn
    have hstep := psi_sub_psi_div6_le_half n hn
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
    have herr : 5 / (4 * log 6) * log m ^ 2 + 5 / 4 * log m + 5 / 2 * log n ≤
        5 / (4 * log 6) * log n ^ 2 + 5 / 4 * log n := by
      calc
        _ ≤ 5 / (4 * log 6) * (log n - log 6) ^ 2
            + 5 / 4 * (log n - log 6) + 5 / 2 * log n := by nlinarith
        _ = _ := by field_simp; ring
    have hAm : 6 / 5 * A * (m : ℝ) ≤ 1 / 5 * A * n := by nlinarith [A_pos]
    nlinarith

end LeanLab.ChebyshevExplicit
