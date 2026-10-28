module

public import LeanLab.ChebyshevExplicit.Psi30Refined
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.
Half-log factorial bounds derived from Mathlib's Stirling proofs.
These helper constants are derived here and are not paper transcriptions.
Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- A natural-input upper Stirling bound with constant one. -/
theorem log_factorial_le_half (n : ℕ) (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * log n - n + log n / 2 + 1 := by
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
  change log (Stirling.stirlingSeq ((n - 1) + 1)) ≤ log (Stirling.stirlingSeq 1) at h
  rw [Nat.sub_add_cancel hn] at h
  have h1 : log (Stirling.stirlingSeq 1) = 1 - log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, log_div (by positivity) (by positivity), log_exp,
      log_sqrt (by norm_num)]
  rw [Stirling.log_stirlingSeq_formula, h1,
    log_mul (by norm_num) (by exact_mod_cast (by omega : n ≠ 0)),
    log_div (by exact_mod_cast (by omega : n ≠ 0)) (by positivity), log_exp] at h
  nlinarith

/-- The upper half-log bound at a real input and its natural floor. -/
theorem log_factorial_floor_le_half {x : ℝ} (hx : 1 ≤ x) :
    log (⌊x⌋₊.factorial : ℝ) ≤ x * log x - x + log x / 2 + 1 := by
  have hn : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hnR : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by linarith
  have hx0 : 0 < x := by linarith
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hln0 : 0 ≤ log (⌊x⌋₊ : ℝ) := log_nonneg hnR
  have hln : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log hn0 hnx
  have hratio := log_le_sub_one_of_pos (div_pos hn0 hx0)
  rw [log_div hn0.ne' hx0.ne'] at hratio
  have hscaled := mul_le_mul_of_nonneg_left hratio hx0.le
  have hcancel : x * ((⌊x⌋₊ : ℝ) / x - 1) = (⌊x⌋₊ : ℝ) - x := by
    field_simp
  rw [hcancel] at hscaled
  have hcore : (⌊x⌋₊ : ℝ) * log (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) ≤ x * log x - x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnx) hln0]
  exact (log_factorial_le_half ⌊x⌋₊ hn).trans (by linarith)

/-- A natural-input lower Stirling bound with a rational constant. -/
theorem le_log_factorial_half (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * log n - n + log n / 2 + 0.8 ≤ log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (by omega : n ≠ 0)
  have h6 : (5 : ℝ) / 2 * log 2 ≤ log 6 :=
    log_ge_of_pow 6 5 2 (by norm_num) (by norm_num)
  have hpi : log (6 : ℝ) ≤ log (2 * Real.pi) :=
    log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have hc : (0.8 : ℝ) ≤ log (2 * Real.pi) / 2 := by
    nlinarith [log_two_gt_d9]
  linarith

/-- The lower half-log bound at a real input and its natural floor. -/
theorem le_log_factorial_floor_half {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x - log x / 2 + 0.8 ≤ log (⌊x⌋₊.factorial : ℝ) := by
  have hx0 : 0 < x := by linarith
  by_cases hx2 : x < 2
  · have hratio := log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : ℝ) < 2))
    rw [log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hratio
    have hl : log x ≤ x / 2 - 0.3 := by linarith [log_two_lt_d9]
    have hp := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ x - 1 / 2)
    have hq := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ x - 1) (by linarith : x - 2 ≤ 0)
    have ht : x * log x - x - log x / 2 + 0.8 ≤ 0 := by nlinarith
    exact ht.trans (log_natCast_nonneg _)
  push Not at hx2
  set m := ⌊x⌋₊ + 1 with hm
  have hf2 : (2 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; exact hx2)
  have hm3 : 3 ≤ m := by omega
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hmx : x ≤ (m : ℝ) := by
    have h := (Nat.lt_floor_add_one x).le
    simpa [hm, Nat.cast_add, Nat.cast_one] using h
  have hlm : 1 ≤ log (m : ℝ) := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  have hl : log x ≤ log (m : ℝ) := log_le_log hx0 hmx
  have hg : x * log x - x - log x / 2 ≤
      (m : ℝ) * log m - m - log m / 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hmx) (sub_nonneg.mpr hlm)
    have hq := mul_nonneg (by linarith : 0 ≤ x - 1 / 2) (sub_nonneg.mpr hl)
    nlinarith
  have hn := le_log_factorial_half m (by omega)
  have heq : log (m.factorial : ℝ) = log (m : ℝ) + log (⌊x⌋₊.factorial : ℝ) := by
    rw [hm, Nat.factorial_succ, Nat.cast_mul,
      log_mul (by positivity) (by positivity)]
  rw [heq] at hn
  linarith

end LeanLab.ChebyshevExplicit
