module

public import LeanLab.ChebyshevExplicit.Psi30Half

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.
Close the same recurrence base gap below thirty with an exact lcm certificate.
This permits a quadratic error with no additive constant.
Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

set_option maxRecDepth 4096 in
/-- A kernel-checked base bound for the recurrence whose threshold is thirty. -/
theorem psi_small_le_three_halves_log_two (n : ℕ) (hn : n < 30) :
    ψ n ≤ 3 / 2 * log 2 * n := by
  have hc : (Nat.lcmUpto n) ^ 2 ≤ 2 ^ (3 * n) := by
    interval_cases n <;> decide
  have hpos : (0 : ℝ) < (Nat.lcmUpto n : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
  have h : log ((Nat.lcmUpto n : ℝ) ^ 2) ≤ log ((2 : ℝ) ^ (3 * n)) :=
    log_le_log (by positivity) (by exact_mod_cast hc)
  rw [log_pow, log_pow] at h
  push_cast at h
  rw [psi_eq_log_lcmUpto]
  nlinarith

/-- The improved recurrence needs no additive constant at natural inputs. -/
theorem psi_le_chebyshev30_quadratic (n : ℕ) :
    ψ n ≤ 6 / 5 * A * n + 5 / (4 * log 6) * log n ^ 2 + 5 / 4 * log n := by
  have h6 : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have hb : 0 < (5 : ℝ) / (4 * log 6) := by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hlogn0 := log_natCast_nonneg n
    by_cases hn : n < 30
    · have hs := psi_small_le_three_halves_log_two n hn
      have hc : 3 / 2 * log (2 : ℝ) ≤ 6 / 5 * A := by
        linarith [A_gt, log_two_lt_d9]
      have hmain := mul_le_mul_of_nonneg_right hc hn0
      have hpoly : 0 ≤ 5 / (4 * log (6 : ℝ)) * log n ^ 2 := by positivity
      linarith
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

/-- The quadratic psi bound with rational linear coefficient. -/
theorem psi_le_110556_quadratic (n : ℕ) :
    ψ n ≤ 1.10556 * n + 5 / (4 * log 6) * log n ^ 2 + 5 / 4 * log n := by
  have h := psi_le_chebyshev30_quadratic n
  have hA := A_lt_09213
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- The strongest quadratic theta bound on a real interval. -/
theorem theta_le_110556_quadratic_real {x : ℝ} (hx : 2 ≤ x) :
    θ x ≤ 1.10556 * x + 5 / (4 * log 6) * log x ^ 2 + 5 / 4 * log x := by
  have hf1 : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfR : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf1
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hl0 : 0 ≤ log (⌊x⌋₊ : ℝ) := log_nonneg hfR
  have hl : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log (by linarith) hfx
  have hs := pow_le_pow_left₀ hl0 hl 2
  have hb : 0 ≤ (5 : ℝ) / (4 * log 6) := by positivity
  have hbs := mul_le_mul_of_nonneg_left hs hb
  calc
    θ x = θ (⌊x⌋₊ : ℝ) := theta_eq_theta_coe_floor x
    _ ≤ ψ (⌊x⌋₊ : ℝ) := theta_le_psi _
    _ ≤ 1.10556 * (⌊x⌋₊ : ℝ) + 5 / (4 * log 6) * log (⌊x⌋₊ : ℝ) ^ 2
        + 5 / 4 * log (⌊x⌋₊ : ℝ) := psi_le_110556_quadratic _
    _ ≤ _ := by nlinarith

end LeanLab.ChebyshevExplicit
