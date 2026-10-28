module

public import LeanLab.ChebyshevExplicit.Psi30Upper

/-!
AI-written Lean code, Claude, 2026-10-20, PC run 20261020T0503Z-11094, unit U-1166.

# An explicit upper bound for π(n) from Chebyshev's θ bound

`pi_le_theta_explicit`: for real `x ≥ 4`,
  `π ⌊x⌋ ≤ θ x / log x + log 4 · (4 x / log² x + √x / log² 2)`.
`pi_le_11062`: for natural `n ≥ 4`,
  `π n ≤ (1.1062 n + 2 log² n + 160) / log n + log 4 · (4 n / log² n + √n / log² 2)`,
so `π(n) ≤ 1.1062 n / log n · (1 + O(1 / log n))` with every constant explicit.

Method: Mathlib's Abel summation `Chebyshev.primeCounting_eq_theta_div_log_add_integral`,
Mathlib's `θ t ≤ log 4 · t` inside the integral, and the split of `∫₂ˣ dt / log² t` at `√x`.
The split lemma `integral_one_div_log_sq_le_explicit` is private in Mathlib, so its proof is
repeated here from `Mathlib/NumberTheory/Chebyshev.lean`, Apache-2.0, Mathlib contributors.
The main term uses the lab's `theta_le_11062`, Psi30Upper.lean.

KNOWN mathematics, Chebyshev 1852 and partial summation. No cited input. Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Monotone bound on `∫ₐᵇ dt / log² t`; repeated from Mathlib, where it is private. -/
theorem integral_one_div_log_sq_le_mono {a b : ℝ} (hab : a ≤ b) (one_lt : 1 < a) :
    ∫ x in a..b, 1 / log x ^ 2 ≤ (b - a) / log a ^ 2 := by
  calc
  _ ≤ ∫ x in a..b, 1 / log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨_, _⟩ ↦ by
        gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq <;> linarith
  _ ≤ _ := by simp [field]

/-- `∫₂ˣ dt / log² t ≤ 4 x / log² x + √x / log² 2` for `x ≥ 4`; repeated from Mathlib. -/
theorem integral_one_div_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, 1 / log t ^ 2 ≤ 4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2 := by
  have two_le_sqrt : 2 ≤ x.sqrt := le_sqrt_of_sq_le <| by norm_num [hx]
  have sqrt_le_x : x.sqrt ≤ x := sqrt_le_left (by linarith) |>.mpr (by bound)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x.sqrt)]
  · grw [integral_one_div_log_sq_le_mono two_le_sqrt (by linarith),
      integral_one_div_log_sq_le_mono sqrt_le_x (by linarith)]
    rw [log_sqrt (by linarith), add_comm, div_pow, ← div_mul, mul_comm, mul_div_assoc]
    norm_num
    gcongr <;> linarith
  all_goals apply intervalIntegrable_one_div_log_sq <;> linarith

/-- The Abel summation integral with `θ t ≤ log 4 · t`. -/
theorem integral_theta_le {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤ log 4 * (4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2) := by
  calc ∫ t in 2..x, θ t / (t * log t ^ 2)
      ≤ ∫ t in 2..x, log 4 * (1 / log t ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun t ⟨ht, _⟩ ↦ ?_
        · rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith),
            ← integrableOn_Icc_iff_integrableOn_Ioc]
          exact integrableOn_theta_div_id_mul_log_sq x
        · refine (intervalIntegrable_one_div_log_sq ?_ ?_).const_mul _ <;> linarith
        · have ht0 : 0 < t := by linarith
          have hl : 0 < log t := log_pos (by linarith)
          calc θ t / (t * log t ^ 2) ≤ log 4 * t / (t * log t ^ 2) := by
                gcongr; exact theta_le_log4_mul_x ht0.le
            _ = log 4 * (1 / log t ^ 2) := by field_simp
    _ = log 4 * ∫ t in 2..x, 1 / log t ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ log 4 * (4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_one_div_log_sq_le hx) (log_pos (by norm_num)).le

/-- Explicit form of `π ⌊x⌋ = θ x / log x + O(x / log² x)`. -/
theorem pi_le_theta_explicit {x : ℝ} (hx : 4 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ θ x / log x + log 4 * (4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2) := by
  rw [primeCounting_eq_theta_div_log_add_integral (by linarith)]
  gcongr
  exact integral_theta_le hx

/-- `π n ≤ (1.1062 n + 2 log² n + 160) / log n + log 4 · (4 n / log² n + √n / log² 2)` for
`n ≥ 4`: Chebyshev's constant `1.1062` in front of `n / log n`, every lower term explicit. -/
theorem pi_le_11062 (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ (1.1062 * n + 2 * log n ^ 2 + 160) / log n
      + log 4 * (4 * n / (log n) ^ 2 + (n : ℝ).sqrt / log 2 ^ 2) := by
  have hx : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h := pi_le_theta_explicit hx
  rw [Nat.floor_natCast] at h
  have hl : 0 < log (n : ℝ) := log_pos (by linarith)
  refine h.trans ?_
  gcongr
  exact theta_le_11062 n

/-- Vacuity: the hypothesis `n ≥ 4` holds at `n = 10⁶`; there the bound evaluates in Python to about `1.12 · 10⁵`, against
`π(10⁶) = 78498`; the hypotheses hold, `n ≥ 4`. -/
theorem pi_le_11062_vacuity : (4 : ℕ) ≤ 10 ^ 6 := by norm_num

end LeanLab.ChebyshevExplicit
