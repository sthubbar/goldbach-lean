module

public import LeanLab.ChebyshevExplicit.PiUpperSharp

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.
Rational bounds derived from the existing definition of Chebyshev's constant.
No cited hypothesis is used. Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 4096 in
/-- A certified upper enclosure for the existing exact constant A. -/
theorem A_lt_09213 : A < 0.9213 := by
  have h2 := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ 485 / 306 * Real.log 2 := by
    have h : Real.log ((3 : ℝ) ^ 306) ≤ Real.log ((2 : ℝ) ^ 485) :=
      Real.log_le_log (by positivity) (by
        exact_mod_cast (show (3 : ℕ) ^ 306 ≤ 2 ^ 485 by decide))
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have h5 : Real.log 5 ≤ 815 / 351 * Real.log 2 := by
    have h : Real.log ((5 : ℝ) ^ 351) ≤ Real.log ((2 : ℝ) ^ 815) :=
      Real.log_le_log (by positivity) (by
        exact_mod_cast (show (5 : ℕ) ^ 351 ≤ 2 ^ 815 by decide))
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold A
  rw [h30]
  linarith

/-- A smaller linear coefficient in the existing explicit psi bound. -/
theorem psi_le_110556 (n : ℕ) :
    ψ n ≤ 1.10556 * n + 2 * log n ^ 2 + 160 := by
  have hp := psi_le_chebyshev30 n
  have hA := A_lt_09213
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

end LeanLab.ChebyshevExplicit
