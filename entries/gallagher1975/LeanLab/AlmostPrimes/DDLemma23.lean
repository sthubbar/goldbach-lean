module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T1203Z-2488, unit U-0947.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
Lemma 2.3 and its proof, read in Claude in Chrome on arxiv.org/html/2602.22720.

Lemma 2.3: `R₄(A, z^{18.4}) < 0.591 z^{18.4} log⁸ z` for `z ≥ 10¹⁰`. The proof by Rankin's trick
ends with (5), `R₄(A, D) < D log⁸ z exp(2.1072 + 8α e^α - α log D / log z)`, at
`log D / log z = 18.4` and `α = 0.457`.
PROVED:
* `const_2_1072`: `8 · 0.2634 = 2.1072`, the Rosser-Schoenfeld constant times 8, MATCH.
* `exp_le_one_add_mul_exp`: `e^x ≤ 1 + x e^x` for every real `x`, the step `e^{η log p} ≤ 1 + η log p z^η`.
* `lemma2_3_const`: `exp(2.1072 + 8 · 0.457 · e^{0.457} - 18.4 · 0.457) < 0.591`; the value is
  about 0.59014, MATCH.
* `alpha_near_opt`: `e^α (1 + α)` is within 0.002 of `2.3` at `α = 0.457`, so 0.457 is close
  to the optimal α.
The Rosser-Schoenfeld inputs stay cited. Goldbach is open.
-/

@[expose] public section

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.DDLemma23

theorem const_2_1072 : 8 * (0.2634 : ℝ) = 2.1072 := by norm_num

/-- `e^x ≤ 1 + x e^x` for every real `x`. -/
theorem exp_le_one_add_mul_exp (x : ℝ) : exp x ≤ 1 + x * exp x := by
  have h := Real.add_one_le_exp (-x)
  have hp := exp_pos x
  have e : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  nlinarith

lemma exp0457_le : exp (0.457 : ℝ) ≤ 1.5794 := by
  have h := Real.exp_bound' (x := (0.457 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

lemma exp0457_ge : (1.5793 : ℝ) ≤ exp 0.457 := by
  have h := Real.sum_le_exp_of_nonneg (x := (0.457 : ℝ)) (by norm_num) 8
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

/-- **Lemma 2.3's constant**, MATCH. -/
theorem lemma2_3_const :
    exp (2.1072 + 8 * 0.457 * exp 0.457 - 18.4 * 0.457) < (0.591 : ℝ) := by
  have h1 := exp0457_le
  have hE : 2.1072 + 8 * 0.457 * exp 0.457 - 18.4 * 0.457 ≤ (-0.5273 : ℝ) := by
    norm_num; nlinarith
  have h2 : (1.6943 : ℝ) ≤ exp 0.5273 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.5273 : ℝ)) (by norm_num) 10
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have h3 : exp (2.1072 + 8 * 0.457 * exp 0.457 - 18.4 * 0.457) ≤ (exp 0.5273)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have h4 : (exp 0.5273)⁻¹ ≤ (1.6943 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have : (1.6943 : ℝ)⁻¹ < 0.591 := by norm_num
  linarith

/-- `α = 0.457` nearly solves `8 e^α (1 + α) = 18.4`, the optimum of `8α e^α - 18.4 α`. -/
theorem alpha_near_opt :
    |exp (0.457 : ℝ) * (1 + 0.457) - 2.3| < 0.002 := by
  have h1 := exp0457_le
  have h2 := exp0457_ge
  rw [abs_lt]; constructor <;> nlinarith

end LeanLab.AlmostPrimes.DDLemma23
