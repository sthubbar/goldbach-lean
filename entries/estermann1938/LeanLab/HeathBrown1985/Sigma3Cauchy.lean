module

public import Mathlib
public import LeanLab.HeathBrown1985.Sigma3

/-!
P0096 Heath-Brown 1985, pages 55 to 56, the Cauchy step 3.5 for Σ₃ over the full range of `n`:
`|S₃| ≤ Σ_n Λ(n) |Σ_r d_r f(rn)|`, hence
`Σ₃² ≤ (Σ_{m,n} Λ(n)²) · Σ_{m,n} |Σ_r d_r f_m(rn)|²`.
PROVED here, zero sorry.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- The inner `r` sum `T(n) = Σ_{u < r, rn ≤ N} d_r f(rn)` for `n > v`. -/
def T3 (U V N : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 N, if U < r ∧ V < n ∧ r * n ≤ N then dr U r * f (r * n) else 0

/-- `|S₃| ≤ Σ_n Λ(n) |T(n)|`. -/
theorem abs_S3_le (U V N : ℕ) (f : ℕ → ℝ) :
    |S3 U V N f| ≤ ∑ n ∈ Icc 1 N, Λ n * |T3 U V N f n| := by
  unfold S3
  rw [sum_comm]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  have e : ∑ r ∈ Icc 1 N, (if U < r ∧ V < n ∧ r * n ≤ N then dr U r * Λ n * f (r * n) else 0) =
      Λ n * T3 U V N f n := by
    unfold T3
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    split_ifs <;> ring
  rw [e, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- 3.5, full range: `Σ₃² ≤ (Σ_{m,n} Λ(n)²) · Σ_{m,n} T_m(n)²`. -/
theorem sigma3_sq_le_cauchy (x Q : ℝ) :
    Sigma3 x Q ^ 2 ≤
      (∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊, Λ n ^ 2) *
        ∑ m ∈ mRange x, ∑ n ∈ Icc 1 ⌊3 * x⌋₊,
          T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m) n ^ 2 := by
  set N := ⌊3 * x⌋₊
  set T := fun p : ℕ × ℕ => T3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ N (fm x Q p.1) p.2
  have h1 : Sigma3 x Q ≤ ∑ p ∈ mRange x ×ˢ Icc 1 N, Λ p.2 * |T p| := by
    rw [sum_product]
    unfold Sigma3
    exact sum_le_sum fun m _ => abs_S3_le _ _ _ _
  have h0 : 0 ≤ Sigma3 x Q := sum_nonneg (fun _ _ => abs_nonneg _)
  have h2 := cauchy_abs (mRange x ×ˢ Icc 1 N) (fun p => Λ p.2) T
  rw [sum_product, sum_product] at h2
  exact (pow_le_pow_left₀ h0 h1 2).trans (by rw [sum_product] at *; exact h2)

end LeanLab.HeathBrown1985
