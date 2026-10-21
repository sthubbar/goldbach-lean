module

public import Mathlib
public import LeanLab.GoldbachAverage.Statements

/-!
Elementary identities for average Goldbach representations, all proved.
`∑_{n ≤ N} G(n) = ∑_{a ≤ N} Λ(a) ψ(N - a)`, hence `∑_{n ≤ N} G(n) ≤ ψ(N)²`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `ψ` on naturals, as a sum from `0`; equals Mathlib's `Chebyshev.psi` below. -/
def psiN (m : ℕ) : ℝ := ∑ b ∈ range (m + 1), Λ b

theorem psiN_eq (m : ℕ) : psiN m = Chebyshev.psi m := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, psiN, Nat.range_succ_eq_Icc_zero]

theorem G_eq (n : ℕ) : G n = ∑ a ∈ range (n + 1), Λ a * Λ (n - a) := by
  rw [G, Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => Λ a * Λ b)]

theorem sum_G (N : ℕ) :
    ∑ n ∈ range (N + 1), G n = ∑ a ∈ range (N + 1), Λ a * psiN (N - a) := by
  induction N with
  | zero => simp [G_eq, psiN]
  | succ N ih =>
    have hz : psiN (N + 1 - (N + 1)) = 0 := by simp [psiN]
    have hstep : ∀ a ∈ range (N + 1), Λ a * psiN (N + 1 - a)
        = Λ a * psiN (N - a) + Λ a * Λ (N + 1 - a) := by
      intro a ha
      rw [mem_range] at ha
      have : N + 1 - a = (N - a) + 1 := by omega
      rw [this, psiN, sum_range_succ, ← psiN, mul_add]
    rw [sum_range_succ, ih, G_eq, sum_range_succ (fun a => Λ a * psiN (N + 1 - a)) (N + 1),
      sum_range_succ (fun a => Λ a * Λ (N + 1 - a)) (N + 1), hz, mul_zero, add_zero,
      sum_congr rfl hstep, sum_add_distrib]
    simp

theorem psiN_mono {m m' : ℕ} (h : m ≤ m') : psiN m ≤ psiN m' := by
  unfold psiN
  apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
  intro i _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- `∑_{n ≤ N} G(n) ≤ ψ(N)²`. -/
theorem sum_G_le (N : ℕ) : ∑ n ∈ range (N + 1), G n ≤ psiN N ^ 2 := by
  rw [sum_G, sq, psiN, sum_mul]
  apply sum_le_sum
  intro a ha
  rw [mem_range] at ha
  exact mul_le_mul_of_nonneg_left (by rw [← psiN]; exact psiN_mono (by omega)) ArithmeticFunction.vonMangoldt_nonneg

theorem G_nonneg (n : ℕ) : 0 ≤ G n :=
  sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

/-- `∑_{n ≤ 2N} G(n) ≥ ψ(N)²`: every pair `a, b ≤ N` has `a + b ≤ 2N`. -/
theorem sum_G_ge (N : ℕ) : psiN N ^ 2 ≤ ∑ n ∈ range (2 * N + 1), G n := by
  rw [sum_G, sq, psiN, sum_mul]
  have hsub : range (N + 1) ⊆ range (2 * N + 1) := range_subset_range.mpr (by omega)
  calc ∑ a ∈ range (N + 1), Λ a * ∑ b ∈ range (N + 1), Λ b
      ≤ ∑ a ∈ range (N + 1), Λ a * psiN (2 * N - a) := by
        apply sum_le_sum
        intro a ha
        rw [mem_range] at ha
        exact mul_le_mul_of_nonneg_left (by rw [← psiN]; exact psiN_mono (by omega))
          ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ a ∈ range (2 * N + 1), Λ a * psiN (2 * N - a) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))

end LeanLab.GoldbachAverage
