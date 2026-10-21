module

public import LeanLab.Schnirelmann.Inequality

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Explicit Schnirelmann basis theorem: if `0 ∈ A`, `α ≤ σ(A)` and `1 ≤ α * m`, then
`(2 * m) • A = ℕ`. This names the order `h` that `LeanLab.Schnirelmann.exists_nsmul_eq_univ`
leaves existential. Uses `(1 - α)^m ≤ exp(-α m) ≤ exp(-1) < 1/2`.
-/

@[expose] public section

open Finset
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit

open LeanLab.Schnirelmann

/-- **Explicit basis theorem.** If `0 ∈ A`, `α ≤ σ(A)` and `α * m ≥ 1`, then every natural
number is a sum of `2 m` elements of `A`. -/
theorem nsmul_eq_univ_of_le_density (A : Set ℕ) (hA : 0 ∈ A) (α : ℝ)
    (hσ : α ≤ schnirelmannDensity A) (m : ℕ) (hm : 1 ≤ α * m) :
    (2 * m) • A = Set.univ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    rcases m with _ | k
    · simp at hm; linarith
    · exact ⟨k, rfl⟩
  have hσ1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
  have h0 : 0 ≤ 1 - schnirelmannDensity A := by linarith
  have hd := one_sub_density_nsmul_le A hA k
  have hexp : (1 - schnirelmannDensity A) ^ (k + 1) ≤ 1 / 2 := by
    calc (1 - schnirelmannDensity A) ^ (k + 1) ≤ (Real.exp (-α)) ^ (k + 1) := by
          gcongr
          exact (by linarith : 1 - schnirelmannDensity A ≤ 1 - α).trans
            (Real.one_sub_le_exp_neg α)
      _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-α)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-1) := by
          apply Real.exp_le_exp.mpr
          push_cast at hm ⊢
          linarith
      _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le
  rw [two_mul, add_nsmul]
  apply add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
    (zero_mem_nsmul A hA _) (zero_mem_nsmul A hA _)
  linarith

end LeanLab.SchnirelmannExplicit
