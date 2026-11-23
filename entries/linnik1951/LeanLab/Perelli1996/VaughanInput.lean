module

public import LeanLab.Perelli1996.Section2

/-!
P0083, page 482. The divisor second moment input cited to Vaughan, page 120.
The full input is a Prop. The degree one case is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Section2
open Finset Real Polynomial

/-- The k-fold divisor function as a Dirichlet convolution power. -/
def divisorCount (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n

/-- Cited divisor second moment used after equation 7, with the O constant explicit. -/
def DivisorSecondMoment (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Icc 1 ⌊x⌋₊, (divisorCount k n : ℝ) ^ 2 ≤
      C * x * (Real.log (Real.exp 1 * x)) ^ (k ^ 2 - 1)

/-- The divisor second moment at k equal one has constant one. -/
theorem divisorSecondMoment_one : DivisorSecondMoment 1 := by
  refine ⟨1, by norm_num, fun x hx => ?_⟩
  have hsum : ∑ n ∈ Icc 1 ⌊x⌋₊, (divisorCount 1 n : ℝ) ^ 2 = (⌊x⌋₊ : ℝ) := by
    calc ∑ n ∈ Icc 1 ⌊x⌋₊, (divisorCount 1 n : ℝ) ^ 2
        = ∑ _n ∈ Icc 1 ⌊x⌋₊, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          simp [divisorCount, ArithmeticFunction.zeta_apply_ne hn0]
      _ = (⌊x⌋₊ : ℝ) := by simp
  rw [hsum]
  norm_num
  exact Nat.floor_le (by linarith)

end LeanLab.Perelli1996.Section2
