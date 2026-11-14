module

public import LeanLab.Perelli1996.Section2

/-!
P0083 Perelli 1996, page 480. Unchanged definitions moved from Decomp88.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Decomp88
open Finset Real Polynomial MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

/-- The prime sum S on page 480, with integer cutoff M. -/
def primeSum (M : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ range (M + 1), (Λ n : ℂ) * Kernel.e ((n : ℝ) * α)

/-- The primary major arcs modulo one, page 480, radius L to the B over N. -/
def majorArcs (N B : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.log N ^ B ∧
    ∃ a : ℤ, Nat.Coprime a.natAbs q ∧ |α - (a : ℝ) / q| ≤ Real.log N ^ B / N}

/-- The primary minor arcs on the unit interval, page 480. -/
def minorArcs (N B : ℝ) : Set ℝ := Set.Icc 0 1 \ majorArcs N B

/-- The coefficient integrand in equation 1. -/
def coefficientIntegrand (M m : ℕ) (α : ℝ) : ℂ :=
  primeSum M α ^ 2 * Kernel.e (-(m : ℝ) * α)

/-- The major arc mean square in equation 1. -/
def majorError (F : ℤ[X]) (M : ℕ) (N H B : ℝ) : ℝ :=
  ∑ n ∈ win F N H,
    ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B, coefficientIntegrand M (Fv F n).toNat α) -
      ((Fv F n : ℝ) * Sing (Fv F n).toNat : ℂ)‖ ^ 2

/-- The minor arc mean square in equation 1. -/
def minorError (F : ℤ[X]) (M : ℕ) (N H B : ℝ) : ℝ :=
  ∑ n ∈ win F N H,
    ‖∫ α in minorArcs N B, coefficientIntegrand M (Fv F n).toNat α‖ ^ 2

/-- The two Farey orders on page 480. This is the smaller order Q. -/
def fareyOrder (F : ℤ[X]) (N H B : ℝ) : ℝ :=
  Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) / 2

/-- The punctured Farey interval used in equations 14 and 16. -/
def puncturedArc (N B Q : ℝ) (q : ℕ) (a : ℤ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * Q))
    ((a : ℝ) / q + 1 / ((q : ℝ) * Q)) \ majorArcs N B

/-- The largest local second moment needed in equation 14. -/
def localMass (M : ℕ) (N B Q : ℝ) : ℝ :=
  sSup {x | ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ a : ℤ,
    Nat.Coprime a.natAbs q ∧ x = ∫ α in puncturedArc N B Q q a, ‖primeSum M α‖ ^ 2}

/-- The exact remainder after subtracting the principal kernel in equation 15. -/
def characterRemainder (M q : ℕ) (a : ℤ) (η : ℝ) : ℂ :=
  primeSum M ((a : ℝ) / q + η) -
    ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η

end
end LeanLab.Perelli1996.Decomp88
