module

public import Mathlib

/-!
# Mann's α + β theorem for Schnirelmann density, Mann 1942

H. B. Mann, *A proof of the fundamental theorem on the density of sums of sets of positive
integers*, Ann. of Math. (2) 43 (1942) 523-527. For sets `A`, `B` of natural numbers containing
`0`, the Schnirelmann density of the sumset satisfies `σ(A + B) ≥ min(1, σ(A) + σ(B))`.

`schnirelmannDensity` is Mathlib's, `Mathlib/Combinatorics/Schnirelmann.lean`, whose TODO list
asks for Mann's theorem; `A + B` is Mathlib's pointwise sum of sets. The target theorems, each
proved in the solution with no assumption beyond those in its statement, are:
* `LeanLab.Schnirelmann.Mann.mann`: Mann's theorem `σ(A + B) ≥ min(1, σ(A) + σ(B))`;
* `LeanLab.Schnirelmann.Mann.mann_sum`: its form for finitely many sets,
  `σ(A_0 + ⋯ + A_h) ≥ min(1, σ(A_0) + ⋯ + σ(A_h))`, where each summand may also be `0`.

The proof goes through the rank `h` case of Dyson's theorem, following M. B. Nathanson,
arXiv:2407.12253. Binary Goldbach is open; nothing here claims it. AI wrote the Lean code.
Lean names keep the namespaces of the lab where the proofs were written.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.Ramare1995.Theorem91

/-- `Rep A k p`: `p` is a sum `f 0 + ⋯ + f (k-1)` with each `f i` in `A i` or equal to `0`. -/
def Rep (A : ℕ → Set ℕ) (k p : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < k, f i = 0 ∨ f i ∈ A i) ∧ ∑ i ∈ range k, f i = p

end LeanLab.Ramare1995.Theorem91

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Theorem91

/-- The sumset `A 0 + ⋯ + A (k-1)` (each summand may be `0`). -/
def SumSet (A : ℕ → Set ℕ) (k : ℕ) : Set ℕ := {p | Rep A k p}

/-- **Mann's theorem** for `h + 1` sets: `σ(A_0 + ⋯ + A_h) ≥ min(1, Σ σ(A_i))`. -/
theorem mann_sum (A : ℕ → Set ℕ) (h : ℕ) :
    min 1 (∑ i ∈ range (h + 1), schnirelmannDensity (A i)) ≤
      schnirelmannDensity (SumSet A (h + 1)) := by
  sorry

/-- **Mann's theorem**, Mann 1942, the `α + β` theorem: for `0 ∈ A`, `0 ∈ B`,
`σ(A + B) ≥ min(1, σ(A) + σ(B))`. -/
theorem mann (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (A + B) := by
  sorry

end LeanLab.Schnirelmann.Mann
