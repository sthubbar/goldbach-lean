module

public import LeanLab.Linnik.Decomp482c

/-!
Gallagher 1975 P0094 p.127 Theorem 3.
The sealed definitions and helpers moved identically to Decomp482a.
The character expansion is proved. The proof uses two smaller analytic leaves.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp466a

open Finset MeasureTheory
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- LEAF. Gallagher 1975 P0094 p.127 Theorem 3, unnumbered display.
The error is O of N over log squared N times the totient weight times the sum of
log P over P times tau of n, exp of minus c over theta, and the quoted exceptional weight.
The quoted term occurs only for an exceptional zero at height T equal to P to the fifth
with conductor at most P. One conductor works for all nonzero frequencies.
The fixed exceptional strip is chosen small enough for the p.127 preliminary facts.
No vanishing exponential error or restriction on the frequency is asserted.
CITED input. Its proof uses Section 1 and the references printed there. -/
theorem gallagher_theorem3 :
    ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ) ∧
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n) := by
  exact LeanLab.Linnik.Decomp482c.gallagher_theorem3_split

end LeanLab.Linnik.Decomp466a
