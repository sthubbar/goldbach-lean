module

public import LeanLab.Linnik.Decomp486c

/-!
Gallagher 1975 p.131 display 14.
The shared definitions moved identically to Decomp486c. Two smaller analytic cases remain.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp482b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp1532b (zeroCount excSet)
open LeanLab.PNTPort.LargeSieve (e)

/-- ASSEMBLY. CONDITIONAL ON the two Decomp486c explicit formula cases.
Gallagher 1975 p.131 display 14 and the paragraph following it.
The explicit formula and the near one density bound give exponential decay
of the corrected character energy. One exceptional conductor and real zero
are selected before the frequency. The strip and height are those of Theorem 3.
The zero density input and finite sieve are proved separately. -/
theorem corrected_energy_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ) := by
  exact LeanLab.Linnik.Decomp486c.corrected_energy_decay_split

end LeanLab.Linnik.Decomp482b








