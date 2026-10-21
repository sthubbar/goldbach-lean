module

public import LeanLab.HardyLittlewood1923.TheoremD

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5707, paper P0004.

# Hardy-Littlewood 1923, Theorem E, (3.63) and (3.64), p. 31: the statement

Every large even `n` is the sum of four odd primes, and the number of ordered representations
`N̄₄(n) ∼ (1/3) C₄ n³/(log n)⁴ ∏_{p ∣ n, p odd} (p - 1)(p² - 3p + 3)/((p - 2)(p² - 2p + 2))`,
`C₄ = ∏_{ϖ ≥ 3} (1 - 1/(ϖ - 1)⁴)`. Hardy and Littlewood assume Hypothesis R.
Also the shared notation of the proof: `g`, the divisor expansion of `Pi3`.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset

attribute [local instance] Classical.propDecidable

/-- `N̄₄(n)`: ordered 4-tuples of odd primes with sum `n`, repetitions allowed. -/
noncomputable def N4bar (n : ℕ) : ℕ :=
  #{t ∈ (range (n + 1)) ×ˢ ((range (n + 1)) ×ˢ (range (n + 1))) |
    t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 < n ∧
    (n - t.1 - t.2.1 - t.2.2).Prime ∧
    Odd t.1 ∧ Odd t.2.1 ∧ Odd t.2.2 ∧ Odd (n - t.1 - t.2.1 - t.2.2)}

/-- (3.64) `C₄ = ∏_{ϖ ≥ 3 prime} (1 - 1/(ϖ - 1)⁴)`. -/
noncomputable def C4 : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, if p = ⟨2, Nat.prime_two⟩ then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 4

/-- The product in (3.63), over the odd prime divisors of `n`. -/
noncomputable def Pi4 (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2),
    ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 3 * p + 3) / (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2))

/-- Theorem E, (3.63), in the `ε` form of `∼`, over even `n`. -/
def theoremE_stmt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n →
    |(N4bar n : ℝ) - C4 * (n : ℝ) ^ 3 / (3 * Real.log n ^ 4) * Pi4 n| ≤
      ε * (C4 * (n : ℝ) ^ 3 / (3 * Real.log n ^ 4) * Pi4 n)

/-- The multiplicative weight with `Pi3 m = Σ_{d ∣ m, d odd squarefree} g d` for odd `m`:
`g d = ∏_{ℓ ∣ d} (-1/(ℓ² - 3ℓ + 3))`. -/
noncomputable def g (d : ℕ) : ℝ :=
  ∏ l ∈ d.primeFactors, (-1 / ((l : ℝ) ^ 2 - 3 * l + 3))

end LeanLab.HardyLittlewood1923

