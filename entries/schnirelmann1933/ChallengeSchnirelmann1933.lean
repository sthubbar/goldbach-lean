module

public import Mathlib

/-!
# Every integer at least 2 is a sum of a bounded number of primes, Schnirelmann 1933

L. Schnirelmann, *Über additive Eigenschaften von Zahlen*, Math. Ann. 107 (1933) 649-690.
Schnirelmann showed that the set of numbers `0`, `1` and the sums of two primes has positive
Schnirelmann density, and deduced from his basis theorem that every integer `n ≥ 2` is a sum of
at most `H` primes for an absolute constant `H`.

The target theorems, each proved in the solution with no hypothesis, are:
* `SchnirelmannGoldbach.S4_schnirelmann_pos`: the set `{0, 1} ∪ G`, with `G` the sums of two
  primes, has positive Schnirelmann density, Mathlib's `schnirelmannDensity`;
* `SchnirelmannGoldbach.schnirelmann_bounded_primes`: Schnirelmann's theorem, some `H` works;
* `SchnirelmannExplicit.Sharper6.schnirelmann_bounded_primes_H₆`: an explicit form, every
  `n ≥ 2` is a sum of at most `H₆ = 2 · 15385 + 2 = 30772` primes.

`SumOfPrimes k n` says that `n` is the sum of a list of `k` primes, repetitions allowed. The
explicit constant `30772` is far weaker than the best known constants: Ramaré 1995 showed that
every even integer is a sum of at most 6 primes, so every `n ≥ 2` is a sum of at most 7, and
Helfgott's ternary Goldbach theorem gives at most 4. Binary Goldbach itself is open; nothing
here claims it. Lean names keep the namespaces of the lab where the proofs were written.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

end LeanLab

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach

/-- Goldbach sums, the set of `p + q`. -/
def G : Set ℕ := {n | IsGoldbachSum n}

/-- S4. Positive Schnirelmann density. -/
def S4_schnirelmann_pos_stmt : Prop :=
    0 < schnirelmannDensity ({0, 1} ∪ G)

/-- `n` is a sum of exactly `k` primes. -/
def SumOfPrimes (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length = k ∧ (∀ p ∈ l, p.Prime) ∧ l.sum = n

/-- Schnirelmann 1933: the set of `0`, `1` and the sums of two primes has positive
Schnirelmann density. -/
theorem S4_schnirelmann_pos : S4_schnirelmann_pos_stmt := by
  sorry

/-- Schnirelmann 1933: there is an `H` such that every `n ≥ 2` is a sum of at most `H`
primes. -/
theorem schnirelmann_bounded_primes :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n := by
  sorry

end LeanLab.SchnirelmannGoldbach

namespace LeanLab.SchnirelmannExplicit.Sharper6

open LeanLab.SchnirelmannGoldbach

/-- The number of summands from `{0, 1} ∪ G` used in the explicit basis step. -/
def K₆ : ℕ := 15385

/-- The explicit Schnirelmann constant, `2 · 15385 + 2 = 30772`. -/
def H₆ : ℕ := 2 * K₆ + 2

/-- Schnirelmann's theorem, explicit form: every integer `n ≥ 2` is a sum of at most
`H₆ = 30772` primes. -/
theorem schnirelmann_bounded_primes_H₆ :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₆, SumOfPrimes k n := by
  sorry

end LeanLab.SchnirelmannExplicit.Sharper6
