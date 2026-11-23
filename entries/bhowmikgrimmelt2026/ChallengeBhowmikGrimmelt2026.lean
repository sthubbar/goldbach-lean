module

public import Mathlib

/-!
# Bhowmik and Grimmelt 2026, Theorem 3.1: the exceptional set under a zero hypothesis

G. Bhowmik and L. Grimmelt, The exceptional set of the Goldbach problem, arXiv 2607.27282 v2,
Theorem 3.1 on page 9, which the paper attributes to Hardy and Littlewood. Assume that every
zero of every Dirichlet L-function has real part at most `Θ`, with `Θ < 3/4`. Then for every
`ε > 0` the number `E(X)` of even numbers up to `X` that are not a sum of two primes satisfies
`E(X) ≪_ε X^(2Θ - 1/2 + ε)`.

The zero hypothesis `ZeroBound Θ` is stated for every modulus and every Dirichlet character,
primitive or not, on the zeros of Mathlib's `DirichletCharacter.LFunction` in the open strip
`0 < Re s < 1`. It is not known for any `Θ < 1`, it is false for `Θ < 1/2`, and the generalized
Riemann hypothesis gives it for `Θ = 1/2`. The compared theorem takes it, `Θ < 3/4` and
`ε > 0` as explicit hypotheses; no other input is assumed.

Every definition below repeats the definition of the same name in the solution, with the same
namespaces and local instances; the solution's `open LeanLab.ExceptionalSet` line names more
definitions, which these statements do not use. Binary Goldbach is open and is not claimed here. AI wrote
the Lean code.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

end LeanLab

namespace LeanLab.ExceptionalSet
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- `E X`, the number of even `n` with `4 ≤ n ≤ X` that are not a sum of two primes. Since
`4 = 2 + 2`, this is the paper's count of even `N` with `2 < N ≤ X` that are not a sum of two
primes. -/
noncomputable def E (X : ℕ) : ℕ :=
  ((Finset.Icc 4 X).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- `E X ≪ X^θ`: some constant `C` has `E X ≤ C X^θ` for every `X ≥ 1`. -/
def PowerBound (θ : ℝ) : Prop := ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → (E X : ℝ) ≤ C * (X : ℝ) ^ θ

end LeanLab.ExceptionalSet

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound)

attribute [local instance] Classical.propDecidable

/-- Every zero of every Dirichlet L-function has real part at most `Θ`, page 9. Zeros are taken
in the open strip `0 < Re s < 1`: trivial zeros have real part at most 0, and the strip avoids
the value that Mathlib's `LFunction` of a principal character takes at `s = 1`. -/
def ZeroBound (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re ≤ Θ

/-- Theorem 3.1, page 9: if `ZeroBound Θ` with `Θ < 3/4`, then for every `ε > 0`,
`E(X) ≪_ε X^(2Θ - 1/2 + ε)`. -/
def Theorem31 : Prop :=
  ∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ → ∀ ε : ℝ, 0 < ε → PowerBound (2 * Θ - 1 / 2 + ε)

end LeanLab.BhowmikGrimmelt2026

namespace LeanLab.BhowmikGrimmelt2026

/-- Theorem 3.1 of Bhowmik and Grimmelt, page 9, proved from its three hypotheses
`Θ < 3/4`, `ZeroBound Θ` and `0 < ε`. -/
theorem theorem31_ported1122 : Theorem31 := by
  sorry

end LeanLab.BhowmikGrimmelt2026
