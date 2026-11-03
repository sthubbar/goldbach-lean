module

public import Mathlib

/-!
The sum of two primes predicate shared by the Goldbach files.
AI wrote the Lean code, Claude.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

end LeanLab
