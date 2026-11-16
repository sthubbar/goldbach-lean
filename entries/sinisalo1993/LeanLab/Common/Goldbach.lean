module

public import Mathlib

/-!
Shared Goldbach definitions for the Lean Lab.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.

This file is an extract of the lab file `LeanLab/Common/Goldbach.lean`: only four
Goldbach definitions are kept, the same extract as in the Helfgott and Platt 2013 entry.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `n` is a sum of three primes. -/
def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- Binary Goldbach holds for every even `n` with `4 ≤ n ≤ N`. -/
def EvenGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ N → IsGoldbachSum n

/-- Ternary Goldbach holds for every odd `n` with `7 ≤ n ≤ N`. -/
def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Odd n → 7 ≤ n → n ≤ N → IsTernarySum n

end LeanLab
