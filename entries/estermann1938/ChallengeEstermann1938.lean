module

public import Mathlib

/-!
# Almost all even positive integers are sums of two primes, Estermann 1938

T. Estermann, On Goldbach's problem: proof that almost all even positive integers are sums of
two primes, Proc. London Math. Soc. series 2, volume 44, 1938, pages 307-314, doi 10.1112/plms/s2-44.4.307.

The Introduction, p. 307: let `Q(n)` denote the number of those even positive integers less than
`n` which are not representable as sums of two primes. Then, as `n → ∞`,
`Q(n) = O(n log^{-a} n)` for any positive number `a`.

The target theorem `LeanLab.Estermann1938.main` states exactly this, with natural logarithms;
another base changes only the constant. "Two primes" allows the prime `2`. The implied constant
depends on `a` and is ineffective in the proof given, as it rests on the Siegel-Walfisz theorem.
Binary Goldbach itself is open; nothing here claims it.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

end LeanLab

namespace LeanLab.Estermann1938
open Real Filter Asymptotics

attribute [local instance] Classical.propDecidable

/-- Estermann's `Q(n)`, p. 307: the even positive integers `m < n` that are not a sum of two
primes. The primes may be `2`, as in the paper, which says "two primes", not "two odd primes". -/
noncomputable def Q (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun m => 0 < m ∧ Even m ∧ ¬ IsGoldbachSum m)).card

/-- The main result, p. 307: for every `a > 0`, `Q(n) = O(n log^{-a} n)` as `n → ∞`. -/
def theorem_stmt : Prop :=
  ∀ a : ℝ, 0 < a →
    (fun n : ℕ => (Q n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log n ^ (-a))

/-- Estermann 1938, the main result, p. 307. -/
theorem main : theorem_stmt := by
  sorry

end LeanLab.Estermann1938
