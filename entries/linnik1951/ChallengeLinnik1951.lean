module

public import Mathlib

/-!
# Linnik 1951: two primes and a bounded number of powers of two, under GRH

Yu. V. Linnik, Prime numbers and powers of two, Trudy Mat. Inst. Steklov 38, 1951,
pages 152 to 169. The theorem on page 154 assumes the generalized Riemann hypothesis for all
Dirichlet L-functions. Its qualitative consequence, drawn on pages 168 and 169, is stated
here: there is a constant `K` such that every sufficiently large even integer is the sum of two
primes and at most `K` powers of two. The constant `K` is not made explicit. The printed
theorem is an asymptotic formula for the number of such representations with exactly `k`
powers of two; only the qualitative consequence is stated here.

The hypothesis is the generalized Riemann hypothesis, stated for zeros in the open strip
`0 < Re s < 1`, which leaves out the trivial zeros and the zeros on `Re s = 0` of the Euler
factors of imprimitive characters. Linnik 1953 and Gallagher 1975 later proved the result
without this hypothesis. Binary Goldbach, the case `K = 0`, is open and is not claimed.

Every definition below repeats the definition of the same name in the solution, with the
same `open` lines. AI wrote the Lean code.
-/

@[expose] public section

namespace LeanLab.DERZ1997

/-- The generalized Riemann hypothesis for Dirichlet L-functions: for every modulus `q ≥ 1`,
every Dirichlet character `χ` modulo `q` and every `s` with `0 < Re s < 1`, if the
L-function of `χ` vanishes at `s` then `Re s = 1/2`. For `q = 1` this is the Riemann
hypothesis. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

end LeanLab.DERZ1997

namespace LeanLab.Linnik
open LeanLab.DERZ1997

/-- `LinnikExact K N`: `N` is the sum of two primes and exactly `K` powers of two
`2 ^ ν` with each exponent `ν ≥ 1`. -/
def LinnikExact (K N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin K → ℕ, (∀ i, 1 ≤ ν i) ∧ N = p + q + ∑ i, 2 ^ ν i

/-- `LinnikAtMost K N`: `N` is the sum of two primes and at most `K` powers of two, each
at least `2`. -/
def LinnikAtMost (K N : ℕ) : Prop := ∃ k, k ≤ K ∧ LinnikExact k N

/-- `AllLargeEven P`: every sufficiently large even integer has property `P`. -/
def AllLargeEven (P : ℕ → Prop) : Prop := ∃ N0 : ℕ, ∀ N, Even N → N0 < N → P N

end LeanLab.Linnik

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- Linnik 1951, page 154, in its qualitative form: assuming the generalized Riemann
hypothesis for Dirichlet L-functions, there is a constant `K` such that every sufficiently
large even integer is the sum of two primes and at most `K` powers of two. -/
theorem linnik1951_decomposed_final_b1122 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) :=
  sorry

end LeanLab.Linnik1951
