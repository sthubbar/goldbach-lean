module

public import LeanLab.SchnirelmannGoldbach.Main
public import LeanLab.SchnirelmannGoldbach.S1.Final

/-!
Schnirelmann's theorem, 1930: every integer n ≥ 2 is a sum of at most H primes, for some
absolute H. Unconditional, with no placeholder proofs. The bound H is not explicit.
AI-written Lean code, Claude, 2026-10-16. Uses a port of the PNT+ Selberg sieve by
Arend Mellendijk, Apache 2.0.
-/

@[expose] public section

namespace LeanLab.SchnirelmannGoldbach

theorem schnirelmann_bounded_primes :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n :=
  schnirelmann_goldbach_of_S1u S1u_holds

end LeanLab.SchnirelmannGoldbach
