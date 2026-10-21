module

public import LeanLab.SchnirelmannGoldbach.S3
public import LeanLab.SchnirelmannGoldbach.FromDensity
public import LeanLab.SchnirelmannGoldbach.S2

/-!
Assembly: Schnirelmann's bounded-primes theorem from S1u and S2.
AI-written Lean code, Claude, 2026-10-16.
-/

@[expose] public section

namespace LeanLab.SchnirelmannGoldbach

/-- Every `n ≥ 2` is a sum of at most `H` primes, given the sieve bound S1u and the mean
square bound S2. Both remain open in the lab. -/
theorem schnirelmann_goldbach_of_S1u_S2 (h1 : S1u) (h2 : S2) :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n :=
  schnirelmann_goldbach_of_S3 (S3_of_S1u_S2 h1 h2)

/-- Every `n ≥ 2` is a sum of at most `H` primes, given only the uniform sieve bound S1u.
S2 is proved in S2.lean. S1u is the one remaining open step in the lab. -/
theorem schnirelmann_goldbach_of_S1u (h1 : S1u) :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n :=
  schnirelmann_goldbach_of_S1u_S2 h1 S2_holds

end LeanLab.SchnirelmannGoldbach
