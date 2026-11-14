module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Schnirelmann.Inequality

/-!
Roadmap for Schnirelmann's theorem that every integer above 1 is a sum of a bounded number of
primes, Schnirelmann 1930. The roadmap statements are `def ..._stmt : Prop` here and are all
PROVED, with no placeholder proofs, in LeanLab.SchnirelmannGoldbach.Discharged; run 20261019T1003Z-30522 retired
the five old unproved theorems, the previous file is old/Statements-20261019T1003Z-30522.lean.
AI-written Lean code, Claude, 2026-10-16.
Proof plan, as in Nathanson GTM 164 Chapter 7:
  S1 sieve upper bound for r(n), the number of p with p and n - p prime;
  S2 mean square bound for the singular product over n ≤ N;
  S3 Cauchy-Schwarz plus Chebyshev give positive lower density of Goldbach sums;
  S4 positive Schnirelmann density of {0, 1} ∪ Goldbach sums;
  S5 Schnirelmann basis theorem, proved in LeanLab.Schnirelmann.Inequality;
  S6 removal of the ones.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach

/-- Goldbach sums, the set of `p + q`. -/
def G : Set ℕ := {n | IsGoldbachSum n}

/-- Number of primes `p < n` with `n - p` prime. -/
noncomputable def r (n : ℕ) : ℕ := #{p ∈ range n | p.Prime ∧ (n - p).Prime}

/-- The singular product `∏_{p ∣ n} (1 + 1/p)`. -/
noncomputable def singProd (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))

/-- S1. Selberg or Brun sieve upper bound. PROVED in Discharged.lean. -/
def S1_sieve_upper_stmt : Prop :=
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
    (r n : ℝ) ≤ C * n / (Real.log n) ^ 2 * singProd n

/-- S2. Mean square of the singular product is linear. PROVED in Discharged.lean. -/
def S2_mean_square_stmt : Prop :=
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ C * N

/-- S3. Goldbach sums have positive lower density. PROVED in Discharged.lean. -/
def S3_positive_lower_density_stmt : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * N ≤ #{n ∈ Icc 1 N | n ∈ G}

/-- S4. Positive Schnirelmann density. PROVED in Discharged.lean. -/
def S4_schnirelmann_pos_stmt : Prop :=
    0 < schnirelmannDensity ({0, 1} ∪ G)

/-- `n` is a sum of exactly `k` primes. -/
def SumOfPrimes (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length = k ∧ (∀ p ∈ l, p.Prime) ∧ l.sum = n

/-- S6 and the main theorem. Schnirelmann 1930. PROVED in Discharged.lean, from S4, S5, S6. -/
def schnirelmann_goldbach_stmt : Prop :=
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n

end LeanLab.SchnirelmannGoldbach
