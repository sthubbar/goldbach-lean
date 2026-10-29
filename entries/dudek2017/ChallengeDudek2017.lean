module

public import Mathlib

/-!
# Dudek 2017: every integer N > 2 is a prime plus a square-free number, given AP12Lower 0.21

A. W. Dudek, *On the sum of a prime and a square-free number*, The Ramanujan Journal 42, 2017,
pages 233 to 240, doi 10.1007/s11139-015-9736-2, arXiv 1410.7459, Theorem 1: every integer
`N > 2` is the sum of a prime and a square-free number.

The target theorems are

* `dudek_all_ap12`: Dudek's Theorem 1, every `N > 2` is `p + (N - p)` with `p < N` prime and
  `N - p` square-free, conditional on the hypothesis `AP12Lower 0.21`;
* `dudek_even_split`: the even case, every even `N ≥ 4` is `p + m` with `p` prime and `m ≥ 1`
  square-free, with no hypothesis;
* `ap12Lower_of_bmor`: `BMORCor16`, Corollary 1.6 of Bennett, Martin, O'Bryant and Rechnitzer,
  *Explicit bounds for primes in arithmetic progressions*, Illinois J. Math. 62, 2018, implies
  `AP12Lower 0.21`.

`AP12Lower c` says that for every integer `x ≥ 10⁹` each reduced class mod 12 holds more than
`c x / log x` primes `p ≤ x`. It is a hypothesis of the theorem, not an axiom; it is not proved
here. Binary Goldbach is open and nothing here claims it. AI wrote the Lean code. Lean names keep
the namespaces of the lab where the proofs were written.
-/

@[expose] public section

open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.U1445DudekOdd

/-- `π(x; q, a)` at an integer `x`: the primes `p ≤ x` with `p ≡ a mod q`. -/
def primesAP (x q a : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun p => p.Prime ∧ p % q = a % q)

/-- **Cited input.** Bennett, Martin, O'Bryant, Rechnitzer, *Explicit bounds for primes in
arithmetic progressions*, Illinois J. Math. 62 (2018), arXiv 1802.00085, Corollary 1.6: for
`1 ≤ q ≤ 1200`, `gcd(a, q) = 1` and all `x ≥ 50 q²`,
`x/(φ(q) log x) < π(x; q, a) < x/(φ(q) log x) · (1 + 5/(2 log x))`.
Stated here at integer `x` only, which the published statement for real `x` implies. -/
def BMORCor16 : Prop :=
  ∀ q a x : ℕ, 1 ≤ q → q ≤ 1200 → Nat.Coprime a q → 50 * q ^ 2 ≤ x →
    (x : ℝ) / ((q.totient : ℝ) * Real.log x) < ((primesAP x q a).card : ℝ) ∧
      ((primesAP x q a).card : ℝ) <
        (x : ℝ) / ((q.totient : ℝ) * Real.log x) * (1 + 5 / (2 * Real.log x))

end LeanLab.AlmostPrimes.U1445DudekOdd

end

open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.U1504DudekOdd12

open LeanLab.AlmostPrimes.U1445DudekOdd

/-- **The hypothesis.** For every `a` prime to `12` and every integer `x ≥ 10⁹`, the primes
`p ≤ x` with `p ≡ a mod 12` number more than `c x / log x`. At `c = 1/4` this is the lower half
of Bennett, Martin, O'Bryant, Rechnitzer 2018 Corollary 1.6 at `q = 12`; the entry uses
`c = 0.21`. -/
def AP12Lower (c : ℝ) : Prop :=
  ∀ a x : ℕ, Nat.Coprime a 12 → 10 ^ 9 ≤ x →
    c * (x : ℝ) / Real.log x < ((primesAP x 12 a).card : ℝ)

/-- `BMORCor16` implies `AP12Lower 0.21`. -/
theorem ap12Lower_of_bmor (hB : BMORCor16) : AP12Lower 0.21 := by
  sorry

end LeanLab.AlmostPrimes.U1504DudekOdd12

end

namespace LeanLab.AlmostPrimes.U1497DudekAll

/-- **Dudek 2017, Theorem 1, even case, with no hypothesis**: every even `N ≥ 4` is the sum of a
prime `p` and a square-free number `m ≥ 1`. -/
theorem dudek_even_split (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  sorry

end LeanLab.AlmostPrimes.U1497DudekAll

namespace LeanLab.AlmostPrimes.U1504DudekAll

open LeanLab.AlmostPrimes.U1504DudekOdd12

/-- **Dudek 2017, Theorem 1, conditional on `AP12Lower 0.21`**: every integer `N > 2` is
`p + (N - p)` with `p < N` prime and `N - p` square-free. -/
theorem dudek_all_ap12 (hA : AP12Lower 0.21) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) := by
  sorry

end LeanLab.AlmostPrimes.U1504DudekAll
