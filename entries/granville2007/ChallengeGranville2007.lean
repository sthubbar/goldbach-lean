module

public import Mathlib

/-!
# The Riemann hypothesis and the average number of Goldbach representations, Granville 2007

A. Granville, *Refinements of Goldbach's conjecture, and the generalized Riemann hypothesis*,
Funct. Approx. Comment. Math. 37 (2007) 159–173, Theorem 1A, with the Corrigendum, ibid. 38
(2008) 235–237. Write `G(n) = Σ_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)` for the number of representations of
`n` as a sum of two prime powers, each weighted by the logarithms of its primes, and `J(n)` for
the singular series prediction. Granville's Theorem 1A states that RH holds iff
`Σ_{n ≤ x} (G(n) − J(n)) ≪ x^{3/2+o(1)}`. Since `Σ_{n ≤ x} J(n) = x²/2 + O(x log x)`
unconditionally, this is equivalent to the form formalized here:
`Σ_{n ≤ N} G(n) = N²/2 + O(N^{3/2+ε})` for every `ε > 0`, as noted by Bhowmik and Halupczok,
arXiv 1809.06920, Section 4, (10) and (11).

The target theorems, each proved in the solution with no hypothesis, are:
* `avgRH_of_RH`: the Riemann hypothesis implies the average asymptotic;
* `Converse.rh_of_avgRH`: the average asymptotic implies the Riemann hypothesis;
* `Converse.granville_equiv_proved`: the equivalence.

`RiemannHypothesis` is Mathlib's: every zero of `riemannZeta` that is not a trivial zero
`-2(n+1)` and is not at `s = 1` has real part `1/2`. The sum runs over integers `N ≥ 1`; for
real `x ≥ 1` and `N = ⌊x⌋` the two forms differ by at most `x`. Granville's 2007 sketch of the
direction from the asymptotic to RH was reconstructed in part by Bhowmik, Halupczok, Matsumoto,
Suzuki (arXiv 1704.06103) and completed by Bhowmik and Ruzsa (arXiv 1711.06442); the solution
follows that completed route, through the power series `Σ G(n) qⁿ = (Σ Λ(n) qⁿ)²`, a Mellin
transform holomorphic on `Re s > 1/2`, and the residue of `ζ'/ζ` at a zero. Binary Goldbach
itself is open; nothing here claims it.
Lean names keep the namespaces of the lab where the proofs were written.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `G(n) = ∑_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)`; `Λ 0 = 0`, so the ends of the antidiagonal add 0. -/
def G (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, Λ p.1 * Λ p.2

/-- `∑_{n ≤ x} G(n) = x²/2 + O(x^{3/2+ε})` for every `ε > 0`. -/
def AvgRH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ range (N + 1), G n - (N : ℝ) ^ 2 / 2| ≤ K * (N : ℝ) ^ (3 / 2 + ε)

/-- A form equivalent to Granville 2007, Theorem 1A: the Riemann hypothesis holds if and only
if `AvgRH`. -/
def GranvilleEquiv : Prop := RiemannHypothesis ↔ AvgRH

/-- A form equivalent to Granville 2007, Theorem 1A, the direction RH ⇒ `AvgRH`. -/
theorem avgRH_of_RH (hRH : RiemannHypothesis) : AvgRH := by
  sorry

end LeanLab.GoldbachAverage

namespace LeanLab.GoldbachAverage.Converse

/-- A form equivalent to Granville 2007, Theorem 1A, the direction `AvgRH` ⇒ RH,
unconditional. -/
theorem rh_of_avgRH (H : AvgRH) : RiemannHypothesis := by
  sorry

/-- A form equivalent to Granville 2007, Theorem 1A:
RH ⇔ `Σ_{n ≤ N} G(n) = N²/2 + O(N^{3/2+ε})` for every `ε > 0`. -/
theorem granville_equiv_proved : GranvilleEquiv := by
  sorry

end LeanLab.GoldbachAverage.Converse
