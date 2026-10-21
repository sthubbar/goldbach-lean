module

public import Mathlib

/-!
# Conditional on RH: the number of Goldbach representations on average, Languasco and Zaccagnini

A. Languasco and A. Zaccagnini, *The number of Goldbach representations of an integer*,
Proc. Amer. Math. Soc. 140 (2012), no. 3, pages 795 to 804, arXiv 1011.3198, Theorem 1. Write
`G(n) = Σ_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)`, the paper's `R(n)`. Assuming the Riemann hypothesis,
Theorem 1 states, for `N ≥ 2`,

`Σ_{n ≤ N} G(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + O(N log³ N)`.

The target theorems are:
* `lz_theorem1_proved`: Theorem 1, with Mathlib's `RiemannHypothesis` as an explicit hypothesis;
  it is NOT an axiom, and nothing here proves or assumes RH outside that hypothesis. The
  `O(N log³ N)` is stated as one constant `K` for all integers `N ≥ 2`.
* `bsp_upper_proved`: the earlier upper bound of G. Bhowmik and J.-C. Schlage-Puchta, *Mean
  representation number of integers as the sum of primes*, Nagoya Math. J. 200 (2010), pages 27
  to 33: under RH the same formula holds with error `O(N log⁵ N)`. Their Ω result is not stated.
* `fujii_proved`: A. Fujii, *An additive problem of prime numbers. II*, Proc. Japan Acad. Ser. A
  Math. Sci. 67 (1991), pages 248 to 252: under RH the same formula holds with error
  `O((N log N)^{4/3})`.
* `lz_zeroSum_summable`: unconditional, the family summed in `zeroSum` for `Z1 x` is summable for
  every real `x > 0`, so `Z1 x` is its genuine sum and not Lean's junk value 0.

The sum over zeros. `NontrivialZero` is the set of zeros of `riemannZeta` in the open strip
`0 < Re ρ < 1`; each distinct zero appears once and is weighted by its multiplicity
`analyticOrderNatAt riemannZeta ρ`, so this is the paper's sum over zeros counted with
multiplicity. Under RH these are the zeros `1/2 + iγ` of the paper. `zeroSum` is an unordered
`tsum`; since the family is summable, by `lz_zeroSum_summable`, and `ℂ` is finite dimensional, it
is absolutely convergent and its value does not depend on any ordering of the zeros, as in the
paper, where the sum converges absolutely.

Binary Goldbach itself is open; nothing here claims it. This is an average over `n`.
Lean names keep the namespaces of the lab where the proofs were written.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `G(n) = ∑_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)`; `Λ 0 = 0`, so the ends of the antidiagonal add 0. -/
def G (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, Λ p.1 * Λ p.2

/-- Nontrivial zeros of ζ: zeros in the open critical strip. -/
def NontrivialZero : Type := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `Σ_ρ m(ρ) f(ρ)` over nontrivial zeros with multiplicity `m(ρ)`, an unordered `tsum`. -/
def zeroSum (f : ℂ → ℂ) : ℂ :=
  ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1

/-- `Z1 x = Σ_ρ m(ρ) x^{ρ+1} / (ρ(ρ+1))`, the zero sum of Theorem 1. -/
def Z1 (N : ℝ) : ℂ := zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))

end LeanLab.GoldbachAverage

noncomputable section
namespace LeanLab.GoldbachAverage
open Complex Finset Filter MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

/-- **Languasco-Zaccagnini 2012, Theorem 1, conditional on RH**: under the Riemann hypothesis,
`Σ_{n ≤ N} G(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + O(N log³ N)` for `N ≥ 2`. -/
theorem lz_theorem1_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * N * Real.log N ^ 3 := by
  sorry

/-- **Bhowmik and Schlage-Puchta 2010, upper bound, conditional on RH**: the same formula with
error `O(N log⁵ N)` for `N ≥ 2`. -/
theorem bsp_upper_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * N * Real.log N ^ 5 := by
  sorry

/-- **Fujii 1991, part II, conditional on RH**: the same formula with error `O((N log N)^{4/3})` for
`N ≥ 2`. -/
theorem fujii_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * ((N : ℝ) * Real.log N) ^ ((4 : ℝ) / 3) := by
  sorry

/-- The zero sum `Z1 x` converges absolutely: for every real `x > 0` the family
`ρ ↦ m(ρ) x^{ρ+1}/(ρ(ρ+1))` over the nontrivial zeros is summable, so `zeroSum` in `Z1 x` is its
genuine unordered sum, not the junk value `0`. Unconditional. -/
theorem lz_zeroSum_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((x : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1)))) := by
  sorry

end LeanLab.GoldbachAverage
