module

public import Mathlib

/-!
# Conditional on RH: the Cesàro average of Goldbach representations, Goldston and Yang

D. A. Goldston and L. Yang, *The average number of Goldbach representations*, in: Prime numbers
and representation theory, edited by Ye Tian and Yangbo Ye, Science Press, Beijing, 2017, pages 1 to 12,
arXiv 1601.06902, Theorem 2, eq. 2.2. Write `G(n) = Σ_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)`, the paper's
`r₂(n)`. Assuming the Riemann hypothesis, Theorem 2 states

`Σ_{n ≤ N} (1 − n/N) G(n) = N²/6 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)(ρ+2)) + O(N)`.

The target theorems are:
* `gy_theorem2_proved`: Theorem 2, with Mathlib's `RiemannHypothesis` as an explicit hypothesis;
  it is NOT an axiom, and nothing here proves or assumes RH outside that hypothesis. The `O(N)`
  is stated as one constant `K` for all integers `N ≥ 2`.
* `gy_zeroSum_summable`: unconditional, the family summed in `zeroSum` for Theorem 2 is
  summable for every `N ≥ 1`, so `zeroSum` there is its genuine sum and not Lean's junk value 0.

The sum over zeros. `NontrivialZero` is the set of zeros of `riemannZeta` in the open strip
`0 < Re ρ < 1`; each distinct zero appears once and is weighted by its multiplicity
`analyticOrderNatAt riemannZeta ρ`, so this is the paper's sum over zeros counted with
multiplicity. The trivial zeros are not included: the paper's sum comes from the explicit
formula for `ψ₁`, whose trivial zero terms are absorbed into `O(N)`. `zeroSum` is an unordered
`tsum`; since the family is summable, by `gy_zeroSum_summable`, and `ℂ` is finite dimensional,
it is absolutely convergent and its value does not depend on any ordering of the zeros, as in
the paper, which notes the sum is absolutely convergent.

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

end LeanLab.GoldbachAverage

namespace LeanLab.GoldbachAverage
open Complex Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The zero sum of Goldston-Yang Theorem 2 converges absolutely: for every `N ≥ 1` the family
`ρ ↦ m(ρ) N^{ρ+1}/(ρ(ρ+1)(ρ+2))` over the nontrivial zeros is summable, so `zeroSum` is its
genuine unordered sum, not the junk value `0`. Unconditional. -/
theorem gy_zeroSum_summable (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((N : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1) * (ρ.1 + 2)))) := by
  sorry

/-- **Goldston-Yang 2017, Theorem 2, conditional on RH**: under the Riemann hypothesis,
`Σ_{n ≤ N} (1 − n/N) G(n) = N²/6 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)(ρ+2)) + O(N)` for `N ≥ 2`. -/
theorem gy_theorem2_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), (1 - (n : ℝ) / N) * G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 6
      + 2 * zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1) * (ρ + 2)))‖ ≤ K * N := by
  sorry

end LeanLab.GoldbachAverage
