module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Explicit Chen theorems, statements only, as `Prop`s, so nothing unproved is asserted.
* P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409, Theorem 1.1.
* P0009 M. Bordignon, D. R. Johnston, V. Starichkova, An explicit version of Chen's theorem,
  arXiv 2207.09452, Theorem 3, Corollary 4, Theorem 5.
Both papers define their count as the number of representations of `N` as a prime plus a
product of at most two primes; neither text, as read on 2026-10-16, adds size conditions on the
prime factors, so we use `Nat.IsAtMostAlmostPrime 2` from Mathlib, which admits `1`.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

/-- Chen representations: primes `p < N` with `N - p` a product of at most two primes. -/
def chenCount (N : ℕ) : ℕ := by
  classical exact #{p ∈ range N | p.Prime ∧ Nat.IsAtMostAlmostPrime 2 (N - p)}

/-- The twin prime constant `∏_{p > 2} (1 - 1/(p-1)²)`. -/
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `U_N = 2 e^{-γ} ∏_{p>2} (1 - 1/(p-1)²) ∏_{p>2, p ∣ N} (p-1)/(p-2)`, equation (2) of P0009
and the display after Theorem 1.1 of P0010. -/
def U (N : ℕ) : ℝ :=
  2 * Real.exp (-Real.eulerMascheroniConstant) * twinC *
    ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- **Yamada 2015, Theorem 1.1.** For even `N > exp exp 36`, `π₂(N) > 0.007 U_N N / log² N`. -/
def Yamada : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp 36) < N →
    (7 / 1000 : ℝ) * U N * N / Real.log N ^ 2 < chenCount N

/-- **BJS 2022, Theorem 3.** For `N > exp exp 32.7`, `π₂(N) > 2·10⁻⁴ U_N N / log² N`.
The paper's Theorem 3 is about even `N`; we keep the evenness hypothesis. -/
def BJS3 : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp (327 / 10)) < N →
    (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 < chenCount N

/-- **BJS 2022, Corollary 4.** Every even `N > exp exp 32.7` is a prime plus a squarefree number
with at most two prime factors. -/
def BJS4 : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp (327 / 10)) < N →
    ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ Squarefree m ∧ ω m ≤ 2

/-- The form of Corollary 4 the BJS proof actually gives, with `m > 1`, via their count
`π₂*(N)` of square-free `η > 1`. -/
def BJS4strong : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp (327 / 10)) < N →
    ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ 1 < m ∧ Squarefree m ∧ ω m ≤ 2

/-- **BJS 2022, Theorem 5.** Every even `N ≥ 4` is a prime plus a product of at most `e^{29.3}`
primes. -/
def BJS5 : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N →
    ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ m ≠ 0 ∧ (Ω m : ℝ) ≤ Real.exp (293 / 10)

/-- Qualitative Chen above a threshold `T`: every even `N > T` is `p + P₂`. -/
def ChenAbove (T : ℝ) : Prop :=
  ∀ N : ℕ, Even N → T < N → ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ Nat.IsAtMostAlmostPrime 2 m

end LeanLab.ChenExplicit
