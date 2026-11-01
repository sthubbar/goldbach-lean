module

public import Mathlib

/-!
P0100, A. W. Dudek, On the Riemann hypothesis and the difference between primes,
Int. J. Number Theory 11 (2015), arXiv 1402.6417, read 2026-10-16.
Statements only, side by side with STATEMENTS.md. No unproved theorem is left here: every theorem is a
statement `def`. `theorem1_stmt`, `theorem3_stmt`, `abstract_c3_stmt` are PROVED CONDITIONAL ON RH
and `HSWN70 gZ` in Retired2.lean, through Theorem1HSW.lean and AbstractC3HSW.lean;
`theorem2_stmt`, `theorem2_large_stmt` are PROVED CONDITIONAL ON RH, `TrudgianN70 gZ` and
Schoenfeld's ψ - θ bounds in Retired.lean. Header refreshed by PC 20261020T2203Z-17931, U-1297,
comment only; old copy old/Statements.lean-20261020T2203Z-17931-U-1297.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Dudek2014
open Real

/-- Dudek's interval length `(4/π) √x log x`. -/
noncomputable def dudekH (x : ℝ) : ℝ := 4 / π * √x * Real.log x

/-- There is a prime in `(x - (4/π) √x log x, x]`. -/
def PrimeInDudekInterval (x : ℝ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x - dudekH x < p ∧ (p : ℝ) ≤ x

/-- Number of primes in the half open interval `(x, x + h]`. -/
noncomputable def primesIn (x h : ℝ) : ℕ :=
  ((Finset.range (⌊x + h⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x < (p : ℝ))).card

/-- Theorem 1: under RH there is `c > 0` with `π(x + c √x log x) - π(x) > √x` for `x ≥ 2`.
RETIRED 2026-10-20 by CLOUD 20261020T2018Z-cloud50, U-6739: the unproved theorem is now this
statement only; it is PROVED CONDITIONAL ON `HSWN70 gZ` as `Dudek2014.Retired2.theorem1_stmt_of`,
through `Theorem1H.theorem1_of_RH_hsw`. Old copy in old/Statements-20261020-cloud50.lean. -/
def theorem1_stmt : Prop := RiemannHypothesis →
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → √x < primesIn x (c * √x * Real.log x)

/-- Theorem 2: under RH there is a prime in `(x - (4/π) √x log x, x]` for every `x ≥ 2`.
RETIRED 2026-10-20 by PC 20261020T1603Z-26078, U-1246: the unproved theorem is now this
statement only; it is PROVED CONDITIONAL ON Trudgian's N(T) bound and Schoenfeld's ψ - θ bounds
as `Dudek2014.Retired.theorem2_stmt_of`, through `PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_trudgian`.
Old copy in old/Statements-20261020.lean. -/
def theorem2_stmt : Prop := RiemannHypothesis → ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x

/-- Theorem 2, the analytic range of Section 2.2: the paper proves it for `x` at least about
`66798.7`; the lab uses `66799`. RETIRED 2026-10-20, U-1246, to a statement; PROVED CONDITIONAL
ON the same two inputs as `Dudek2014.Retired.theorem2_large_stmt_of`. -/
def theorem2_large_stmt : Prop := RiemannHypothesis → ∀ x : ℝ, 66799 ≤ x → PrimeInDudekInterval x

/-- Theorem 3: under RH, for every `ε > 0`, a prime in `(x - (1 + ε) √x log x, x]` for all
large `x`. RETIRED 2026-10-20, U-6739, to a statement; PROVED CONDITIONAL ON `HSWN70 gZ` as
`Dudek2014.Retired2.theorem3_stmt_of`, through `AbstractC3.theorem3_of_RH_hsw`. -/
def theorem3_stmt : Prop := RiemannHypothesis → ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    ∃ p : ℕ, p.Prime ∧ x - (1 + ε) * √x * Real.log x < p ∧ (p : ℝ) ≤ x

/-- Introduction and Section 2.4: under RH, `c = 3 + ε` works in Theorem 1 for all large `x`.
VERIFY notes Section 2.4 may define the constant as `3/2 + ε`; `3 + ε` is the weaker claim.
RETIRED 2026-10-20, U-6739, to a statement; PROVED CONDITIONAL ON `HSWN70 gZ` as
`Dudek2014.Retired2.abstract_c3_stmt_of`, through `AbstractC3.abstract_c3_of_RH_hsw`. -/
def abstract_c3_stmt : Prop := RiemannHypothesis → ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    √x < primesIn x ((3 + ε) * √x * Real.log x)

end LeanLab.Dudek2014

