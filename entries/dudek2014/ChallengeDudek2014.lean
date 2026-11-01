module

public import Mathlib

/-!
# On the Riemann hypothesis and the difference between primes

A. W. Dudek, *On the Riemann hypothesis and the difference between primes*, Int. J. Number
Theory 11 (2015), arXiv 1402.6417. Three of its theorems are compared, each under the Riemann
Hypothesis, Mathlib's `RiemannHypothesis`, which is the paper's own hypothesis.

* Theorem 2, `LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_hsw`: for every real `x ≥ 2`
  there is a prime in `(x - (4/π) √x log x, x]`.
* Theorem 1, `LeanLab.Dudek2014.Theorem1H.theorem1_of_RH_hsw`: there is `c > 0` with
  `π(x + c √x log x) - π(x) > √x` for every real `x ≥ 2`.
* Theorem 3, `LeanLab.Dudek2014.AbstractC3.theorem3_of_RH_hsw`: for every `ε > 0` there is a prime
  in `(x - (1 + ε) √x log x, x]` for all large `x`.

Each theorem also takes one cited input as an explicit hypothesis, never as an axiom:
`Dudek2014.SigmaH.HSWN70 gZ`, the zero count of Hasanalizade, Shen and Wong, arXiv 2107.06506,
Corollary 1.2, for `T ≥ 70`, stated for `gZ`, the ordinates of the nontrivial zeros of ζ counted
with multiplicity. The paper cites the zero count of Trudgian 2014 instead, whose constant
Hasanalizade, Shen and Wong report to be in error. Schoenfeld's bounds for `ψ - θ`, which the
paper also cites, are proved in the solution, as are Dudek's Lemma 4 and the explicit formula.

AI wrote the Lean code, Claude, Anthropic. Lean names keep the namespaces of the lab where the
proofs were written; every definition below is restated under its exact name and in the same
`open` context as in the solution files.
-/

@[expose] public section

/-! ### Primes in short intervals, `LeanLab/Dudek2014/Statements.lean` -/

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

end LeanLab.Dudek2014

/-! ### The zeros of ζ, `LeanLab/PNTPort/ExplicitPsi1/ZeroSum.lean` and `DudekTrudgian.lean` -/

namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology Set

local notation "ζ" => riemannZeta

/-- The zeros of ζ with `Re ρ ≥ -1/2`. These are exactly the nontrivial zeros: ζ has no zero on
`[-1/2, 0]` or on `Re s ≥ 1`, and Mathlib's value of `riemannZeta` at the pole `s = 1` is not
zero. -/
def Zall : Set ℂ := {ρ | ζ ρ = 0 ∧ -1 / 2 ≤ ρ.re}

end LeanLab.PNTPort.ExplicitPsi1

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex
open LeanLab.PNTPort.ExplicitPsi1

local notation "ζ" => riemannZeta

/-- The nontrivial zeros of ζ with multiplicity, as an index type: a zero `ρ` of order `m(ρ)`
contributes `m(ρ)` indices. -/
abbrev ZIdx := Σ ρ : Zall, Fin (analyticOrderNatAt ζ (ρ : ℂ))

/-- Their ordinates, `γ = Im ρ`. -/
noncomputable def gZ (i : ZIdx) : ℝ := ((i.1 : ℂ)).im

end LeanLab.PNTPort.ExplicitPsi1.Trivial

/-! ### The Hasanalizade-Shen-Wong count, `LeanLab/ChirreHagen2025/Lemma26HSW.lean` and
`LeanLab/Dudek2014/SigmaHSW.lean` -/

namespace LeanLab.ChirreHagen2025.Lemma26H
open MeasureTheory Set Filter Topology Real

variable {ι : Type*}

/-- The main term `M(T) = (T/2π) log(T/(2πe)) + 7/8`. -/
noncomputable def Mt (T : ℝ) : ℝ := T / (2 * π) * log (T / (2 * π * exp 1)) + 7 / 8

/-- The Hasanalizade-Shen-Wong error `0.1038 log T + 0.2573 log log T + 9.3675` with the `7/8`
of `M(T)` added, `R(T) = 0.1038 log T + 0.2573 log log T + 10.2425`. -/
noncomputable def Rt (T : ℝ) : ℝ := 0.1038 * log T + 0.2573 * log (log T) + 10.2425

end LeanLab.ChirreHagen2025.Lemma26H

namespace LeanLab.Dudek2014.SigmaH
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt)

variable {ι : Type*}

/-- Cited, Hasanalizade-Shen-Wong arXiv 2107.06506 Corollary 1.2,
`|N(T) - (T/2π) log(T/(2πe))| ≤ 0.1038 log T + 0.2573 log log T + 9.3675`, in its `N(T)` form
with the `7/8` moved into the error, as counts over any finite set of the ordinates, both signs,
for `70 ≤ T ≤ t`. -/
def HSWN70 (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 70 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)) ∧
  (∀ T t : ℝ, 70 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + Rt t) - (Mt T - Rt T)))

end LeanLab.Dudek2014.SigmaH

/-! ### Theorem 2, `LeanLab/Dudek2014/SigmaHSWDownstream.lean` -/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- Dudek 2015, Theorem 2. Under RH, given the Hasanalizade-Shen-Wong zero count `HSWN70` for
the ordinates `gZ`, for every real `x ≥ 2` there is a prime `p` with
`x - (4/π) √x log x < p ≤ x`. -/
theorem theorem2_of_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) :
    ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x := by
  sorry

end LeanLab.PNTPort.ExplicitPsi1.Trivial

/-! ### Theorem 1, `LeanLab/Dudek2014/Theorem1HSW.lean` -/

namespace LeanLab.Dudek2014.Theorem1H
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)

/-- Dudek 2015, Theorem 1. Under RH, given `HSWN70 gZ`, there is `c > 0` such that for every
real `x ≥ 2` the interval `(x, x + c √x log x]` holds more than `√x` primes. -/
theorem theorem1_of_RH_hsw (hRH : RiemannHypothesis) (hN : HSWN70 gZ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → √x < primesIn x (c * √x * Real.log x) := by
  sorry

end LeanLab.Dudek2014.Theorem1H

/-! ### Theorem 3, `LeanLab/Dudek2014/AbstractC3HSW.lean` -/

namespace LeanLab.Dudek2014.AbstractC3
open Real Finset
open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)
open scoped ArithmeticFunction.vonMangoldt

/-- Dudek 2015, Theorem 3. Under RH, given `HSWN70 gZ`, for every `ε > 0` there is `X` such
that for every real `x ≥ X` there is a prime `p` with `x - (1 + ε) √x log x < p ≤ x`. -/
theorem theorem3_of_RH_hsw (hRH : RiemannHypothesis) (hN : HSWN70 gZ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p : ℕ, p.Prime ∧ x - (1 + ε) * √x * Real.log x < p ∧ (p : ℝ) ≤ x := by
  sorry

end LeanLab.Dudek2014.AbstractC3
