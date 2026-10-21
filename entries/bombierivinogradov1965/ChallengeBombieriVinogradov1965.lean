module

public import Mathlib

/-!
# The Bombieri-Vinogradov theorem, Bombieri 1965 and A. I. Vinogradov 1965

E. Bombieri, *On the large sieve*, Mathematika 12, 1965, 201-225, DOI 10.1112/S0025579300005313,
and A. I. Vinogradov, *The density hypothesis for Dirichlet L-series*, Izv. Akad. Nauk SSSR
Ser. Mat. 29, 1965, 903-934. For every `A > 0` there is `B > 0` with
`Σ_{q ≤ x^{1/2} (log x)^{−B}} max_{y ≤ x} max_{(a,q)=1} |ψ(y; q, a) − y/φ(q)| ≪_A x (log x)^{−A}`.

The target theorems, each proved in the solution with no hypothesis, are:
* `bombieriVinogradovMax`: the theorem in its classical form for `ψ`, with the maximum over
  `y ≤ x` and over the reduced residue `a` inside the sum, written with choice functions `y q`
  and `a q`;
* `bombieriVinogradovMax_at_x`: the special case `y q = x`, `a q = 1`, a check that the
  hypotheses of the classical form can be met;
* `bvTheta`: the same classical form for `θ(y; q, a) = Σ_{p ≤ y, p ≡ a mod q} log p`;
* `bvPi`: the same for `π(y; q, a)` against `liD(y)/φ(q)`, `liD(y) = Σ_{2 ≤ n ≤ y} 1/log n`;
* `bvPiPi`: the same for `π(y; q, a)` against `π(y)/φ(q)`, the form sieve papers use as level of
  distribution `1/2`.

All constants are ineffective, through Siegel's theorem, as in the papers. "≪" with constants
depending on `A` is read as: for each `A > 0` some `B > 0` and `K`, for every `x ≥ 2`. The range
`q ≤ x^{1/2} (log x)^{−B}` is `Finset.Icc 1 ⌊√x / (log x)^B⌋₊`. Binary Goldbach is open; nothing
here claims it. Lean names keep the namespaces of the lab where the proofs were written:
`HeathBrown1985` for `ψ(x; k, l)`, `PNTPort.BVMax` for the rest. An AI agent, Claude by
Anthropic, wrote the Lean code; the zero-free region for ζ and the prime number theorem files
under `LeanLab/PNTPort/StrongPNT` are ported from PrimeNumberTheoremAnd, Apache-2.0. The
Heath-Brown 1985 entry PALOMAR-2026-10-21-000005 shares the library but does not compare these
statements; this entry adds the maximum over `y ≤ x` and the forms for `θ` and `π`.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `ψ(x; k, l) = Σ_{n ≤ x, n ≡ l mod k} Λ(n)`. -/
def psi (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), Λ n

end LeanLab.HeathBrown1985
end

namespace LeanLab.PNTPort.BVMax

open Finset Real Filter
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.HeathBrown1985 (psi)

/-- Bombieri-Vinogradov, classical form: the maximum over `y ≤ x` and over the residue class is
inside the sum, written with choice functions `y` and `a`. -/
def BombieriVinogradovMax : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |psi (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A

end LeanLab.PNTPort.BVMax

namespace LeanLab.PNTPort.BVMax

open Finset Real
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.HeathBrown1985 (psi)

/-- `θ(N; q, a)`, natural argument. -/
noncomputable def thetaN (N q a : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n % q = a % q ∧ n.Prime), Real.log n

/-- `π(N; q, a)`, natural argument. -/
noncomputable def piN (N q a : ℕ) : ℝ :=
  (((Icc 1 N).filter (fun n => n % q = a % q ∧ n.Prime)).card : ℝ)

/-- `Σ_{2 ≤ n ≤ N} 1/log n`; the `n = 1` term is `1/log 1 = 0`. -/
noncomputable def liN (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, 1 / Real.log n

/-- `θ(y; q, a) = Σ_{p ≤ y, p ≡ a mod q} log p`. -/
noncomputable def thetaAP (y : ℝ) (q a : ℕ) : ℝ := thetaN ⌊y⌋₊ q a

/-- `π(y; q, a) = #{p ≤ y : p prime, p ≡ a mod q}`. -/
noncomputable def piAP (y : ℝ) (q a : ℕ) : ℝ := piN ⌊y⌋₊ q a

/-- `liD(y) = Σ_{2 ≤ n ≤ y} 1/log n`. -/
noncomputable def liD (y : ℝ) : ℝ := liN ⌊y⌋₊

/-- Bombieri-Vinogradov for `θ`, classical form with the maximum over `y ≤ x`. -/
def BVTheta : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |thetaAP (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A

/-- Bombieri-Vinogradov for `π` against `liD`, classical form with the maximum over `y ≤ x`. -/
def BVPi : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |piAP (y q) q (a q) - liD (y q) / q.totient| ≤ K * x / Real.log x ^ A

end LeanLab.PNTPort.BVMax

namespace LeanLab.PNTPort.BVMax

open Finset Real

/-- Bombieri-Vinogradov against `π(y)/φ(q)`, classical form with the maximum over `y ≤ x`. -/
def BVPiPi : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |piAP (y q) q (a q) - piAP (y q) 1 1 / q.totient| ≤ K * x / Real.log x ^ A

/-- The Bombieri-Vinogradov theorem for `ψ`, classical form with `max_{y ≤ x} max_{(a,q)=1}`
inside the sum over `q ≤ x^{1/2} (log x)^{−B}`. -/
theorem bombieriVinogradovMax : BombieriVinogradovMax := by sorry

/-- The case `y q = x`, `a q = 1` of `bombieriVinogradovMax`. -/
theorem bombieriVinogradovMax_at_x (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ,
    ∀ x : ℝ, 2 ≤ x → ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
      |HeathBrown1985.psi x q 1 - x / q.totient| ≤ K * x / Real.log x ^ A := by sorry

/-- The Bombieri-Vinogradov theorem for `θ`, classical form. -/
theorem bvTheta : BVTheta := by sorry

/-- The Bombieri-Vinogradov theorem for `π` against `liD(y)/φ(q)`, classical form. -/
theorem bvPi : BVPi := by sorry

/-- The Bombieri-Vinogradov theorem for `π` against `π(y)/φ(q)`, classical form. -/
theorem bvPiPi : BVPiPi := by sorry

end LeanLab.PNTPort.BVMax
