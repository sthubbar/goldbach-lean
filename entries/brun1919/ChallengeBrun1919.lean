module

public import Mathlib

/-!
# Brun 1919: the sum of the reciprocals of the twin primes converges

V. Brun, *La série 1/5 + 1/7 + 1/11 + 1/13 + ... où les dénominateurs sont nombres premiers
jumeaux est convergente ou finie*, Bull. Sci. Math. 43, 1919, 100-104 and 124-128, proves that
the series of the reciprocals of the twin primes converges, by an upper bound for the number of
twin primes below `N`.

The target theorems, each proved in the solution with no hypothesis, are:
* `LeanLab.Brun1919.brun`: Brun's theorem, the series `Σ 1/p + 1/(p + 2)` over the primes `p`
  with `p + 2` prime is summable over the reals;
* `LeanLab.Brun1919.twinUpper`: the twin prime bound `π₂(N) ≤ C N / log² N` for `N ≥ 3`, which
  is stronger than the bound `π₂(N) ≪ N (log log N)² / log² N` of Brun's paper;
* `LeanLab.Brun1919.LeanEvalBridge.brun_constant_converges`: Brun's theorem in the exact form of
  the lean-eval problem `brun_constant_converges`, definitions copied from
  `LeanEval/NumberTheory/BrunConstant.lean` of github.com/leanprover/lean-eval;
* `LeanLab.BrunGap.brun_gap`: for every even `h ≠ 0`, the sum of `1/p` over the primes `p` with
  `p + h` prime converges;
* `LeanLab.BrunGap.gapUpper_uniform`: the number of primes `p < N` with `p + h` prime is at most
  `C₀ 𝔖(h) N / log² N`, with `𝔖(h) = ∏_{p ∣ h} (1 + 1/p)` and one absolute constant `C₀` for
  every even `h ≠ 0` and every `N ≥ 3`;
* `LeanLab.BrunGap.sum_gapCount_le`: its average over gaps, at most `9 C₀ H N / log² N` prime
  pairs `(p, p + h)` with `p < N` and `h ≤ H` even.

The bounds come from the Selberg sieve, not from Brun's own sieve. Binary Goldbach and the twin
prime conjecture are open; nothing here claims them. Lean names keep the namespaces of the lab
where the proofs were written.
-/

@[expose] public section

/-! ### Definitions, restated from `LeanLab/Brun1919/Statements.lean` -/

open Finset

namespace LeanLab.Brun1919

/-- `p` is the smaller member of a twin prime pair. -/
def IsTwin (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- Decidability of `IsTwin`, from the decidability of primality. -/
instance : DecidablePred IsTwin := fun p => by unfold IsTwin; infer_instance

/-- `π₂(N)`: the number of twin primes `p < N`, counting the smaller member. -/
noncomputable def twinCount (N : ℕ) : ℕ := #{p ∈ range N | IsTwin p}

/-- **Brun's upper bound**, `π₂(N) ≪ N / log² N`. -/
def TwinUpper : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → (twinCount N : ℝ) ≤ C * N / Real.log N ^ 2

/-- **Brun's theorem**: the series `1/3 + 1/5 + 1/5 + 1/7 + 1/11 + 1/13 + ...` over twin prime
pairs `(p, p + 2)` converges. -/
def BrunTheorem : Prop :=
  Summable (fun p : ℕ => if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0)

end LeanLab.Brun1919

/-! ### Definition, restated from `LeanLab/SchnirelmannGoldbach/Statements.lean` -/

section
open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach

/-- The singular product `∏_{p ∣ n} (1 + 1/p)`. -/
noncomputable def singProd (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))

end LeanLab.SchnirelmannGoldbach
end

/-! ### Definitions, restated from `LeanLab/BrunGap/Sieve.lean` and `Uniform.lean` -/

section
open Finset
open LeanLab.SchnirelmannGoldbach

noncomputable section
namespace LeanLab.BrunGap

/-- The number of primes `p < N` with `p + h` prime. -/
def gapCount (h N : ℕ) : ℕ := #{p ∈ range N | p.Prime ∧ (p + h).Prime}

/-- The constant of the uniform bound. -/
def C₀ : ℝ := 128 + 5 * 17 ^ 8

end LeanLab.BrunGap
end
end

/-! ### Definitions, restated from `LeanLab/Brun1919/LeanEvalBridge.lean`, which copies them
from the lean-eval problem `brun_constant_converges` -/

namespace LeanLab.Brun1919.LeanEvalBridge

/-- A twin-prime start is a prime `p` such that `p + 2` is also prime. -/
def IsTwinPrimeStart (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime

/-- The reciprocal contribution of the twin pair beginning at `p`, counted once, by its smaller
prime. -/
noncomputable def twinPrimeReciprocalTerm (p : ℕ) : ℝ :=
  by
    classical
    exact if IsTwinPrimeStart p then (1 / (p : ℝ)) + (1 / ((p + 2 : ℕ) : ℝ)) else 0

end LeanLab.Brun1919.LeanEvalBridge

/-! ### Target theorems -/

section
open Finset

namespace LeanLab.Brun1919

/-- **Brun's upper bound** `π₂(N) ≤ C N / log² N`. -/
theorem twinUpper : TwinUpper := by
  sorry

/-- **Brun's theorem.** The sum of the reciprocals of the twin primes converges. -/
theorem brun : BrunTheorem := by
  sorry

end LeanLab.Brun1919

namespace LeanLab.Brun1919.LeanEvalBridge

/-- **Brun's theorem** in the form of the lean-eval problem. -/
theorem brun_constant_converges :
    Summable twinPrimeReciprocalTerm := by
  sorry

end LeanLab.Brun1919.LeanEvalBridge

namespace LeanLab.BrunGap
open LeanLab.SchnirelmannGoldbach

/-- **Brun's theorem for gap `h`.** For every even `h ≥ 2`, the sum of `1/p` over primes `p`
with `p + h` prime converges. -/
theorem brun_gap (h : ℕ) (hh : Even h) (hh0 : h ≠ 0) :
    Summable (fun p : ℕ => if p.Prime ∧ (p + h).Prime then (1 : ℝ) / p else 0) := by
  sorry

/-- **Uniform Brun bound**: one constant `C₀` for every even gap `h ≠ 0`. -/
theorem gapUpper_uniform (h : ℕ) (hh : Even h) (hh0 : h ≠ 0) (N : ℕ) (hN : 3 ≤ N) :
    (gapCount h N : ℝ) ≤ C₀ * singProd h * N / Real.log N ^ 2 := by
  sorry

/-- **Prime pairs with bounded gap, on average.** For `H ≥ 1` and `N ≥ 3`, the number of
pairs of primes `(p, p + h)` with `p < N` and `h ≤ H` even is at most `9 C₀ H N / log² N`. -/
theorem sum_gapCount_le (H N : ℕ) (hH : 1 ≤ H) (hN : 3 ≤ N) :
    ∑ h ∈ (Icc 1 H).filter Even, (gapCount h N : ℝ) ≤ 9 * C₀ * H * N / Real.log N ^ 2 := by
  sorry

end LeanLab.BrunGap
end
