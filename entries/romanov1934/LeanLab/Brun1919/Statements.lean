module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Brun 1919, "La série 1/5 + 1/7 + 1/11 + 1/13 + ... où les dénominateurs sont nombres premiers
jumeaux est convergente ou finie", Bull. Sci. Math. 43.
Statements only, as `Prop`s, so that no placeholder proof is needed. Proofs live in `Sieve.lean` and
`Final.lean`.
-/

@[expose] public section

open Finset

namespace LeanLab.Brun1919

/-- `p` is the smaller member of a twin prime pair. -/
def IsTwin (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

instance : DecidablePred IsTwin := fun p => by unfold IsTwin; infer_instance

/-- `π₂(N)`: the number of twin primes `p < N`, counting the smaller member. -/
noncomputable def twinCount (N : ℕ) : ℕ := #{p ∈ range N | IsTwin p}

/-- **Brun's upper bound**, `π₂(N) ≪ N / log² N`. Brun 1919 proves the stronger
`π₂(x) ≪ x (log log x / log x)²` with his pure sieve and later `x / log² x` with his
combinatorial sieve; we state the latter, which the Selberg sieve also gives. -/
def TwinUpper : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → (twinCount N : ℝ) ≤ C * N / Real.log N ^ 2

/-- **Brun's theorem**, the paper's title: the series `1/3 + 1/5 + 1/5 + 1/7 + 1/11 + 1/13 + ...`
over twin prime pairs `(p, p + 2)` converges. -/
def BrunTheorem : Prop :=
  Summable (fun p : ℕ => if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0)

end LeanLab.Brun1919
