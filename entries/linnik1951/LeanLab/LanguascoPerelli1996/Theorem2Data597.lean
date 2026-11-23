module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.ExceptionalSet.Statements
public import LeanLab.DERZ1997.Statements

/-!
Sealed data moved verbatim from Statements to avoid a theorem2 import cycle.
P0071 pages 350 and 353. No definition body or statement changes.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996
open Real Filter Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)


abbrev GRH : Prop := LeanLab.DERZ1997.GRH

/-- `E(X,H)`, the number of even `2n ∈ [X, X+H]` that are not a sum of two primes. -/
noncomputable def EH (X H : ℝ) : ℕ :=
  ((Finset.Icc ⌈X⌉₊ ⌊X + H⌋₊).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- `S(α) = Σ_{X/4 ≤ n ≤ 2X} Λ(n) e(nα)`; the lower limit `X/4` is checked on the image. -/
noncomputable def S (X α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊, (Λ n : ℂ) * e (n * α)

/-- `T(α) = Σ_{X/4 ≤ n ≤ 2X} e(nα)`. -/
noncomputable def Tsum (X α : ℝ) : ℂ := ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊, e (n * α)

/-- `μ(q)/φ(q)`. -/
noncomputable def muPhi (q : ℕ) : ℝ := ((moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)

/-- `R(η;q,a) = S(a/q + η) - μ(q)/φ(q) T(η)`. -/
noncomputable def R (X η : ℝ) (q a : ℕ) : ℂ :=
  S X ((a : ℝ) / q + η) - (muPhi q : ℂ) * Tsum X η

/-- `I(X,Q;q,a) = ∫_{-1/qQ}^{1/qQ} abs R(η;q,a)² dη`. -/
noncomputable def Ival (X Q : ℝ) (q a : ℕ) : ℝ :=
  ∫ η in (-(1 / (q * Q)))..(1 / (q * Q)), ‖R X η q a‖ ^ 2

/-- Hypothesis (5) for a choice `Q = Q(X)`: `I(X,Q;q,a) ≪_ε X^{1+ε}/(qQ)` uniformly for
`q ≤ Q`, `(a,q) = 1`, for every `ε > 0`. -/
def Bound5 (Q : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q X →
    ∀ a : ℕ, Nat.Coprime a q → Ival X (Q X) q a ≤ C * X ^ (1 + ε) / (q * Q X)

/-- **Theorem 2**, p. 350. Assume GRH, `ε > 0`, `X^ε ≤ Q ≤ X^{1/2}/2`, and (5). Then
`E(X, 4Q²) ≪_ε X^ε`. Read with the paper's convention that `ε` is arbitrarily small and may
change: a fixed `ε₀` in the range of `Q`, (5) for every `ε`, the conclusion for every `ε`. -/
def Theorem2 : Prop :=
  GRH → ∀ ε0 : ℝ, 0 < ε0 → ∀ Q : ℝ → ℝ,
    (∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → X ^ ε0 ≤ Q X ∧ Q X ≤ X ^ (1 / 2 : ℝ) / 2) → Bound5 Q →
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → (EH X (4 * Q X ^ 2) : ℝ) ≤ C * X ^ ε


end LeanLab.LanguascoPerelli1996
