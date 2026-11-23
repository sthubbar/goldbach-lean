module

public import LeanLab.LanguascoPintzZaccagnini2007.TrueConstantK

/-!
P0045 task131. Decomposition of the conclusion on preprint page 9.
The target restores the factor 2c0 recorded in the earlier lab audit.
It makes no assertion that the corrected constant belongs to [1, 2].
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- Page 3: e(t) = exp(2 pi i t). -/
def phase131 (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- Page 3: the prime exponential sum S. -/
def primeSum131 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 X, (Λ m : ℝ) * phase131 ((m : ℝ) * α)

/-- Page 3: G uses exponents at most L - sqrt L. -/
def powerSum131 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ ν ∈ Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊, phase131 ((2 : ℝ) ^ ν * α)

/-- Page 3: Q = X/P. -/
def arcQ131 (X : ℕ) (P : ℝ) : ℝ := X / P

/-- Page 3: the major arcs about reduced a/q with q at most P. -/
def majorArcs131 (X : ℕ) (P : ℝ) : Set ℝ :=
  {α | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ a ∈ Icc 1 q ∧ Nat.Coprime a q ∧
    α ∈ Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * arcQ131 X P))
      ((a : ℝ) / q + 1 / ((q : ℝ) * arcQ131 X P))}

/-- Page 3: the minor arcs in the shifted unit interval. -/
def minorArcs131 (X : ℕ) (P : ℝ) : Set ℝ :=
  Set.Icc (1 / arcQ131 X P) (1 + 1 / arcQ131 X P) \ majorArcs131 X P

/-- Display 5 on page 4: real part of the major arc integral. -/
def majorContribution131 (k X N : ℕ) (P : ℝ) : ℝ :=
  (∫ α in majorArcs131 X P,
    primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)).re

/-- Display 6 on page 4: real part of the minor arc integral. -/
def minorContribution131 (k X N : ℕ) (P : ℝ) : ℝ :=
  (∫ α in minorArcs131 X P,
    primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)).re

/-- Page 1: the even integers of J(X) = [2X/3, X]. -/
def evenJ131 (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun N : ℕ => Even N ∧ 2 * (X : ℝ) / 3 ≤ N)

/-- The corrected coefficient of display 25, with the missing factor from display 2. -/
def coefficient131 (k N : ℕ) : ℝ := 2 * LeanLab.ChenExplicit.twinC * Ck k N

/-- Page 3: the allowed range of P. This is a paper parameter condition. -/
def AdmissibleP131 (X : ℕ) (P : ℝ) : Prop :=
  (X : ℝ) ^ ((2 : ℝ) / 5) ≤ P ∧ P ≤ (X : ℝ) ^ ((41 : ℝ) / 100)

/-- CITED repair of the main conclusion on page 9, restricted to J(X).
The earlier lab audit requires the coefficient 2c0 C(k,N).
The range [1,2] of the printed theorem is not assumed. -/
def RepairedMainJ131 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((evenJ131 X).filter (fun N : ℕ =>
        η * N * Lg X ^ k < |Rpp k X N - coefficient131 k N * N * Lg X ^ k|)).card : ℝ) ≤
      K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10

end

end LeanLab.LPZ2007
