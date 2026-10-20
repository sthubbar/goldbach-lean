module

public import Mathlib
public import LeanLab.ChenExplicit.Statements

/-!
Average Goldbach representations.
P0098 A. Granville 2007, Funct. Approx. 37, Theorem 1A, read ONLY as quoted by P0060:
the Project Euclid page was behind bot protection on 2026-10-16.
P0060 G. Bhowmik and K. Halupczok, Asymptotics of Goldbach representations, arXiv 1809.06920v1,
read 2026-10-16: its Theorem 2 attributes the equivalence to Granville and says Granville's
sketch does not give RH from the asymptotic; Bhowmik, Halupczok, Matsumoto, Suzuki and
Bhowmik-Ruzsa 2018 filled the gap. KNOWN.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `G(n) = ∑_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)`; `Λ 0 = 0`, so the ends of the antidiagonal add 0. -/
def G (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, Λ p.1 * Λ p.2

/-- `C₂ = 2 ∏_{p > 2} (1 - 1/(p-1)²)`. -/
def C2 : ℝ := 2 * LeanLab.ChenExplicit.twinC

/-- `J(n) = n C₂ ∏_{p ∣ n, p > 2} (p-1)/(p-2)` for even `n`, `0` for odd `n`. -/
def J (n : ℕ) : ℝ :=
  if Even n then (n : ℝ) * C2 * ∏ p ∈ n.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- `∑_{n ≤ x} G(n) = x²/2 + O(x^{3/2+ε})` for every `ε > 0`. -/
def AvgRH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ range (N + 1), G n - (N : ℝ) ^ 2 / 2| ≤ K * (N : ℝ) ^ (3 / 2 + ε)

/-- P0060 Theorem 2, after Granville 2007 Theorem 1A: RH is equivalent to `AvgRH`.
P0060 states it with `F = G - J`; the `G` form is P0060's Appendix 4. Formerly a cited
`theorem granville_equiv`, cited, unproved; retired 2026-10-19 by PC run 20261019T1107Z-17600,
unit U-1060, into this Prop, because it is now PROVED with no cited input as
`LeanLab.GoldbachAverage.Converse.granville_equiv_proved : GranvilleEquiv` in Converse.lean. -/
def GranvilleEquiv : Prop := RiemannHypothesis ↔ AvgRH

end LeanLab.GoldbachAverage
