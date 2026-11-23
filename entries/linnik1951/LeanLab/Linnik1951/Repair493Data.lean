module

public import LeanLab.Linnik1951.Conventions
public import LeanLab.Perelli1996.Sing

/-!
P0093 pages 154, 165, 167 and 168. Shared data for the repaired error bound.
Sealed data move with identical declarations. AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- Ordered representations in P0093 equation 2.1, page 154.
The finite bounds lose no representations because each summand is at most N. -/
noncomputable def representationCount111 (k N : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun t : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) =>
    (t.1.val).Prime ∧ (t.2.1.val).Prime ∧ (∀ i, 1 ≤ (t.2.2 i).val) ∧
      N = t.1.val + t.2.1.val + ∑ i, 2 ^ (t.2.2 i).val).card

/-- Singular series in P0093 page 168, equation 10.6. -/
noncomputable def singularSeries111 (n : ℕ) : ℝ :=
  ∏' p : Nat.Primes, if (p : ℕ) ∣ n then
    1 + 1 / (((p : ℕ) : ℝ) - 1) else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2

/-- Main term in P0093 page 168 after equation 10.7, with multiplicity of exponent tuples. -/
noncomputable def mainTerm111 (k N : ℕ) : ℝ := by
  classical
  exact ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
      Even (N - ∑ i, 2 ^ (ν i).val)),
    singularSeries111 (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2

/-- The positive scale in P0093 Section 11, page 169. -/
noncomputable def scale111 (k N : ℕ) : ℝ :=
  N * (Real.log N / Real.log 2) ^ (k - 2)

/-- P0093 page 154, the exponentially damped prime series S. Local copy of
primeFourier111. -/
noncomputable def primeSeriesSplit111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- P0093 pages 154 and 161, the damped series T over positive powers of two.
Local copy of powerFourier111. -/
noncomputable def powerSeriesSplit111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑' m : ℕ,
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)

/-- P0093 page 165 Section 8. Major arcs with Q equal to N to the one tenth and
tau equal to N to the one seventh. Local copy of majorArcs280. -/
noncomputable def majorArcsSplit111 (N : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
    |α - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))}

/-- P0093 pages 162 and 167. Minor points where T is large. Local copy of
exceptionalArcs280. -/
noncomputable def exceptionalArcsSplit111 (N : ℕ) (η : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ α ∉ majorArcsSplit111 N ∧
    (1 - η) * ‖powerSeriesSplit111 N 0‖ < ‖powerSeriesSplit111 N α‖}

/-- P0093 page 167 before equation 10.1. The remaining minor points. Local copy
of goodMinorArcs280. -/
noncomputable def goodMinorArcsSplit111 (N : ℕ) (η : ℝ) : Set ℝ :=
  Set.Icc 0 1 \ (majorArcsSplit111 N ∪ exceptionalArcsSplit111 N η)

/-- P0093 pages 154 and 167, equations 2.2 and 10.2. Real contribution of an
arc set, including the factor e from exponential damping. Local copy of
arcContribution280. -/
noncomputable def arcContributionSplit111 (k N : ℕ) (s : Set ℝ) : ℝ :=
  Real.exp 1 * (∫ α in s, primeSeriesSplit111 N α ^ 2 * powerSeriesSplit111 N α ^ k *
    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re

end LeanLab.Linnik1951
