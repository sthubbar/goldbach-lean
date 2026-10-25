module

public import Mathlib

/-!
# Density versions of the binary Goldbach problem, Alsetri and Shao, Theorem 1.2

A. Alsetri and X. Shao, *Density versions of the binary Goldbach problem*, arXiv 2405.18576v2,
Acta Arith. 218, 2025, pages 285 to 295. For a set `A` of primes and a reduced residue class
`b mod W`, the relative lower density of `A` in that class is

`δ(A; W, b) = liminf_{N → ∞} |A ∩ {1 ≤ n ≤ N : n ≡ b mod W}| / |P ∩ {1 ≤ n ≤ N : n ≡ b mod W}|`,

here `lowerDensityRes A b W`.

The paper's results:
* `LeanLab.DensityGoldbach.U1502.alsetriShao_1_2`: Theorem 1.2. If `A ⊆ P` and
  `inf_{W, b} δ(A; W, b) > 1/2`, the infimum over all reduced classes `b mod W`, then almost all
  even positive integers are `p₁ + p₂` with `p₁, p₂ ∈ A`. The infimum condition is written as one
  `η > 1/2` with `η ≤ δ(A; W, b)` for every `W > 0` and every `b` coprime to `W`; "almost all" is
  read as: the number of even `n ≤ X` that are not such a sum, divided by `X`, tends to `0`.
* `LeanLab.DensityGoldbach.AlsetriShaoThm11.theorem1_1`: Theorem 1.1. For every `ε > 0` some
  `A ⊆ P` has relative lower density in the primes above `1 − ε`, written as a lower bound
  `δ π(N) ≤ |A ∩ [0, N]|` for all large `N` with a constant `δ > 1 − ε`, while at least `c N` of
  the even `n ≤ N` are not a sum of two elements of `A`, for a constant `c > 0` and all large `N`.
* `LeanLab.DensityGoldbach.AlsetriShaoSharp.remark1_3`: Remark 1.3, the constant `1/2` is sharp.
  For every `c < 1/2` some `A ⊆ P` has, in every reduced class, a constant `δ > c` with
  `δ π(N; W, b) ≤ |A ∩ [0, N] ∩ {n ≡ b mod W}|` for all large `N`, while at least `κ N` of the even
  `n ≤ N` are not a sum of two elements of `A`, for a constant `κ > 0` and infinitely many `N`.

Derived result of this entry, not a result of the paper; it checks that the hypothesis of
Theorem 1.2 can be met:
* `LeanLab.DensityGoldbach.U1506.hyp_satisfiable`: the hypothesis holds for `A = P`, `η = 3/4`.

Binary Goldbach is open; nothing here claims it. Theorem 1.2 is a statement about almost all even
numbers. An AI agent, Claude by Anthropic, wrote the Lean code. Lean names keep the namespaces of
the lab where the proofs were written.
-/

@[expose] public section

open Finset Filter
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach

/-- The primes as a set. -/
def P : Set ℕ := {p | p.Prime}

/-- Relative lower density of `A` in the reduced residue class `b mod W`. -/
def lowerDensityRes (A : Set ℕ) (b W : ℕ) : ℝ :=
  liminf (fun N : ℕ =>
    (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime ∧ n % W = b % W} : ℝ) /
      #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W}) atTop

/-- Alsetri-Shao 2024, Theorem 1.2: if every reduced residue class density is at least some
`η > 1/2`, almost all even `N` are `p₁ + p₂` with `p₁, p₂ ∈ A`: the exceptional even
`n ≤ X` are `o(X)`. -/
def AlsetriShao12 : Prop := ∀ A : Set ℕ, A ⊆ P → ∀ η : ℝ, 1 / 2 < η →
  (∀ W b : ℕ, 0 < W → Nat.Coprime b W → η ≤ lowerDensityRes A b W) →
  Tendsto (fun X : ℕ =>
    (#{n ∈ Icc 1 X | Even n ∧ ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = n} : ℝ) / X) atTop (nhds 0)

end LeanLab.DensityGoldbach

namespace LeanLab.DensityGoldbach.U1502

/-- **Alsetri-Shao 2024, Theorem 1.2**, with no hypothesis beyond the theorem's own: for `A` a set
of primes with relative lower density at least some `η > 1/2` in every reduced class, almost all
even numbers are a sum of two elements of `A`. -/
theorem alsetriShao_1_2 : LeanLab.DensityGoldbach.AlsetriShao12 := by
  sorry

end LeanLab.DensityGoldbach.U1502

namespace LeanLab.DensityGoldbach.U1506

/-- Derived result of this entry, not a result of the paper: the hypotheses of `AlsetriShao12`
are satisfiable, by `A = P` and `η = 3/4`. -/
theorem hyp_satisfiable : P ⊆ P ∧ (1 / 2 : ℝ) < 3 / 4 ∧
    ∀ W b : ℕ, 0 < W → Nat.Coprime b W → (3 / 4 : ℝ) ≤ lowerDensityRes P b W := by
  sorry

end LeanLab.DensityGoldbach.U1506

namespace LeanLab.DensityGoldbach.AlsetriShaoThm11

open Finset

open Classical in
/-- **Alsetri-Shao 2024, Theorem 1.1.** For every `ε > 0` there is a set `A` of primes whose
relative lower density in the primes exceeds `1 - ε`, written as a lower bound
`δ π(N) ≤ |A ∩ [0, N]|` for all large `N` with `δ > 1 - ε`, while a positive proportion of even
numbers, at least `c N` of those up to `N`, are not `p + q` with `p, q ∈ A`. -/
theorem theorem1_1 : ∀ ε : ℝ, 0 < ε → ∃ A : Set ℕ, (∀ p ∈ A, p.Prime) ∧
    (∃ δ : ℝ, 1 - ε < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      δ * (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤
        (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.range (N + 1)).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)).card : ℝ)) := by
  sorry

end LeanLab.DensityGoldbach.AlsetriShaoThm11

open Real Finset Filter

namespace LeanLab.DensityGoldbach.AlsetriShaoSharp

open Classical in
/-- **Alsetri-Shao 2024, Remark 1.3.** The constant `1/2` in Theorem 1.2 is sharp: for every
`c < 1/2` there is a set `A` of primes with relative lower density above `c` in every reduced
class, while `A + A` misses a positive proportion of the even integers up to infinitely many
`N`. -/
theorem remark1_3 : ∀ c : ℝ, c < 1 / 2 → ∃ A : Set ℕ, (∀ p ∈ A, p.Prime) ∧
    (∀ W b : ℕ, 1 ≤ W → Nat.Coprime b W → ∃ δ : ℝ, c < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      δ * (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % W = b % W)).card : ℝ) ≤
        (((Finset.range (N + 1)).filter (fun p => p ∈ A ∧ p % W = b % W)).card : ℝ)) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      κ * (N : ℝ) ≤ (((Finset.range (N + 1)).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)).card : ℝ)) := by
  sorry

end LeanLab.DensityGoldbach.AlsetriShaoSharp
