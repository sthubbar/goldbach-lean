module

public import Mathlib

/-!
Density versions of the binary Goldbach problem, after A. Alsetri and X. Shao 2024, arXiv
2405.18576, Density versions of the binary Goldbach problem, Theorem 1.2.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0081.
Checked by the Lean kernel. Binary Goldbach is open.

This copy keeps the definitions used by the Alsetri-Shao 2024 entry. The lab file also states,
without proof, results of Shao 2012 and of Li and Pan 2007 and Theorem 1.1 of Alsetri and Shao in
another form; those statements and the definitions only they use were removed, see PORTING.md.
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
