module

public import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
The external explicit formula and density inputs on P0045 preprint page 5.
Zeros are indexed with multiplicity. The pole is a separate index.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- P0045 page 5: the Dirichlet L function, with zero as the unused modulus zero value. -/
def Lfun481 {r : ℕ} (χ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  if h : r = 0 then 0 else haveI : NeZero r := ⟨h⟩; DirichletCharacter.LFunction χ s

/-- P0045 display 8, pages 4 and 5: exceptional primitive character zeros.
The strict upper edge excludes the pole at one, which is added separately. -/
def zeroBox481 (X : ℕ) (H T P : ℝ) : Set (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :=
  {z | 1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun481 z.2.1 z.2.2 = 0 ∧
    1 - H / Real.log X ≤ z.2.2.re ∧ z.2.2.re < 1 ∧ |z.2.2.im| ≤ T}

/-- P0045 page 5: the Gamma quotient and power in one pair contribution. -/
def gammaPair481 (s t : ℂ) (n : ℕ) : ℂ :=
  (Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)) *
    (n : ℂ) ^ (s + t - 1)

/-- P0045 page 5: the pole has weight one and every zero has weight minus one. -/
def zeroSign481 {K : ℕ} (i : Fin (K + 1)) : ℂ := if i = 0 then 1 else -1

/-- P0045 page 5, Lemma 4.1, quoted from Pintz Theorem 10.
This is the real part of the printed formula, with its uniform remainder.
The small singular series clause retains the two divisibility conditions needed here.
The multiplicity bound rules out repeating a zero beyond its analytic order. -/
def Lemma41Statement481 : Prop :=
  ∃ c ε₀ B H₀ T₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 ≤ B ∧
    ∃ Cε : ℝ → ℕ, (∀ ε, 0 < Cε ε) ∧
    ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ P : ℝ, AdmissibleP131 X P ∧
        ∃ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
          (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
          (z 0).1 = 1 ∧ (z 0).2.2 = 1 ∧
          (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) ∧
          (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
            analyticOrderNatAt (Lfun481 w.2.1) w.2.2) ∧
          (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
          (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
          (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
            (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) ∧
          ∀ n ∈ evenJ131 X,
            |binaryMajor131 X n P -
              (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
              B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)

/-- P0045 page 5, Jutila density bound following display 8.
The sum counts analytic multiplicities, including common zeros for different characters. -/
def JutilaStatement481 : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      T ≤ P → P ≤ Real.sqrt X →
      ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
        (∀ z ∈ F, z ∈ zeroBox481 X H T P) →
        (∑ z ∈ F, (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤
          C₀ * Real.exp (4 * H)

lemma Lfun481_zero_modulus {r : ℕ} (χ : DirichletCharacter ℂ r) (s : ℂ) (h : r = 0) : Lfun481 χ s = 0 := by
  dsimp [Lfun481]
  <;> split_ifs <;> simp_all [h]
  <;> rfl



end
end LeanLab.LPZ2007
