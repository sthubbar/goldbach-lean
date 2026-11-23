module

public import LeanLab.Linnik1951.Decomp491a

/-!
P0093 pages 155, 156 and 160. The definitions of the three character terms of
equation 3.4 and the natural Ramanujan sum identity, moved character for
character from Decomp491b so that the proofs in the SPLIT files of 491 can sit
upstream of Decomp491b. No statement is changed and nothing new is defined.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- P0093 page 155 equation 2.3. Conjugate Gauss coefficient in natural residues. -/
noncomputable def conjugateGauss491 (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  star (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    χ a * Complex.exp (((2 * Real.pi * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I))

/-- P0093 page 156 equation 3.4. The signed reduced residue phase. -/
noncomputable def signedRamanujan491 (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 156 equation 3.4. One ordered character pair contribution. -/
noncomputable def characterPair491 (N q : ℕ) (n : ℤ)
    (χ ψ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (q.totient : ℂ) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ *
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      χ a * ψ a * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
    (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))

/-- P0093 page 160 equation 6.1. The principal square integral alone. -/
noncomputable def principalIntegral491 (N q : ℕ) (n : ℤ) : ℂ :=
  ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
    characterPrime280 (1 : DirichletCharacter ℂ q) N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)

/-- P0093 page 156 equation 3.4. The term I zero. -/
noncomputable def principalTerm491 (N q : ℕ) (n : ℤ) : ℂ :=
  ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
    signedRamanujan491 q n) * principalIntegral491 N q n

/-- P0093 page 156 equation 3.4. The mixed term I one, with both ordered pairs. -/
noncomputable def mixedTerm491 (N q : ℕ) [NeZero q] (n : ℤ) : ℂ :=
  ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
    (characterPair491 N q n 1 χ + characterPair491 N q n χ 1)

/-- P0093 page 156 equation 3.4. The term I two with both characters nonprincipal. -/
noncomputable def nonprincipalTerm491 (N q : ℕ) [NeZero q] (n : ℤ) : ℂ :=
  ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
    ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1),
      characterPair491 N q n χ ψ

/-- LEAF. P0093 page 161 equation 6.4. For nonnegative residuals the signed
reduced residue phase is the existing natural Ramanujan sum. -/
theorem signedRamanujan_toNat491 (q : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    signedRamanujan491 q n = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat := by
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  unfold signedRamanujan491 LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    LeanLab.Perelli1996.Kernel.e
  apply sum_congr rfl
  intro a ha
  rw [hc]
  congr 1
  push_cast
  ring

end LeanLab.Linnik1951
