module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Merged copy, PC run 20261020T0503Z-11094, unit U-1167: the repo encoding of P0083, moved under the
namespace LeanLab.Perelli1996.B in Perelli1996/B so it builds beside the OneDrive encoding A.
Content unchanged apart from the namespace and import paths.
P0083 A. Perelli, "Goldbach numbers represented by polynomials", Rev. Mat. Iberoamericana 12
(1996), no. 2, 477-490. Read 2026-10-18 from the open EMS Press copy, doi 10.4171/RMI/205,
pages 477 and 478, formulas from the rendered page images.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Theorem 1 and Corollary 1 are unconditional almost-all results.

Readings: `F ∈ ℤ[x]` with `deg F = k ≥ 1` and positive leading coefficient; `N` is a large
positive real, `L = log N`. The window `N^{1/k} ≤ n ≤ N^{1/k} + H` runs over natural numbers.
`R` and `𝔖` are applied to `F(n)` read as a natural number; in the window `F(n) > 0` for large
`N`. `≪_{A,ε,F}` becomes `∃ K N₀, ∀ N ≥ N₀`, uniform in `H`.
-/

@[expose] public section

namespace LeanLab.Perelli1996.B
open Finset Real Polynomial
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `R(n) = ∑_{r + s = n} Λ(r) Λ(s)`, page 477. -/
def R (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, Λ p.1 * Λ p.2

/-- `𝔖(n) = ∏_{p ∤ n} (1 - 1/(p-1)²) ∏_{p | n} (1 + 1/(p-1))`, page 477, as one product over
all primes. -/
def Sing (n : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime},
    if p.1 ∣ n then 1 + 1 / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

/-- `F(n)` as an integer. -/
def Fv (F : ℤ[X]) (n : ℕ) : ℤ := F.eval (n : ℤ)

/-- The error `R(F(n)) - F(n) 𝔖(F(n))`. -/
def Delta (F : ℤ[X]) (n : ℕ) : ℝ :=
  R (Fv F n).toNat - (Fv F n : ℝ) * Sing (Fv F n).toNat

/-- The window `N^{1/k} ≤ n ≤ N^{1/k} + H`, `k = deg F`. -/
def win (F : ℤ[X]) (N H : ℝ) : Finset ℕ :=
  Icc ⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ ⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊

/-- The admissible polynomials: degree `k ≥ 1`, positive leading coefficient. -/
def Admissible (F : ℤ[X]) : Prop := 1 ≤ F.natDegree ∧ 0 < F.leadingCoeff

/-- Theorem 1, page 478: for `A, ε > 0` and `N^{1/(3k)+ε} ≤ H ≤ N^{1/k}`,
`∑_{N^{1/k} ≤ n ≤ N^{1/k}+H} |R(F(n)) - F(n) 𝔖(F(n))|² ≪_{A,ε,F} H N² L^{-A}`. -/
def Theorem1 : Prop :=
  ∀ F : ℤ[X], Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ K N₀ : ℝ, ∀ N H : ℝ, N₀ ≤ N →
    N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∑ n ∈ win F N H, Delta F n ^ 2 ≤ K * H * N ^ 2 * Real.log N ^ (-A)

/-- Corollary 1, first assertion: `R(F(n)) = F(n) 𝔖(F(n)) + O(N L^{-A})` for all `n` in the
window but `O(H L^{-A})` exceptions; `C₁` is the constant of the `O(N L^{-A})`. -/
def Cor1a : Prop :=
  ∀ F : ℤ[X], Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C₁ C₂ N₀ : ℝ, ∀ N H : ℝ, N₀ ≤ N →
    N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (((win F N H).filter (fun n => C₁ * N * Real.log N ^ (-A) < |Delta F n|)).card : ℝ) ≤
        C₂ * H * Real.log N ^ (-A)

/-- `ρ_F(d) = |{m mod d : F(m) ≡ 0 mod d}|`, page 478. -/
def rho (F : ℤ[X]) (d : ℕ) [NeZero d] : ℕ :=
  (Finset.univ.filter (fun m : ZMod d => (F.map (Int.castRingHom (ZMod d))).eval m = 0)).card

/-- `A_F(N, H) = {N^{1/k} ≤ n ≤ N^{1/k} + H : F(n) ≡ 0 mod 2}`, page 478. -/
def AF (F : ℤ[X]) (N H : ℝ) : Finset ℕ := (win F N H).filter (fun n => Even (Fv F n))

/-- Corollary 1, second assertion: if `ρ_F(2) ≠ 0`, then for all `n ∈ A_F(N, H)` but
`O(H L^{-A})` exceptions, `F(n)` is a Goldbach number. -/
def Cor1b : Prop :=
  ∀ F : ℤ[X], Admissible F → rho F 2 ≠ 0 → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
    ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
        (((AF F N H).filter (fun n => ¬ IsGoldbachSum (Fv F n).toNat)).card : ℝ) ≤
          C * H * Real.log N ^ (-A)

end

end LeanLab.Perelli1996.B
