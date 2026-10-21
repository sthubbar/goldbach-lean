module

public import Mathlib
public import LeanLab.GoldbachAverage.Statements

/-!
Explicit formulas for the average of Goldbach representations, under RH.
P0052 D. A. Goldston and L. Yang, The average number of Goldbach representations,
arXiv 1601.06902v1, read 2026-10-16 with pdftotext; Theorem 1 there is attributed to
Languasco-Zaccagnini, Proc. AMS 140, 2012, arXiv 1011.3198, also read.
Zeros are counted with multiplicity by `analyticOrderNatAt`; the sums converge absolutely.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- Nontrivial zeros of ζ: zeros in the open critical strip. -/
def NontrivialZero : Type := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `Σ_ρ m(ρ) f(ρ)` over nontrivial zeros with multiplicity `m(ρ)`. -/
def zeroSum (f : ℂ → ℂ) : ℂ :=
  ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1

/-- `Σ_ρ N^{ρ+1} / (ρ(ρ+1))`. -/
def Z1 (N : ℝ) : ℂ := zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))

/-- Goldston-Yang eq. 2.1 AS PRINTED, coefficient 1 on the zero sum. FINDING F-0004: this is a
misprint for the Languasco-Zaccagnini formula, coefficient 2; under RH it is false, since the zero sum is not `O(N log³ N)`.
Kept as a `def`, not asserted. -/
def gy_eq2_1_printed : Prop := ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + Z1 N‖ ≤ K * N * Real.log N ^ 3

/-- If both the true and the printed formula held, the zero sum would be `O(N log³ N)`. -/
theorem printed_forces_small
    (hLZ : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
        ≤ K * N * Real.log N ^ 3) (hP : gy_eq2_1_printed) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → ‖Z1 N‖ ≤ K * N * Real.log N ^ 3 := by
  obtain ⟨K1, h1⟩ := hLZ
  obtain ⟨K2, h2⟩ := hP
  refine ⟨K1 + K2, fun N hN => ?_⟩
  have e : Z1 N = (((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N)
      - (((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + Z1 N) := by ring
  rw [e]
  calc _ ≤ ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
        + ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + Z1 N‖ := norm_sub_le _ _
    _ ≤ K1 * N * Real.log N ^ 3 + K2 * N * Real.log N ^ 3 := add_le_add (h1 N hN) (h2 N hN)
    _ = (K1 + K2) * N * Real.log N ^ 3 := by ring

end LeanLab.GoldbachAverage
