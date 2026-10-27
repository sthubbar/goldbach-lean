module

public import Mathlib
public import LeanLab.Routes.U1505Theta6HSW
public import LeanLab.ChirreHagen2025.U6806Theorem2Sp

/-!
Unit U-1508, T2 FRONTIER, idea I-5171, run 20261025T0416Z-19415, 2026-10-25.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Composition of `LeanLab.Routes.U1505.goldbach_445_of_J_hsw` with
`LeanLab.ChirreHagen2025.SmoothT2.theorem2_u6806` of ChirreHagen2025/U6806Theorem2Sp.lean,
specialised to the true ordinates `γ = gZ` of the nontrivial zeros of ζ with multiplicity, so
that the one `Ordinates14 gZ` input is shared by the J step and the θ step.
ChirreHagen2025 is only imported here; no file there is created or edited.

Plain statement, `goldbach_445_hsw_gZ`. Assume RH. Assume
  ExplicitA  : for every 0 < δ ≤ 10^-13 the truncated sums
               Σ_{ρ ∈ Z n} c_ρ(δ) y^ρ, c_ρ(δ) = ((1+δ)^ρ - 1)/ρ, ρ = 1/2 + iγ, γ = gZ,
               converge to -(V_δ(y) - B_δ(y)) for a.e. y ≥ 2, where
               V_δ(y) = ψ((1+δ)y) - ψ(y) - δy; Montgomery-Vaughan (12.1);
  HadamardK  : Σ_{γ' ∈ s} 4/(4 + (γ - γ')²) ≤ log |γ| for every finite set s of zeros;
  Ordinates14: every ordinate has |γ| ≥ 14;
  BPTN       : Brent-Platt-Trudgian Lemma 1 zero counts for T ≥ 10^13;
  HSWN70, HSWHead14 : Hasanalizade-Shen-Wong Corollary 1.2 zero counts, T ≥ 70 and T ≥ 14;
  the even Goldbach check up to 4·10^18.
Then for every real x ≥ 3 there is a Goldbach number n, a sum of two odd primes, with
x < n < x + 4.45 (log x)².
Schoenfeld 1976 Corollary 1, `SchoenfeldTheta`, is NOT an input.

Hypotheses by name and kind.
  RiemannHypothesis   RH, the antecedent of the conclusion.
  hE  ExplicitA gZ Z  cited analytic input, MV (12.1) truncated explicit formula; under RH.
  hH  HadamardK gZ    cited analytic input, Hadamard product bound; under RH.
  h14 Ordinates14 gZ  cited numeric fact, first zero at 14.1347; a computation, not done here.
  hB  BPTN gZ         cited numeric input, Brent-Platt-Trudgian JNT 238 2022 Lemma 1, T ≥ 10^13.
  hN  HSWN70 gZ       cited numeric input, Hasanalizade-Shen-Wong arXiv 2107.06506 Cor 1.2, T ≥ 70.
  hHd HSWHead14 gZ    cited numeric input, same corollary, head clause, T ≥ 14.
  hEv EvenGoldbachUpTo (4·10^18)  cited computation, Oliveira e Silva, Herzog, Pardi 2014.
BPTN is NOT implied by HSWN70: the HSW error 0.1038 log T + 0.2573 log log T + 10.2425 is larger
than the BPT error 0.137 log T + 0.443 log log T + 1.588 + 0.2/T for log T below about 230, so
the BPT input stays.
-/

@[expose] public section

namespace LeanLab.Routes.U1508
open Real Chebyshev
open LeanLab.ChirreHagen2025
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx)
open LeanLab.Dudek2014.SigmaH (HSWN70)

/-- Under RH, a Goldbach number in `(x, x + 4.45 log² x)` for every `x ≥ 3`, CONDITIONAL ON
ExplicitA, HadamardK, BPTN for the true ordinates `gZ`, `Ordinates14 gZ`, `HSWN70 gZ`,
`HSWHead14 gZ` and the 4·10^18 even check. No Schoenfeld input. -/
theorem goldbach_445_hsw_gZ {Z : ℕ → Finset ZIdx}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA gZ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK gZ) (h14 : SmoothT2.Ordinates14 gZ)
    (hB : RiemannHypothesis → Lemma26B.BPTN gZ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hN : HSWN70 gZ) (hHd : HSWHead14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 :=
  LeanLab.Routes.U1505.goldbach_445_of_J_hsw
    (fun hRH => SmoothT2.theorem2_u6806 (hE hRH) (hH hRH) h14 (hB hRH)) hEv hN hHd h14

/-- The same with a general ordinate family `γ` for the J step, as in U1348.goldbach_445_of_u6806,
and `gZ` only for the θ step. -/
theorem goldbach_445_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hB : RiemannHypothesis → Lemma26B.BPTN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hN : HSWN70 gZ) (hHd : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 :=
  LeanLab.Routes.U1505.goldbach_445_of_J_hsw
    (fun hRH => SmoothT2.theorem2_u6806 (hE hRH) (hH hRH) h14 (hB hRH)) hEv hN hHd h14z

end LeanLab.Routes.U1508

