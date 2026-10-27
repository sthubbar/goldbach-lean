module

public import Mathlib
public import LeanLab.Routes.U1505Theta6
public import LeanLab.PNTPort.ExplicitPsi1.ThetaSchoenfeldLarge

/-!
Unit U-1505, T3 CONNECTION SWEEP, run 20261023T1343Z-19109. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics. Binary Goldbach is OPEN.

`goldbach_445_of_J_hsw`: the RH Goldbach interval `(x, x + 4.45 log² x)` from a J_ψ constant
1.0069, CONDITIONAL ON that J_ψ bound, the 4·10^18 even check, and the three zero-count inputs
`HSWN70 gZ`, `HSWHead14 gZ`, `Ordinates14 gZ` for the true ordinates, under RH. Schoenfeld 1976
Corollary 1, `SchoenfeldTheta`, is no longer an input: it is replaced by the lab's own
`theta_schoenfeld_large`, PNTPort/ExplicitPsi1/ThetaSchoenfeldLarge.lean.
-/

@[expose] public section

namespace LeanLab.Routes.U1505
open Real Chebyshev
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.U1348
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)

/-- `ThetaRel6` under RH from the three zero-count inputs, no Schoenfeld. -/
theorem thetaRel6_of_RH_hsw (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) : ThetaRel6 :=
  thetaRel6_of_large fun _ hu =>
    LeanLab.PNTPort.ExplicitPsi1.Trivial.theta_schoenfeld_large hRH hN hH h14 hu

/-- Under RH, a Goldbach number in `(x, x + 4.45 log² x)` for every `x ≥ 3`, CONDITIONAL ON the
J_ψ bound with constant 1.0069, the 4·10^18 even check and `HSWN70`, `HSWHead14`, `Ordinates14`
for the true zeros. -/
theorem goldbach_445_of_J_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 :=
  goldbach_445_of_J_T6 h2 hE fun hRH => thetaRel6_of_RH_hsw hRH hN hH h14

end LeanLab.Routes.U1505

