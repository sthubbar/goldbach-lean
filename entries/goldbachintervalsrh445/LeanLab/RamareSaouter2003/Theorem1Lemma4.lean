module

public import LeanLab.RamareSaouter2003.Theorem1Dudek
public import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4

/-!
P0099, unit U-6551, CLOUD 20261020T1518Z-cloud45, 2026-10-20.
Ramaré-Saouter 2003 Theorem 1 with Dudek's Lemma 4 discharged: the lab now proves Lemma 4, the
explicit formula for ψ₁ with error at most 2.393, in PNTPort/ExplicitPsi1/DudekLemma4.lean, so
Theorem 1 is CONDITIONAL ON the page 5 zero sum bound `SigmaBd` for the zero sum `Zreal` and
Schoenfeld's ψ - θ bounds only.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.RamareSaouter2003
open Real LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- **Theorem 1, CONDITIONAL ON `SigmaBd` for `Zreal` and Schoenfeld only.** -/
theorem theorem1_of_sigmaBd
    (hS : LeanLab.Dudek2014.Section22.SigmaBd (fun x h => Zreal (x + h) - 2 * Zreal x + Zreal (x - h)))
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x :=
  theorem1_of_dudek (theorem2_of_sigmaBd hS hSch)

end LeanLab.RamareSaouter2003
