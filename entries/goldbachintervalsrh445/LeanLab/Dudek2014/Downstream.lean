module

public import Mathlib
public import LeanLab.Dudek2014.Lemma5
public import LeanLab.GoldbachGaps.DudekRH
public import LeanLab.KanieckiGap.Lemma6Dudek

/-!
Unit U-1074, PC run 20261019T1503Z-1562, T1, P0100 Dudek 2014. Two downstream results that
took Dudek's Theorem 2 conclusion `hD` as a bare hypothesis now take Dudek's own analytic
inputs instead, through `Section22.theorem2_of_lemma4`, cloud U-5112, PC VERIFY U-1025:
* `GoldbachGaps.DudekRH.goldbach_gap_1478_RH`, a Goldbach number in every `(x, x + 1478]`
  for `2 ≤ x ≤ 1.6 · 10^33`, cloud U-5467;
* `KanieckiGap.lemma6_dudek`, Kaniecki 1995 Lemma 6, cloud U-5474.
The inputs are Lemma 4 with an abstract zero sum `Z`, the page 5 zero-sum bound `SigmaBd` for
the second difference of `Z`, and Schoenfeld's ψ − θ bounds, all cited, all RH consequences in
the paper. So both results are CONDITIONAL ON these inputs plus the cited computations
`EvenGoldbachUpTo (4 · 10^18)` and `GapBound1476`, never PROVED outright. The explicit formula
for ψ₁ in `PNTPort/ExplicitPsi1` has an ineffective error `K x^{-1/2}`, so it does not yet give
Lemma 4's constant 2.393; that is the gap left between the lab's zeta work and Dudek's Theorem 2.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Downstream
open Real LeanLab.Dudek2014.Section22
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- Dudek 2014's own cited analytic inputs, bundled, for an abstract zero sum `Z`. -/
structure DudekInputs (Z : ℝ → ℝ) : Prop where
  h4 : Lemma4 Z
  hS : SigmaBd (fun x h => Z (x + h) - 2 * Z x + Z (x - h))
  hSch : Schoenfeld

/-- Dudek's Theorem 2 from his inputs, restated. -/
theorem theorem2 {Z : ℝ → ℝ} (h : DudekInputs Z) :
    ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  theorem2_of_lemma4 h.h4 h.hS h.hSch

/-- **A Goldbach number in every `(x, x + 1478]`, `2 ≤ x ≤ 1.6 · 10^33`**, CONDITIONAL ON
Dudek's inputs, the `4 · 10^18` even check and `GapBound1476`. -/
theorem goldbach_gap_1478 {Z : ℝ → ℝ} (h : DudekInputs Z)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 1.6e33) :
    ∃ n : ℕ, LeanLab.GoldbachGaps.IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 :=
  LeanLab.GoldbachGaps.DudekRH.goldbach_gap_1478_RH hE hG (theorem2 h) hx hx'

/-- **Kaniecki 1995 Lemma 6**, CONDITIONAL ON Dudek's inputs and `GapBound1476`. -/
theorem kaniecki_lemma6 {Z : ℝ → ℝ} (h : DudekInputs Z) (hG : GapBound1476)
    (x : ℕ) (hx : 23 * 10 ^ 8 ≤ x) :
    (LeanLab.KanieckiGap.lam x : ℝ) < 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 :=
  LeanLab.KanieckiGap.lemma6_dudek (theorem2 h) hG x hx

end LeanLab.Dudek2014.Downstream
