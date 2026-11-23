module

public import LeanLab.Dudek2014.Downstream
public import LeanLab.Dudek2014.SigmaTrudgian

/-!
P0100, unit U-6503, CLOUD 20261020T1415Z-cloud44, 2026-10-20.
Downstream.lean with the cited `SigmaBd` discharged by `sigmaBd_of_trudgian`: for the zero sum
`Zr γ` of an ordinate family with every zero on the critical line, Dudek's Theorem 2 and the
Goldbach gap 1478 are CONDITIONAL ON Lemma 4 for that `Zr γ`, `TrudgianN70 γ`, Schoenfeld's
ψ - θ bounds, and for the gap the 4·10^18 check and `GapBound1476`. RH enters as the hypothesis
that `γ` lists the zeros, all of the form `1/2 + iγ`; Lemma 4 for this `Zr γ` is the explicit
formula for ψ₁ with error at most 2.393, still cited.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.SigmaT
open Real LeanLab.Dudek2014.Section22 LeanLab.Dudek2014.Downstream
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

variable {ι : Type*}

theorem inputs_of_trudgian {γ : ι → ℝ} (h4 : Lemma4 (Zr γ)) (hN : TrudgianN70 γ)
    (hSch : Schoenfeld) : DudekInputs (Zr γ) :=
  ⟨h4, sigmaBd_of_trudgian hN, hSch⟩

/-- Dudek's Theorem 2 with `SigmaBd` proved. -/
theorem theorem2_of_trudgian {γ : ι → ℝ} (h4 : Lemma4 (Zr γ)) (hN : TrudgianN70 γ)
    (hSch : Schoenfeld) : ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  LeanLab.Dudek2014.Downstream.theorem2 (inputs_of_trudgian h4 hN hSch)

/-- A Goldbach number in every `(x, x + 1478]`, `2 ≤ x ≤ 1.6 · 10^33`, with `SigmaBd` proved. -/
theorem goldbach_gap_1478_of_trudgian {γ : ι → ℝ} (h4 : Lemma4 (Zr γ)) (hN : TrudgianN70 γ)
    (hSch : Schoenfeld) (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 1.6e33) :
    ∃ n : ℕ, LeanLab.GoldbachGaps.IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 :=
  LeanLab.Dudek2014.Downstream.goldbach_gap_1478 (inputs_of_trudgian h4 hN hSch) hE hG hx hx'

end LeanLab.Dudek2014.SigmaT
