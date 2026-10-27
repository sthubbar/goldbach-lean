module

public import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian

/-!
# Dudek's inputs discharged, and the lab's two downstream uses

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6553. AI wrote this file. Known mathematics.

* `dudekInputs_Zpatch`: the bundle `Dudek2014.Downstream.DudekInputs` holds for `Zpatch` under RH,
  CONDITIONAL ON Trudgian's `N(T)` bound for the zeros and Schoenfeld's `ψ - θ` bounds;
* `goldbach_gap_1478_RH_trudgian`: a Goldbach number in every `(x, x + 1478]`, `2 ≤ x ≤ 1.6·10^33`,
  under RH, CONDITIONAL ON those two, the `4·10^18` even Goldbach check and `GapBound1476`;
* `kaniecki_lemma6_RH_trudgian`: Kaniecki 1995 Lemma 6 under RH on the same inputs, without
  the even check.
Binary Goldbach is OPEN; these are conditional statements about short intervals.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- **Dudek's three inputs hold for `Zpatch`** under RH, from Trudgian and Schoenfeld. -/
theorem dudekInputs_Zpatch (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    LeanLab.Dudek2014.Downstream.DudekInputs Zpatch := by
  refine ⟨lemma4_Zpatch, ?_, hSch⟩
  have hS := LeanLab.Dudek2014.SigmaT.sigmaBd_of_trudgian hN
  intro x hx
  obtain ⟨h0, h1⟩ := LeanLab.Dudek2014.Section22.hD_small hx
  have := hS x hx
  simp only at this ⊢
  rw [sigma_patch hx]
  rwa [Zr_eq_Zreal hRH (by linarith), Zr_eq_Zreal hRH (by linarith),
    Zr_eq_Zreal hRH (by linarith)] at this

/-- **Goldbach numbers in every `(x, x + 1478]`, `2 ≤ x ≤ 1.6·10^33`**, under RH, CONDITIONAL ON
Trudgian's `N(T)`, Schoenfeld, the `4·10^18` even check and `GapBound1476`. -/
theorem goldbach_gap_1478_RH_trudgian (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 1.6e33) :
    ∃ n : ℕ, LeanLab.GoldbachGaps.IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 :=
  LeanLab.GoldbachGaps.DudekRH.goldbach_gap_1478_RH hE hG (theorem2_of_RH_trudgian hRH hN hSch) hx hx'

/-- **Kaniecki 1995 Lemma 6** under RH, CONDITIONAL ON Trudgian's `N(T)`, Schoenfeld and
`GapBound1476`. -/
theorem kaniecki_lemma6_RH_trudgian (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) (hG : GapBound1476)
    (x : ℕ) (hx : 23 * 10 ^ 8 ≤ x) :
    (LeanLab.KanieckiGap.lam x : ℝ) < 1 / (4 * Real.pi) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 :=
  LeanLab.KanieckiGap.lemma6_dudek (theorem2_of_RH_trudgian hRH hN hSch) hG x hx

end LeanLab.PNTPort.ExplicitPsi1.Trivial
