module

public import LeanLab.PrimePowerWindow.Display
public import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian
public import LeanLab.Dudek2014.SigmaHSW

/-!
# Dudek 2014 Theorem 2 on the corrected `N(T)` bound

P0100, unit U-6650, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics.

`theorem2_of_RH_hsw`: Dudek 2014 Theorem 2 under RH, conditional on the zero count `HSWN70` of
Hasanalizade, Shen and Wong, arXiv 2107.06506, Corollary 1.2, through `SigmaH.sigmaBd_of_hsw`.
The prime power window input is proved, `PrimePowerWindow.window_holds`. This copy keeps only
Theorem 2; the lab file also derives Goldbach gap and Kaniecki corollaries, not used here.
-/

@[expose] public section

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- **Dudek 2014 Theorem 2 under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` only.** -/
theorem theorem2_of_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) :
    ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x := by
  refine LeanLab.Dudek2014.Section22.theorem2_of_lemma4_window lemma4_Zpatch ?_
  have hS := LeanLab.Dudek2014.SigmaH.sigmaBd_of_hsw hN
  intro x hx
  obtain ⟨h0, h1⟩ := LeanLab.Dudek2014.Section22.hD_small hx
  have := hS x hx
  simp only at this ⊢
  rw [sigma_patch hx]
  rwa [Zr_eq_Zreal hRH (by linarith), Zr_eq_Zreal hRH (by linarith),
    Zr_eq_Zreal hRH (by linarith)] at this

end LeanLab.PNTPort.ExplicitPsi1.Trivial
