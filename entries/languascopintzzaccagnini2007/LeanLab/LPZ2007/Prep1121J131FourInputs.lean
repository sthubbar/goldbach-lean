module

public import LeanLab.LanguascoPintzZaccagnini2007.Closure481

/-!
Audit of the route step `repaired_mainJ131_of_leaves481`, P0045, journal pages 774 to 775.
The sealed assembly `cor42_published131_of_leaves` calls four cited leaves that are still open.
This file states the same chain with those four published inputs as explicit hypotheses,
so the conditional statement below has no open leaf and its axioms are standard.
CONDITIONAL ON Pintz ELAZ 2004 Theorem 10, Jutila 1977, Pintz 1976 with Goldfeld and
Schinzel 1975, and Iwaniec 1974 Theorem 2, exactly as encoded in Decomp481a and Decomp481b.
No existing statement is changed. AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

/-- P0045 journal page 775, Corollary 4.2 on J of X, from the four cited inputs only.
Same proof as `cor42_published131_of_leaves`, with the cited leaves made hypotheses.
CONDITIONAL ON `Lemma41Statement481`, `JutilaStatement481`, `RealZeroStatement481`
and `IwaniecStatement481`. -/
theorem cor42_of_four_inputs1121 (hexp : Lemma41Statement481) (hjut : JutilaStatement481)
    (hzero : RealZeroStatement481) (hiw : IwaniecStatement481) :
    Cor42OnWindow131 evenJ131 := by
  intro η hη
  obtain ⟨K₁, Cstar, A, H, T, hC, hA, hH, hT, Xf, hf⟩ :=
    explicit_formula_reduction481 hexp hjut indexed_zero_count481 gamma_pair_bound481 η hη
  obtain ⟨c, hc, Xr, hr⟩ := exceptional_radical481 davenport_classification481
    hzero hiw H T hH hT
  refine ⟨K₁, Cstar, c, A, hC, hc, hA, max Xf Xr, ?_⟩
  intro X hX
  obtain ⟨P, E, hP, hcard, hsource, hgood, hall⟩ :=
    hf X ((le_max_left _ _).trans hX)
  refine ⟨P, E, hP, ⟨hcard, ?_⟩, hgood, hall⟩
  intro r hmem
  obtain ⟨z, hz, hzr⟩ := hsource r hmem
  simpa only [hzr] using hr X ((le_max_right _ _).trans hX) P hP z hz

/-- P0045 journal page 776 onward, the repaired main theorem on J of X, display 25 with the
corrected coefficient. CONDITIONAL ON the four published inputs only, with no open leaf. -/
theorem repaired_mainJ131_of_four_inputs1121 (hexp : Lemma41Statement481)
    (hjut : JutilaStatement481) (hzero : RealZeroStatement481) (hiw : IwaniecStatement481) :
    RepairedMainJ131 :=
  repaired_main_cor42_supply383 (cor42_of_four_inputs1121 hexp hjut hzero hiw)

end LeanLab.LPZ2007

