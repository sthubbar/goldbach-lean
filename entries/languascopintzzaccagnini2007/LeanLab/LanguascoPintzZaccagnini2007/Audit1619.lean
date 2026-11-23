module

public import LeanLab.LanguascoPintzZaccagnini2007.Dyadic131
public import LeanLab.LanguascoPintzZaccagnini2007.PrimeRepresentations131

/-!
P0045 U-1619. Axiom report for the two parameter route of U-1617 section 4, applied in Decomp131.
The route lemmas take the leaves as hypotheses, so a clean line below means no other open proof.
`repaired_mainJ131` then rests on `cor42_published131` and `major_arcs_combine131` only.
`cor42_window_extension131` is not used. It stays in DecompJ218 as text, retirement is the main
thread's call. AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

/-- The implication of the route, no open proof: the two leaves give the sealed conclusion. -/
theorem route_of_leaves1619 (hcor : Cor42OnWindow131 evenJ131)
    (hcomb : SingularAverageStatement131) : RepairedMainJ131 :=
  repaired_main_of_narrow1619 (narrow_count1619
    (fun k hk ε hε => major_asymptotic_narrow1619 hcor hcomb k hk ε hε))

end LeanLab.LPZ2007

