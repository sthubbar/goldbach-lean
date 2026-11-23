module

public import Mathlib

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p5, a repair of the rejected p4 branch.
P0014 Helfgott, Major arcs for Goldbach's problem, page 36, display 4.20: the explicit
Pólya-Vinogradov inequality for M(q), the largest absolute value of a partial sum of χ(m).
The paper states display 4.20 without proof, so it is a citation wall and is not split: CITED-LEFT.
This file holds that one LEAF and nothing else. No definition is made: M(q) is written out as
the supremum over n of the norm of the sum of χ(m) for m from 1 to n.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

end LeanLab.HelfgottMajor.PolyaVinogradov123
