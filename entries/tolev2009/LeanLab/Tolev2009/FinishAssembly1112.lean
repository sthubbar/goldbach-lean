module

public import LeanLab.Tolev2009.Decomp83
public import LeanLab.Tolev2009.MajorArc341
public import LeanLab.Tolev2009.Decomp424c

/-!
AI wrote this Lean code. Claude, route burst session 5, assembly jackpot check, 2026-11-12.
Binary Goldbach is open; this file concerns only the Tolev 2009 Theorem, display 5.

Replays `Decomp83.published_assembly` with downstream twins of its two route steps:
* `MajorArc341.major_arc_leaf : BoundE1`, proved.
* `Decomp424c.minor_arc_sup_leaf : Sup12Uniform`, proved; the leaf
  `Decomp424a.grouped_annular_decomposition` it once depended on is now proved.
The repository copy omits the lab's legacy variant about an opaque series.
-/

@[expose] public section

namespace LeanLab.Tolev2009.FinishAssembly1112

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.SeriesIdentification

/-- The published assembly, with the two steps replaced by their downstream twins. -/
theorem published_assembly_finished : TheTheorem halupczokSeries :=
  PublishedTheorem.publishedTheorem_of_display9_sup12
    MajorArc341.major_arc_leaf Decomp424c.minor_arc_sup_leaf

end LeanLab.Tolev2009.FinishAssembly1112
