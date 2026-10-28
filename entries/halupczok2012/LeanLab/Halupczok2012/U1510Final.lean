module

public import LeanLab.Halupczok2012.U1495PPS
public import LeanLab.Halupczok2012.U1496PP

/-!
# Halupczok 2012, Theorem 1.2 repaired, conditional on two cited inputs

AI wrote this Lean code, Claude, Anthropic. Checked by the Lean kernel. Binary Goldbach is open.

The final form of the repair of Theorem 1.2 of K. Halupczok, JTNB 25, 2013, pp. 333 to 334,
Theorem 2 of arXiv 1212.4406; the lab calls the defect finding F-0008, see `NonCoprime`.

It rests on exactly two cited inputs, both checked against page images of the sources and
taken as explicit hypotheses, never as axioms:

* `PPS1984Remark`: the printed REMARK of Perelli, Pintz and Salerno 1984, Ann. Scuola Norm. Sup.
  Pisa 11, p. 530, with display 2 of p. 529, in its uniform reading. A reading of the proof on
  pp. 531 to 538 found that the only dependence on `θ` is `δ = δ(θ)` in display 5 on p. 531,
  which can be taken absolute. The paper quotes this result as its Theorem 2.1, JTNB p. 338.
* `PP1993Goldbach`: the unnumbered Goldbach analogue of Theorem 3 of Perelli and Pintz 1993,
  J. London Math. Soc. 47, pp. 44 to 46, displays 1, 3, 4 and 5. It replaces the paper's
  Theorem 2.3, JTNB p. 339, which the paper itself calls an adaptation of its reference [11].

The axioms of these theorems are `propext`, `Classical.choice` and `Quot.sound` only.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

/-- The repair of Theorem 1.2, all `q ≤ Q` with `T0`, CONDITIONAL ON `PPS1984Remark` and
`PP1993Goldbach`. -/
theorem theorem2Zeroed_U1510 (hR : PPS1984Remark) (hPP : PP1993Goldbach) :
    Theorem2Zeroed :=
  theorem2Zeroed_U1496 (theorem3_of_uniform (uniform_of_remark hR)) hPP

/-- Theorem 2 in the coprime reading, CONDITIONAL ON `PPS1984Remark` and `PP1993Goldbach`. -/
theorem theorem2_U1510 (hR : PPS1984Remark) (hPP : PP1993Goldbach) : Theorem2 :=
  theorem2_U1496 (theorem3_of_uniform (uniform_of_remark hR)) hPP

/-- The paper's own quoted Theorem 2.1, the lab's `Theorem3`, follows from the printed Remark. -/
theorem theorem3_of_remark (hR : PPS1984Remark) : Theorem3 :=
  theorem3_of_uniform (uniform_of_remark hR)

/-- The paper's own Theorem 2.3, the lab's `Theorem5`, follows from `PP1993Goldbach`. -/
theorem theorem5_of_PP1993 (hPP : PP1993Goldbach) : Theorem5 :=
  theorem5_of_PP hPP

end LeanLab.Halupczok2012

