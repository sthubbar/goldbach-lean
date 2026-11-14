module

public import LeanLab.RieselVaughan1983.Assembly
public import LeanLab.RieselVaughan1983.Section9
public import LeanLab.RieselVaughan1983.Lemma9

/-!
P0032 Riesel-Vaughan 1983: the Theorem with (9.1) replaced by Lemmas 9 and 14.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.RieselVaughan1983

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at the four table rows of Lemma 8, Lemma 6 (i) and (ii), (2.30) and (2.31),
Rosser-Schoenfeld (3.3), Lemma 9 and Lemma 14. -/
theorem theorem_of_lemmas (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33) (h9 : Lemma9P)
    (h14 : Lemma14P) : Theorem :=
  theorem_of h24 h42 h278 h396 h6 hTab hRS (display91_of h9 h14 h6 h6')

/-- The nineteen prime form under the same inputs. -/
theorem corollary19_of_lemmas (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33) (h9 : Lemma9P)
    (h14 : Lemma14P) : Corollary19 :=
  corollary19_of h24 h42 h278 h396 h6 hTab hRS (display91_of h9 h14 h6 h6')

/-- **The Theorem** with Lemma 9 discharged: CONDITIONAL ON Lemma 5 at five rows, the four of
Lemma 8 and `Lemma5Neg` at `(60, 8.3)`, Lemma 6 (i) and (ii), (2.30) and (2.31),
Rosser-Schoenfeld (3.3) and Lemma 14. -/
theorem theorem_of_lemma5_14 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33)
    (h14 : Lemma14P) : Theorem :=
  theorem_of_lemmas h24 h42 h278 h396 h6 h6' hTab hRS (lemma9_of h5) h14

end LeanLab.RieselVaughan1983
