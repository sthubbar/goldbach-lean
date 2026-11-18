module

public import LeanLab.KumchevLiu2007.Trunc129BV
public import LeanLab.KumchevLiu2007.Trunc129Sieve
public import LeanLab.KumchevLiu2007.Trunc129Mass

/-!
Kumchev and Liu, arXiv 0801.0130, paper P0088, pages 16 and 17, displays 56 to 59.
Truncated window version of the sieve bound of display 58, with no hypotheses: the
three inputs of `trunc_sifted_sieve_bound_of`, namely the truncated Bombieri Vinogradov
remainder bound, the truncated upper bound sieve and the truncated support bridge, are
supplied by the proved theorems of Trunc129BV and Trunc129Sieve.
This file declares no definition. AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Trunc129

open Real MeasureTheory LeanLab.KumchevLiu2007 Task506b
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 17 display 58 with N bounded as in page 16 display 57, truncated window
version. For n in H2 strictly between X and X plus Y, the sifted pair count of page 16
display 56 is at most a constant times the truncated window length
sqrt Y minus max (sqrt Y / 2) (sqrt (n - X)), times L to the -2 log L times the sieve
product, plus the error Y to the 1/2 L to the -A. Proved from the truncated remainder
bound, the truncated upper bound sieve and the truncated mass bound. -/
theorem trunc_sifted_sieve_bound (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → (n : ℝ) < X + Y X ε →
      siftedCount X B δ ε n ≤ K *
        ((Real.sqrt (Y X ε) - max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X))) * Real.log X ^ (-2 : ℝ) *
            Real.log (Real.log X) * sieveProduct X δ n + errorScale X ε A) :=
  trunc_sifted_sieve_bound_of trunc_bv_remainder trunc_rosser trunc_sifted_le
    A B δ ε hA hB hδ hδ1 hε hε1


end LeanLab.KumchevLiu2007.Trunc129
