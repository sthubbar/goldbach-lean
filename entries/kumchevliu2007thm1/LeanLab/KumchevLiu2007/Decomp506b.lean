module

public import LeanLab.KumchevLiu2007.Decomp506bBase
public import LeanLab.KumchevLiu2007.Decomp506g
public import LeanLab.KumchevLiu2007.Decomp542a

/-!
The page 17 sieve assemblies. Shared numerical definitions are upstream.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task506b

open Real Complex MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: Page 13 Lemma 3.7 applied on page 17 display 58. The sequence is
that of page 16. At large X, every rough composite in I2 has exactly two prime
factors. Use D equal to Y to the one ninth and s equal to log D over log z.
The remainder is the explicit squarefree distribution sum, not a desired
logarithmic error bound. CITED Rosser Iwaniec upper bound sieve. -/
theorem rosser_application (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      siftedCount X B δ ε n ≤ C *
        (primeMass X B ε * sieveProduct X δ n + remainder X B ε n) := by
  exact Task506g.rosser_application_from_weights B δ ε hB hδ hδ1 hε hε1

/-- LEAF: Page 17 between displays 57 and 58. Bombieri Vinogradov with
Cauchy's inequality bounds the explicit squarefree remainder at D equal to Y
to the one ninth. This is only the distribution estimate, with no sieve product
or sifted count in its conclusion. CITED Bombieri Vinogradov input. -/
theorem bv_remainder (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  exact Task542a.bv_remainder_from_maximal A B ε hA hB hε hε1

/-- Page 17 display 58 with N bounded by display 57.
CONDITIONAL on rosser_application and bv_remainder. -/
theorem sifted_sieve_bound (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      siftedCount X B δ ε n ≤ K *
        (massScale X ε * sieveProduct X δ n + errorScale X ε A) := by
  obtain ⟨Cs, Xs, hCs, hs⟩ := rosser_application B δ ε hB hδ hδ1 hε hε1
  obtain ⟨Cr, Xr, hCr, hr⟩ := bv_remainder A B ε hA hB hε hε1
  obtain ⟨Cm, Xm, hCm, hm⟩ := prime_mass_bound B ε hB hε
  refine ⟨Cs * (Cm + Cr), max (max Xs Xr) (max Xm (Real.exp (Real.exp 1))),
    by positivity, ?_⟩
  intro X hX n hn hXn hnle
  have hXs : Xs ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXr : Xr ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXm : Xm ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXe : Real.exp (Real.exp 1) ≤ X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos _).trans_le hXe
  have hLe : Real.exp 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos _) hXe
    simpa only [Real.log_exp] using hh
  have hll : 0 ≤ Real.log (Real.log X) :=
    Real.log_nonneg ((by linarith [Real.add_one_le_exp (1 : ℝ)] : 1 ≤ Real.exp 1).trans hLe)
  have hL : 0 < Real.log X := (Real.exp_pos 1).trans_le hLe
  have hM : 0 ≤ massScale X ε := by unfold massScale Y; positivity
  have hE : 0 ≤ errorScale X ε A := by unfold errorScale Y; positivity
  have hV := sieveProduct_nonneg X δ n
  have hs' := hs X hXs n hn hXn hnle
  have hr' := hr X hXr n hn hXn hnle
  have hm' := mul_le_mul_of_nonneg_right (hm X hXm) hV
  calc _ ≤ Cs * (primeMass X B ε * sieveProduct X δ n + remainder X B ε n) := hs'
       _ ≤ Cs * (Cm * massScale X ε * sieveProduct X δ n + Cr * errorScale X ε A) :=
         mul_le_mul_of_nonneg_left (add_le_add hm' hr') hCs.le
       _ ≤ Cs * ((Cm + Cr) * (massScale X ε * sieveProduct X δ n + errorScale X ε A)) := by
         apply mul_le_mul_of_nonneg_left _ hCs.le
         have hME := mul_nonneg hM hV
         nlinarith [mul_nonneg hCr.le hME, mul_nonneg hCm.le hE]
       _ = _ := by ring

end LeanLab.KumchevLiu2007.Task506b
