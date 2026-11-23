module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.BhowmikGrimmelt2026.SPLIT_meanSquare38
public import LeanLab.BhowmikGrimmelt2026.SingularTail150
public import LeanLab.BhowmikGrimmelt2026.ZeroBoundLeaf150
public import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150
public import LeanLab.BhowmikGrimmelt2026.ModelL2_150
public import LeanLab.BhowmikGrimmelt2026.Coefficients150
public import LeanLab.BhowmikGrimmelt2026.SingularTailAbs150
public import LeanLab.BhowmikGrimmelt2026.ArcTails150
public import LeanLab.BhowmikGrimmelt2026.MeanSquareLeaves150

/-!
Theorem 3.1, P0029 pages 9 to 13.
OPEN leaves for Jules. The assembly is CONDITIONAL on these leaves.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/- SPLIT piece 1 of `zeroBound_lower150`, `hardy_critical_line_zero150`, is the LEAF of
`ZeroBoundLeaf150.lean`: it is CITED and OPEN, and lives in its own file so that this existing
file carries no step it did not have before. -/

/-! ### Split of `mean_square150`, burst 20261112

P0029 pages 12 and 13 obtain display 3.8 from three ingredients: on each Farey arc the main
term of 3.5, summed over reduced residues and then over `q ≤ Q ≍ N ^ (1/2)`, gives the truncated
singular series `N Σ_{q ≤ Q} μ(q)² c_q(N) / φ(q)²`, which equals `N 𝔖(N) + O(N ^ (1/2 + ε))`
by the display on page 12; Parseval together with the zero bound 3.7 controls the mean square of
`r2` minus that truncated main term; and the odd `N` carry no main term at all.  The odd part and
the singular series vanishing are the proved leaves `meanSquare38_odd_singular` and
`meanSquare38_odd_energy` of `SPLIT_meanSquare38`.  The inequality `Θ ≥ 1/2` is the existing
leaf `zeroBound_lower150` above.  AI wrote the Lean code. Goldbach is open. -/

/-- The truncated main term of P0029 page 12: `N Σ_{q ≤ Q} μ(q)² c_q(N) / φ(q)²` with the
Farey level `Q = ⌊N ^ (1/2)⌋`, page 11 "on the Farey arcs one has q ≤ Q ≍ N ^ (1/2)".
Here `c_q(-N) = c_q(N)` is real, so the real part of `ramanujan` is used as in `singular`. -/
noncomputable def truncMain150 (N : ℕ) : ℝ :=
  (N : ℝ) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt N),
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
      (ramanujan q (N : ℤ)).re

/-- LEAF, new. P0029 Section 3, page 12, the unnumbered display after 3.7:
`N Σ_{q ≤ Q} μ(q)² c_q(-N) / φ(q)² = N 𝔖(N) + O(N ^ (1/2 + ε))`, the completion of the
truncated singular series at the Farey level `Q ≍ N ^ (1/2)`.  PROVED, PROVE PASS 20261112,
from `singular_tail150` in `SingularTail150.lean`: `|c_q(N)| ≤ Σ_{e ∣ (q,N)} e`, a Rankin
weight on `q > Q`, `φ(em) ≥ φ(e)φ(m)` and the divisor bound.  AI wrote the Lean code. -/
theorem singular_truncation150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |truncMain150 N - (N : ℝ) * singular N| ≤ C * (N : ℝ) ^ (1 / 2 + ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := singular_tail150 ε hε
  exact ⟨C, fun N hN => by simpa only [truncMain150] using hC N hN⟩

/-! ### Split of `major_minor_mean_square150`, ROUTE BURST 7

The circle method core of P0029 pages 10 to 13.  With `S = Ssum X` of page 14 and the major arc
model `V = VX150 X` of `MeanSquareCore150.lean`, which is display 3.5 with only its main term
`μ(q)/φ(q) Σ_{n ≤ X} e(n(α - a/q))` kept on the Dirichlet arcs of level `Q = ⌊X^{1/2}⌋`:

* `major_arc_uniform150`, CITED, display 3.5 with 3.6 and 3.7: `|S - V| ≪ X^{Θ + 1/4 + ε}`.
  The two open leaves of this split, `major_arc_uniform150` and `arc_tails_sup150`, live in
  `MeanSquareLeaves150.lean`, imported below, because an existing file may never gain a new
  open leaf; every proof here uses them by name as before.
* `major_model_L2_150`, elementary, PROVED: `∫_0^1 |V|² ≪ X^{1 + ε}`.
* `major_coefficients150`, page 12, the arc main term: the `N`-th Fourier coefficient of `V²`
  is the truncated main term `truncMain150 N` up to an error of mean square `≪ X^{2 + ε}`.
  Derived from the PROVED exact coefficient `coeff_WX150` of the full model `W`, Bessel
  `bessel_VW150`, the PROVED level change `truncation_level150`, and the elementary leaf
  `arc_tails150`.
* PROVED in `MeanSquareCore150.lean`: display 3.2, Parseval for `S`, Bessel on `[0, 1]` and the
  abstract assembly `bessel_model150`; the assembly below adds the exponents.

AI wrote the Lean code. Goldbach is open. -/

/-- LEAF, elementary. P0029 page 12, the size of the main term: `∫_0^1 |V(α)|² dα ≪ X^{1+ε}`,
since the arcs of denominator `q` cover the `φ(q)` points `a/q` with `|α - a/q| ≤ 1/(qQ)`,
`∫ |T|² = X` on each, and `Σ_{q ≤ Q} (q + 1) / φ(q)² ≪ Q^ε`.  PROVED, ROUTE BURST 7, as
`integral_norm_sq_VX_le150` in ModelL2_150.lean. -/
theorem major_model_L2_150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∫ α in (0 : ℝ)..1, ‖VX150 X α‖ ^ 2 ≤ C * (X : ℝ) ^ (1 + ε) :=
  integral_norm_sq_VX_le150

/-- PROVED. `‖a - c‖² ≤ 2‖a - b‖² + 2‖b - c‖²` in `ℂ`. -/
theorem norm_sub_sq_le_two150 (a b c : ℂ) :
    ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a b c
  have h0 : 0 ≤ ‖a - c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a - b‖ - ‖b - c‖), norm_nonneg (a - b), norm_nonneg (b - c)]

/-- Page 12, the arc tails in mean square: `∫_0^1 |V² - W|² ≪ X^{2+ε}`.  ROUTE BURST 7: derived
from the leaf `arc_tails_sup150` and the PROVED `integral_norm_VW_le150` and
`integral_sq_VW_le_sup150` of ArcTails150.lean, `∫|g|² ≤ sup|g| ∫|g|`. -/
theorem arc_tails150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ ^ 2 ≤ C * (X : ℝ) ^ (2 + ε) := by
  intro ε hε
  obtain ⟨C1, h1⟩ := arc_tails_sup150 (ε / 2) (by linarith)
  obtain ⟨C2, h2⟩ := integral_norm_VW_le150 (ε / 2) (by linarith)
  refine ⟨|C1| * |C2|, fun X hX => ?_⟩
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set P : ℝ := (X : ℝ) ^ (1 + ε / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  have hB : ∀ α ∈ Set.Icc (0 : ℝ) 1, ‖VX150 X α ^ 2 - WX150 X α‖ ≤ |C1| * P :=
    fun α hα => (h1 X hX α hα).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
  have hI : (∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖) ≤ |C2| * P :=
    (h2 X hX).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
  have hPP : P * P = (X : ℝ) ^ (2 + ε) := by
    rw [hP, ← Real.rpow_add (by linarith : (0 : ℝ) < X)]; congr 1; ring
  calc _ ≤ |C1| * P * ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ :=
        integral_sq_VW_le_sup150 X _ hB
    _ ≤ |C1| * P * (|C2| * P) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = |C1| * |C2| * (P * P) := by ring
    _ = |C1| * |C2| * (X : ℝ) ^ (2 + ε) := by rw [hPP]

/-- PROVED. `Σ_{q ≤ ⌊X^{1/2}⌋} μ(q)² |c_q(N)| / φ(q)² ≪ X^ε`, from `|c_q(N)| ≤ φ(q)` and
`Σ_{q ≤ Q} (q + 1)/φ(q)² ≪ Q^{4/k}` of ModelL2_150.lean. -/
theorem sum_abs_singular_terms150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X → ∀ N : ℕ,
      ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
        |((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          (ramanujan q (N : ℤ)).re| ≤ C * (X : ℝ) ^ ε := by
  intro ε hε
  set k : ℕ := ⌈2 / ε⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 / ε : ℝ) < k := by
    have := Nat.le_ceil (2 / ε)
    rw [hk]; push_cast; linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : 2 * (k : ℝ)⁻¹ ≤ ε := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hkpos]
    have := (div_lt_iff₀ hε).mp hkR
    linarith
  obtain ⟨C, hC0, hC⟩ := sum_totient_weight_le150 k hk1
  refine ⟨C, hC0, fun X hX N => ?_⟩
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hQ1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa using hX)
  have hQ2 : ((Nat.sqrt X : ℝ)) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have hQpow : (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) ≤ (X : ℝ) ^ ε := by
    have hQR : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast hQ1
    have e : (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) = ((Nat.sqrt X : ℝ) ^ 2) ^ (2 * (k : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
    rw [e]
    calc ((Nat.sqrt X : ℝ) ^ 2) ^ (2 * (k : ℝ)⁻¹) ≤ (X : ℝ) ^ (2 * (k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hQ2 (by positivity)
      _ ≤ (X : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hXR hs
  have hpt : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X),
      |((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          (ramanujan q (N : ℤ)).re| ≤ ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 := by
    intro q hq
    have hq1 := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
      have hm : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := q)
        exact_mod_cast h
      exact (sq_le_one_iff_abs_le_one _).mpr hm
    have hre : |(ramanujan q (N : ℤ)).re| ≤ (Nat.totient q : ℝ) :=
      (Complex.abs_re_le_norm _).trans (norm_ramanujan_le150 q N)
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          |(ramanujan q (N : ℤ)).re|
        ≤ 1 / (Nat.totient q : ℝ) ^ 2 * (Nat.totient q : ℝ) :=
          mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hre (abs_nonneg _)
            (by positivity)
      _ ≤ ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 := by
          rw [one_div_mul_eq_div]
          apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  calc _ ≤ ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 :=
        Finset.sum_le_sum hpt
    _ ≤ C * (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) := hC _ hQ1
    _ ≤ C * (X : ℝ) ^ ε := mul_le_mul_of_nonneg_left hQpow hC0

/-- Page 12, the display after 3.7 at the level of `X`: the coefficient
`(N - 1) Σ_{q ≤ ⌊X^{1/2}⌋} μ(q)²/φ(q)² c_q(-N)` of the full model, `coeff_WX150`, against
`truncMain150 N = N Σ_{q ≤ ⌊N^{1/2}⌋} μ(q)²/φ(q)² c_q(N)`, in mean square over the even `N ≤ X`.
Pointwise the difference is `-Σ_{q ≤ Q} μ²c_q/φ²`, which is `≪ X^ε`,
`sum_abs_singular_terms150`, plus `N Σ_{N^{1/2} < q ≤ X^{1/2}} μ²c_q/φ²`, which is
`≪ N^{1/2+ε}` by the absolute tail bound `singular_tail_abs150`; and `c_q(-N) = c_q(N)` is real,
`ramanujan_neg_eq_re150`.  PROVED, ROUTE BURST 7. -/
theorem truncation_level150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
        ‖((N : ℂ) - 1) * (∑ q ∈ Finset.Icc 1 (Nat.sqrt X), wq150 q * ramanujan q (-(N : ℤ))) -
          (truncMain150 N : ℂ)‖ ^ 2 ≤ C * (X : ℝ) ^ (2 + ε) := by
  intro ε hε
  obtain ⟨C1, hC10, hC1⟩ := sum_abs_singular_terms150 (ε / 2) (by linarith)
  obtain ⟨C2, hC2⟩ := singular_tail_abs150 (ε / 2) (by linarith)
  refine ⟨(C1 + |C2|) ^ 2, fun X hX => ?_⟩
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := by linarith
  set F := (Finset.Icc 1 X).filter (fun N => Even N) with hFdef
  set P : ℝ := (X : ℝ) ^ (1 / 2 + ε / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  have hpt : ∀ N ∈ F,
      ‖((N : ℂ) - 1) * (∑ q ∈ Finset.Icc 1 (Nat.sqrt X), wq150 q * ramanujan q (-(N : ℤ))) -
          (truncMain150 N : ℂ)‖ ^ 2 ≤ ((C1 + |C2|) * P) ^ 2 := by
    intro N hN
    obtain ⟨hN1, hNX⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNXR : (N : ℝ) ≤ X := by exact_mod_cast hNX
    set f : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re with hf
    have hterm : ∀ q, wq150 q * ramanujan q (-(N : ℤ)) = ((f q : ℝ) : ℂ) := by
      intro q
      rw [ramanujan_neg_eq_re150, hf]
      unfold wq150
      push_cast
      ring
    set QX := Nat.sqrt X
    set QN := Nat.sqrt N
    have hQ : QN ≤ QX := Nat.sqrt_le_sqrt hNX
    have hsplit : ∑ q ∈ Finset.Icc 1 QX, f q =
        ∑ q ∈ Finset.Icc 1 QN, f q + ∑ q ∈ Finset.Ioc QN QX, f q := by
      have hu : Finset.Icc 1 QX = Finset.Icc 1 QN ∪ Finset.Ioc QN QX := by
        ext q; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
      rw [hu, Finset.sum_union]
      rw [Finset.disjoint_left]
      intro q h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
      omega
    have htrunc : truncMain150 N = (N : ℝ) * ∑ q ∈ Finset.Icc 1 QN, f q := rfl
    have hval : ((N : ℂ) - 1) * (∑ q ∈ Finset.Icc 1 QX, wq150 q * ramanujan q (-(N : ℤ))) -
        (truncMain150 N : ℂ) =
        (((-(∑ q ∈ Finset.Icc 1 QX, f q) + (N : ℝ) * ∑ q ∈ Finset.Ioc QN QX, f q : ℝ)) : ℂ) := by
      simp_rw [hterm]
      rw [← Complex.ofReal_sum, hsplit, htrunc]
      push_cast
      ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    -- the two bounds
    have hA : |∑ q ∈ Finset.Icc 1 QX, f q| ≤ C1 * (X : ℝ) ^ (ε / 2) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (hC1 X hX N)
    have hT : (N : ℝ) * |∑ q ∈ Finset.Ioc QN QX, f q| ≤ C2 * (N : ℝ) ^ (1 / 2 + ε / 2) := by
      refine le_trans ?_ (hC2 N hN1 (QX + 1))
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hsub : Finset.Ioc QN QX ⊆ Finset.range (QX + 1) := by
        intro q hq; simp only [Finset.mem_Ioc, Finset.mem_range] at hq ⊢; omega
      calc ∑ q ∈ Finset.Ioc QN QX, |f q|
          = ∑ q ∈ Finset.Ioc QN QX, |(if q ≤ QN then 0 else f q)| := by
            refine Finset.sum_congr rfl (fun q hq => ?_)
            have : ¬ q ≤ QN := by simp only [Finset.mem_Ioc] at hq; omega
            rw [if_neg this]
        _ ≤ ∑ q ∈ Finset.range (QX + 1), |(if q ≤ QN then 0 else f q)| :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    have hXe1 : (X : ℝ) ^ (ε / 2) ≤ P :=
      Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
    have hNe : (N : ℝ) ^ (1 / 2 + ε / 2) ≤ P :=
      Real.rpow_le_rpow (by linarith) hNXR (by linarith)
    have habs : |-(∑ q ∈ Finset.Icc 1 QX, f q) + (N : ℝ) * ∑ q ∈ Finset.Ioc QN QX, f q| ≤
        (C1 + |C2|) * P := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ N)]
      have h1 : C1 * (X : ℝ) ^ (ε / 2) ≤ C1 * P := mul_le_mul_of_nonneg_left hXe1 hC10
      have h2 : C2 * (N : ℝ) ^ (1 / 2 + ε / 2) ≤ |C2| * P :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hNe (abs_nonneg _))
      linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : ((F.card : ℕ) : ℝ) ≤ X := by
    have : F.card ≤ X := by
      calc F.card ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
        _ = X := by simp
    exact_mod_cast this
  have hP2 : P ^ 2 = (X : ℝ) ^ (1 + ε) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hX0]; congr 1; push_cast; ring
  have hXe : (X : ℝ) * (X : ℝ) ^ (1 + ε) = (X : ℝ) ^ (2 + ε) := by
    rw [show (2 : ℝ) + ε = 1 + (1 + ε) by ring,
      Real.rpow_add (by linarith : (0 : ℝ) < X) 1 (1 + ε), Real.rpow_one]
  calc _ ≤ ((F.card : ℕ) : ℝ) * ((C1 + |C2|) * P) ^ 2 := hsum
    _ ≤ (X : ℝ) * ((C1 + |C2|) * P) ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (C1 + |C2|) ^ 2 * ((X : ℝ) * P ^ 2) := by ring
    _ = (C1 + |C2|) ^ 2 * (X : ℝ) ^ (2 + ε) := by rw [hP2, hXe]

/-- Page 12. "If in 3.5 we keep only the main term and substitute it into 3.2, then the
contribution of the arc around `a/q` can be shown to be `μ(q)²/φ(q)² N e(-aN/q) + O(N^{1/2+ε})`.
Summing first over reduced residues produces Ramanujan sums": the `N`-th Fourier coefficient of
`V²` is `truncMain150 N` up to an error whose mean square over the even `N ≤ X` is `≪ X^{2+ε}`,
the square of the survey's pointwise `N^{1/2+ε}` summed over `N ≤ X`.  ROUTE BURST 7: derived
from the PROVED `coeff_WX150` and `bessel_VW150` of Coefficients150.lean and the two elementary
leaf `arc_tails150` and the PROVED `truncation_level150`. -/
theorem major_coefficients150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
        ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) - (truncMain150 N : ℂ)‖ ^ 2 ≤
          C * (X : ℝ) ^ (2 + ε) := by
  intro ε hε
  obtain ⟨Ca, ha⟩ := arc_tails150 ε hε
  obtain ⟨Cb, hb⟩ := truncation_level150 ε hε
  refine ⟨2 * Ca + 2 * Cb, fun X hX => ?_⟩
  set F := (Finset.Icc 1 X).filter (fun N => Even N) with hFdef
  have hpt : ∀ N ∈ F,
      ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) - (truncMain150 N : ℂ)‖ ^ 2 ≤
        2 * ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) -
          ∫ α in (0 : ℝ)..1, WX150 X α * ee (-((N : ℝ) * α))‖ ^ 2 +
        2 * ‖((N : ℂ) - 1) * (∑ q ∈ Finset.Icc 1 (Nat.sqrt X), wq150 q * ramanujan q (-(N : ℤ))) -
          (truncMain150 N : ℂ)‖ ^ 2 := by
    intro N hN
    have hN' := Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1
    rw [← coeff_WX150 hN'.1 hN'.2]
    exact norm_sub_sq_le_two150 _ _ _
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h1 := (bessel_VW150 X F).trans (ha X hX)
  have h2 := hb X hX
  calc _ ≤ _ := hsum
    _ ≤ 2 * (Ca * (X : ℝ) ^ (2 + ε)) + 2 * (Cb * (X : ℝ) ^ (2 + ε)) := by linarith
    _ = (2 * Ca + 2 * Cb) * (X : ℝ) ^ (2 + ε) := by ring

/-- PROVED. The elementary inequality used to pass from `r2 - truncMain150` and
`truncMain150 - N 𝔖(N)` to `E2`, P0029 page 13, implicit in "using Parseval together with 3.7". -/
theorem sq_sub_le_two150 (a b c : ℝ) : (a - b) ^ 2 ≤ 2 * (a - c) ^ 2 + 2 * (c - b) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * c + b)]

open ArithmeticFunction

/-! ### Development for `exceptional_gap150`: the singular series on even `N`

`singular N = Σ_q μ(q)² c_q(N)/φ(q)²`.  Below: (i) the divisor-sum formula for the
Ramanujan sum `c_q(N)`, (ii) multiplicativity of `q ↦ c_q(N)`, (iii) its value at a prime,
(iv) summability of `μ(q)²/φ(q)²` and of the series term.  All `private` to this file. -/

private lemma ee_add' (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma ee_nat_mul (k : ℕ) (x : ℝ) : ee ((k : ℝ) * x) = (ee x) ^ k := by
  induction k with
  | zero => simp [ee]
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, ee_add', ih, pow_succ]

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma ee_one : ee (1 : ℝ) = 1 := by unfold ee; norm_num

private lemma ee_int_mul (k : ℤ) (x : ℝ) : ee ((k : ℝ) * x) = (ee x) ^ k := by
  unfold ee
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma ee_int_cast (k : ℤ) : ee ((k : ℝ)) = 1 := by
  have h := ee_int_mul k 1
  rw [mul_one] at h
  rw [h, ee_one, one_zpow]

private lemma ee_eq_one_iff {x : ℝ} : ee x = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    have h' : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = 1 := h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero hx)
  · rintro ⟨k, rfl⟩
    exact ee_int_cast k

/-- The orthogonality relation `Σ_{b<m} e(bN/m) = m` if `m ∣ N`, else `0`. -/
private lemma sum_ee_orth {m : ℕ} (hm : 0 < m) (N : ℤ) :
    ∑ b ∈ Finset.range m, ee (((b : ℝ) * (N : ℝ)) / m) =
      if (m : ℤ) ∣ N then (m : ℝ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := ee ((N : ℝ) / m) with hc
  have hterm : ∀ b ∈ Finset.range m, ee (((b : ℝ) * (N : ℝ)) / m) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (N : ℝ)) / m = (b : ℝ) * ((N : ℝ) / m) := by field_simp
    rw [harg, ee_nat_mul]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = ee ((m : ℝ) * ((N : ℝ) / m)) := by
      rw [hc]; exact (ee_nat_mul m ((N : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (N : ℝ) hmR, ee_int_cast]
  have hiff : c = 1 ↔ (m : ℤ) ∣ N := by
    rw [hc, ee_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      have h2 : (N : ℝ) = (k : ℝ) * (m : ℝ) := by
        rw [div_eq_iff hmR] at hk
        linarith [hk]
      have h3 : N = k * (m : ℤ) := by exact_mod_cast h2
      exact ⟨k, by rw [h3]; ring⟩
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      push_cast
      field_simp
  by_cases h1 : c = 1
  · rw [if_pos (hiff.mp h1)]
    simp [h1]
  · rw [if_neg (fun h => h1 (hiff.mpr h))]
    rw [geom_sum_eq h1 m, hcm]
    simp

private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := moebius) (x := n)
  rw [moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma divisors_filter_dvd_eq_gcd {q a : ℕ} (hq : q ≠ 0) :
    q.divisors.filter (fun d => d ∣ a) = (a.gcd q).divisors := by
  have hg : a.gcd q ∣ q := Nat.gcd_dvd_right a q
  have hg0 : a.gcd q ≠ 0 := by
    rcases Nat.eq_zero_or_pos (a.gcd q) with h | h
    · rw [h] at hg; exact absurd (Nat.eq_zero_of_zero_dvd hg) hq
    · exact h.ne'
  rw [← Nat.divisors_filter_dvd_of_dvd hq hg]
  refine Finset.filter_congr (fun d hd => ?_)
  simp only [Nat.mem_divisors] at hd
  exact ⟨fun h => Nat.dvd_gcd h hd.1, fun h => Nat.dvd_trans h (Nat.gcd_dvd_left a q)⟩

private lemma indicator_coprime {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, divisors_filter_dvd_eq_gcd hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors (a.gcd q))
  push_cast at h
  exact h.symm

private lemma sum_range_filter_dvd {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
    ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), g a
      = ∑ b ∈ Finset.range (q / d), g (d * b) := by
  have hdq' : d * (q / d) = q := Nat.mul_div_cancel' hdq
  have hset : (Finset.range q).filter (fun a => d ∣ a)
      = (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨haq, b, rfl⟩
      refine ⟨b, ?_, rfl⟩
      rw [← hdq'] at haq
      exact Nat.lt_of_mul_lt_mul_left haq
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, ⟨b, rfl⟩⟩
      rw [← hdq']
      exact Nat.mul_lt_mul_of_pos_left hb hd
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hd hxy

/-- The Ramanujan sum as a divisor sum: `c_q(N) = Σ_{d ∣ q, (q/d) ∣ N} μ(d)·(q/d)`. -/
private lemma ramanujan_eq_complex (q : ℕ) (N : ℤ) :
    ramanujan q N = ∑ d ∈ q.divisors,
      (moebius d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ N then ((q / d : ℕ) : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [ramanujan]
  have hq0 : q ≠ 0 := hq.ne'
  have hfilter : (Finset.range q).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => a.gcd q = 1) :=
    Finset.filter_congr (fun a _ => Nat.coprime_iff_gcd_eq_one)
  rw [ramanujan, hfilter, Finset.sum_filter]
  have hstep1 : ∑ a ∈ Finset.range q, (if a.gcd q = 1 then ee (((a : ℝ) * (N : ℝ)) / q) else 0)
      = ∑ a ∈ Finset.range q,
          (∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0))
            * ee (((a : ℝ) * (N : ℝ)) / q) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (if a.gcd q = 1 then (1:ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q)
        = (if a.gcd q = 1 then ee (((a : ℝ) * (N : ℝ)) / q) else 0) := by
      by_cases h : a.gcd q = 1 <;> simp [h]
    rw [← h1, indicator_coprime hq0 a]
  rw [hstep1]
  have hstep2 : ∀ a ∈ Finset.range q,
      (∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0))
        * ee (((a : ℝ) * (N : ℝ)) / q)
      = ∑ d ∈ q.divisors,
          (if d ∣ a then (moebius d : ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q) := by
    intro a _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq
  have hm0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hd0
  have hfac : ∑ a ∈ Finset.range q,
        (if d ∣ a then (moebius d : ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q)
      = ∑ a ∈ Finset.range q,
          (if d ∣ a then (moebius d : ℂ) * ee (((a : ℝ) * (N : ℝ)) / q) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : d ∣ a <;> simp [h]
  rw [hfac, ← Finset.sum_filter, sum_range_filter_dvd hd0 hdvd, ← Finset.mul_sum]
  congr 1
  have hqd : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  have hqd0 : ((q / d : ℕ) : ℝ) ≠ 0 := by positivity
  have harg : ∀ b : ℕ, ee (((d * b : ℕ) : ℝ) * (N : ℝ) / q)
      = ee (((b : ℝ) * (N : ℝ)) / (((q / d : ℕ)) : ℝ)) := by
    intro b
    congr 1
    rw [Nat.cast_div hdvd (by positivity : ((d : ℕ) : ℝ) ≠ 0), ← hqd]
    push_cast
    have hdR : ((d : ℕ) : ℝ) ≠ 0 := by positivity
    have hmR : ((q / d : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl (fun b _ => harg b), sum_ee_orth hm0 N]
  have hcd : ((q : ℤ) / (d : ℤ)) = (((q / d : ℕ)) : ℤ) := (Int.natCast_div q d).symm
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ N
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

/-- The Ramanujan sum, with the real divisor sum written out. -/
private lemma ramanujan_eq_real (N q : ℕ) :
    ramanujan q (N : ℤ) = ∑ d ∈ q.divisors,
      ((((moebius d : ℤ)) : ℝ) : ℂ) *
        ((if (q / d : ℕ) ∣ N then ((((q / d : ℕ)) : ℝ) : ℂ) else 0)) := by
  rw [ramanujan_eq_complex]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hiff : ((((q / d : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ)) ↔ (q / d : ℕ) ∣ N := Int.natCast_dvd_natCast
  have hmc : (moebius d : ℂ) = ((((moebius d : ℤ)) : ℝ) : ℂ) := by push_cast; ring
  have hif : (if ((((q / d : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ)) then (((q / d : ℕ)) : ℂ) else 0)
      = ((if (q / d : ℕ) ∣ N then ((((q / d : ℕ)) : ℝ) : ℂ) else 0)) := by
    by_cases hd : (q / d : ℕ) ∣ N
    · rw [if_pos (hiff.mpr hd), if_pos hd]
      norm_num
    · rw [if_neg (fun hh => hd (hiff.mp hh)), if_neg hd]
  rw [hmc, hif]

private lemma cN_eq (N q : ℕ) :
    (ramanujan q (N : ℤ)).re = ∑ d ∈ q.divisors,
      ((moebius d : ℤ) : ℝ) * (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
  rw [ramanujan_eq_real, Complex.re_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : (q / d : ℕ) ∣ N
  · rw [if_pos hd, if_pos hd, ← Complex.ofReal_mul, Complex.ofReal_re]
  · rw [if_neg hd, if_neg hd]
    simp

private lemma cN_one (N : ℕ) : (ramanujan 1 (N : ℤ)).re = 1 := by
  have h := cN_eq N 1
  rw [h]
  simp [Nat.divisors_one]

private lemma cN_zero (N : ℕ) : (ramanujan 0 (N : ℤ)).re = 0 := by
  simp [ramanujan]

private lemma mul_div_mul_div {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (m * n) / (a * b) = (m / a) * (n / b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have ha' : 0 < a := Nat.pos_of_ne_zero ha0
  have hb' : 0 < b := Nat.pos_of_ne_zero hb0
  have hab : 0 < a * b := Nat.mul_pos ha' hb'
  have h1 : a * x * (b * y) = (a * b) * (x * y) := by ring
  rw [h1, Nat.mul_div_right (x * y) hab, Nat.mul_div_right x ha', Nat.mul_div_right y hb']

private lemma cN_summand_mul {N m n a b : ℕ} (hmn : m.Coprime n) (ha : a ∈ m.divisors)
    (hb : b ∈ n.divisors) :
    ((moebius (a * b) : ℤ) : ℝ) *
        (if ((m * n) / (a * b) : ℕ) ∣ N then (((m * n) / (a * b) : ℕ) : ℝ) else 0)
      = (((moebius a : ℤ) : ℝ) * (if (m / a : ℕ) ∣ N then ((m / a : ℕ) : ℝ) else 0))
        * (((moebius b : ℤ) : ℝ) * (if (n / b : ℕ) ∣ N then ((n / b : ℕ) : ℝ) else 0)) := by
  have ha_m : a ∣ m := (Nat.mem_divisors.mp ha).1
  have hb_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hcop : a.Coprime b := (hmn.coprime_dvd_left ha_m).coprime_dvd_right hb_n
  have hmu : ((moebius (a * b) : ℤ) : ℝ) = ((moebius a : ℤ) : ℝ) * ((moebius b : ℤ) : ℝ) := by
    rw [IsMultiplicative.map_mul_of_coprime isMultiplicative_moebius hcop]
    push_cast; ring
  have hdiv : ((m * n) / (a * b) : ℕ) = (m / a) * (n / b) := mul_div_mul_div ha_m hb_n ha0 hb0
  have hcop' : (m / a).Coprime (n / b) :=
    (hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha_m)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hb_n)
  rw [hmu, hdiv]
  have hml : (n / b) ∣ (m / a) * (n / b) := dvd_mul_left _ _
  have hmr : (m / a) ∣ (m / a) * (n / b) := dvd_mul_right _ _
  by_cases hP : (m / a) ∣ N
  · by_cases hQ : (n / b) ∣ N
    · rw [if_pos (hcop'.mul_dvd_of_dvd_of_dvd hP hQ), if_pos hP, if_pos hQ]
      push_cast; ring
    · rw [if_neg (fun hh => hQ (dvd_trans hml hh)), if_pos hP, if_neg hQ]; ring
  · by_cases hQ : (n / b) ∣ N
    · rw [if_neg (fun hh => hP (dvd_trans hmr hh)), if_neg hP, if_pos hQ]; ring
    · rw [if_neg (fun hh => hP (dvd_trans hmr hh)), if_neg hP, if_neg hQ]; ring

private lemma cN_mul (N : ℕ) {m n : ℕ} (h : m.Coprime n) : (ramanujan (m * n) (N : ℤ)).re = (ramanujan m (N : ℤ)).re * (ramanujan n (N : ℤ)).re := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    rw [Nat.coprime_zero_left] at h
    subst h
    rw [mul_one, cN_zero, cN_one]
    ring
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    rw [Nat.coprime_zero_right] at h
    subst h
    rw [one_mul, cN_zero, cN_one]
    ring
  have hm0' : m ≠ 0 := hm0.ne'
  have hn0' : n ≠ 0 := hn0.ne'
  rw [cN_eq, cN_eq, cN_eq, Nat.divisors_mul, Finset.mul_def]
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun b hb => ?_)
    exact cN_summand_mul h ha hb
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' hEq
    simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
    obtain ⟨ham, hbn⟩ := hp
    obtain ⟨ha'm, hb'n⟩ := hp'
    change a * b = a' * b' at hEq
    have ha_m : a ∣ m := (Nat.mem_divisors.mp ham).1
    have hb_n : b ∣ n := (Nat.mem_divisors.mp hbn).1
    have ha'_m : a' ∣ m := (Nat.mem_divisors.mp ha'm).1
    have hb'_n : b' ∣ n := (Nat.mem_divisors.mp hb'n).1
    have ha0 : a ≠ 0 := by rintro rfl; simp at ham
    have hcop_ab' : a.Coprime b' := (h.coprime_dvd_left ha_m).coprime_dvd_right hb'_n
    have hcop_a'b : a'.Coprime b := (h.coprime_dvd_left ha'_m).coprime_dvd_right hb_n
    have h1 : a ∣ a' := by
      have : a ∣ a' * b' := by rw [← hEq]; exact dvd_mul_right a b
      exact hcop_ab'.dvd_of_dvd_mul_right this
    have h2 : a' ∣ a := by
      have : a' ∣ a * b := by rw [hEq]; exact dvd_mul_right a' b'
      exact hcop_a'b.dvd_of_dvd_mul_right this
    have haa : a = a' := Nat.dvd_antisymm h1 h2
    subst haa
    have : b = b' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) hEq
    exact Prod.ext rfl this

private lemma divisors_prime (p : ℕ) (hp : p.Prime) : p.divisors = {1, p} := by
  ext d
  rw [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, -⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd hp d hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨one_dvd p, hp.ne_zero⟩
    · exact ⟨dvd_rfl, hp.ne_zero⟩

/-- The Ramanujan sum at a prime: `c_p(N) = p - 1` if `p ∣ N` and `-1` otherwise. -/
private lemma cN_prime (N p : ℕ) (hp : p.Prime) :
    (ramanujan p (N : ℤ)).re = if p ∣ N then ((p : ℝ) - 1) else (-1) := by
  rw [cN_eq, divisors_prime p hp]
  have hp1 : p ≠ 1 := hp.ne_one
  have hmu1 : ((moebius 1 : ℤ) : ℝ) = 1 := by simp
  have hmup : ((moebius p : ℤ) : ℝ) = -1 := by
    rw [moebius_apply_prime hp]; norm_num
  rw [Finset.sum_insert (by simp [Ne.symm hp1] : (1 : ℕ) ∉ ({p} : Finset ℕ)),
    Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos, hmu1, hmup]
  by_cases h : p ∣ N <;> simp [h] <;> ring

private lemma totient_eq_prod_of_squarefree {q : ℕ} (hq : Squarefree q) :
    q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
  have h := Nat.totient_eq_div_primeFactors_mul q
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [Nat.prod_primeFactors_of_squarefree hq, Nat.div_self (Nat.pos_of_ne_zero hq0),
    one_mul] at h
  exact h

private lemma prime_pow_five_le {p : ℕ} (hp : p.Prime) (h3 : p ≠ 2) :
    (p : ℝ) ^ 5 ≤ ((p : ℝ) - 1) ^ 8 := by
  have hp2 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (2 / 3 : ℝ) * (p : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have h2 : ((2 / 3 : ℝ) * (p : ℝ)) ^ 8 ≤ ((p : ℝ) - 1) ^ 8 := by
    exact pow_le_pow_left₀ (by linarith) h1 8
  have h3 : (1 : ℝ) ≤ (2 / 3 : ℝ) ^ 8 * (p : ℝ) ^ 3 := by
    have hbase : (1 : ℝ) ≤ (2 / 3 : ℝ) ^ 8 * (3 : ℝ) ^ 3 := by norm_num
    have hmono : (3 : ℝ) ^ 3 ≤ (p : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num) hpR 3
    have := mul_le_mul_of_nonneg_left hmono (by norm_num : (0:ℝ) ≤ (2/3:ℝ)^8)
    linarith
  have h4 : (p : ℝ) ^ 5 ≤ ((2 / 3 : ℝ) * (p : ℝ)) ^ 8 := by
    have h8 : ((2 / 3 : ℝ) * (p : ℝ)) ^ 8 = (2 / 3 : ℝ) ^ 8 * (p : ℝ) ^ 8 := by ring
    rw [h8]
    have hp5 : (0 : ℝ) < (p : ℝ) ^ 5 := by positivity
    nlinarith [h3, hp5]
  linarith [h2, h4]

private lemma prod_le_one_of_le_one {s : Finset ℕ} {f : ℕ → ℝ}
    (h0 : ∀ p ∈ s, 0 ≤ f p) (h1 : ∀ p ∈ s, f p ≤ 1) : ∏ p ∈ s, f p ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hA : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have hA0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hB : ∏ x ∈ s, f x ≤ 1 :=
      ih (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
        (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
    have hB0 : 0 ≤ ∏ x ∈ s, f x :=
      Finset.prod_nonneg (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
    nlinarith

private lemma prod_ratio_le {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    ∏ p ∈ s, ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8) ≤ 32 := by
  have hpos : ∀ p ∈ s, (0 : ℝ) < ((p : ℝ) - 1) ^ 8 := by
    intro p hp
    have hp2 : 2 ≤ p := (hs p hp).two_le
    have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
      linarith
    positivity
  have hnum : ∀ p ∈ s, (0 : ℝ) < (p : ℝ) ^ 5 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (hs p hp).two_le
      exact_mod_cast this
    exact pow_pos (by linarith) 5
  have hle1 : ∀ p ∈ s, p ≠ 2 → ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8) ≤ 1 := by
    intro p hp hpne
    have hp' := hs p hp
    have := prime_pow_five_le hp' hpne
    rw [div_le_one (hpos p hp)]
    exact this
  by_cases h2 : 2 ∈ s
  · rw [← Finset.mul_prod_erase s (fun p => ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8)) h2]
    have h2val : ((2 : ℝ) ^ 5 / ((2 : ℝ) - 1) ^ 8) = 32 := by norm_num
    have hrest : ∏ x ∈ s.erase 2, ((x : ℝ) ^ 5 / ((x : ℝ) - 1) ^ 8) ≤ 1 := by
      refine prod_le_one_of_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hp' : p ∈ s := Finset.mem_of_mem_erase hp
        exact le_of_lt (div_pos (hnum p hp') (hpos p hp'))
      · have hp' : p ∈ s := Finset.mem_of_mem_erase hp
        exact hle1 p hp' (Finset.ne_of_mem_erase hp)
    have hrest0 : (0:ℝ) ≤ ∏ x ∈ s.erase 2, ((x : ℝ) ^ 5 / ((x : ℝ) - 1) ^ 8) :=
      Finset.prod_nonneg (fun p hp => le_of_lt (div_pos
        (hnum p (Finset.mem_of_mem_erase hp)) (hpos p (Finset.mem_of_mem_erase hp))))
    have h2val : ((↑(2:ℕ) : ℝ) ^ 5 / ((↑(2:ℕ) : ℝ) - 1) ^ 8) ≤ 32 := by norm_num
    nlinarith [h2val, hrest, hrest0]
  · have : ∏ p ∈ s, ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8) ≤ 1 := by
      refine prod_le_one_of_le_one (fun p hp => ?_) (fun p hp => ?_)
      · exact le_of_lt (div_pos (hnum p hp) (hpos p hp))
      · exact hle1 p hp (by rintro rfl; exact h2 hp)
    linarith

private lemma totient_pow_le {q : ℕ} (hq : Squarefree q) :
    (q : ℝ) ^ 5 ≤ 32 * (q.totient : ℝ) ^ 8 := by
  have hprod := Nat.prod_primeFactors_of_squarefree hq
  have htot := totient_eq_prod_of_squarefree hq
  have hqeq : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← hprod]
    push_cast
    simp
  have hteq : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [htot]
    push_cast
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [hqeq, hteq]
  have h5 : (∏ p ∈ q.primeFactors, (p : ℝ)) ^ 5 = ∏ p ∈ q.primeFactors, (p : ℝ) ^ 5 :=
    (Finset.prod_pow q.primeFactors 5 (fun p => (p : ℝ))).symm
  have h8 : (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) ^ 8
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ^ 8 :=
    (Finset.prod_pow q.primeFactors 8 (fun p => ((p : ℝ) - 1))).symm
  rw [h5, h8]
  have hratio := prod_ratio_le (s := q.primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [Finset.prod_div_distrib] at hratio
  have hbpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ^ 8 := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    have : (0:ℝ) < (p:ℝ) - 1 := by linarith
    positivity
  rw [div_le_iff₀ hbpos] at hratio
  linarith [hratio]

private lemma rpow_totient_le {q : ℕ} (hq : Squarefree q) :
    (q : ℝ) ^ (5 / 4 : ℝ) ≤ 32 ^ (1 / 4 : ℝ) * (q.totient : ℝ) ^ 2 := by
  have h := totient_pow_le hq
  have h1 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (q:ℝ)^5) h (by norm_num : (0:ℝ) ≤ 1/4)
  have e1 : ((q:ℝ)^5) ^ (1/4:ℝ) = (q:ℝ) ^ (5/4:ℝ) := by
    rw [← Real.rpow_natCast (q:ℝ) 5, ← Real.rpow_mul (by positivity)]
    norm_num
  have e2 : ((32:ℝ) * (q.totient:ℝ)^8) ^ (1/4:ℝ)
      = (32:ℝ)^(1/4:ℝ) * ((q.totient:ℝ)^8)^(1/4:ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
  have e3 : ((q.totient:ℝ)^8)^(1/4:ℝ) = (q.totient:ℝ)^2 := by
    rw [← Real.rpow_natCast (q.totient:ℝ) 8, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [e1, e2, e3] at h1
  exact h1

private lemma phiSq_nonneg (q : ℕ) : 0 ≤ ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
  positivity

private lemma phiSq_le (q : ℕ) :
    ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 ≤ 32 ^ (1/4 : ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have h1 : ((moebius 0 : ℤ) : ℝ) = 0 := by simp
    rw [h1]
    simp [Real.zero_rpow]
  by_cases hsq : Squarefree q
  · have hmu : ((moebius q : ℤ) : ℝ) ^ 2 = 1 := by
      have h := moebius_sq_eq_one_of_squarefree hsq
      have hc := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at hc
      simpa using hc
    rw [hmu]
    have hφpos : (0 : ℝ) < (q.totient : ℝ) ^ 2 := by
      have := Nat.totient_pos.mpr hq
      have : (0:ℝ) < (q.totient : ℝ) := by exact_mod_cast this
      positivity
    have hqpos : (0 : ℝ) < (q : ℝ) ^ (5/4 : ℝ) :=
      Real.rpow_pos_of_pos (by positivity : (0:ℝ) < (q:ℝ)) _
    have hkey := rpow_totient_le hsq
    have e : (32:ℝ) ^ (1/4:ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ))
        = (32:ℝ) ^ (1/4:ℝ) / (q : ℝ) ^ (5/4 : ℝ) := by ring
    rw [e, le_div_iff₀ hqpos]
    have heq : (1 / (q.totient : ℝ) ^ 2) * (q : ℝ) ^ (5/4 : ℝ)
        = (q : ℝ) ^ (5/4 : ℝ) / (q.totient : ℝ) ^ 2 := by ring
    rw [heq, div_le_iff₀ hφpos]
    linarith [hkey]
  · have hmu : ((moebius q : ℤ) : ℝ) = 0 := by
      have h := moebius_eq_zero_of_not_squarefree hsq
      rw [h]; simp
    rw [hmu]
    have hzero : ((0:ℝ)^2 / (q.totient : ℝ) ^ 2) = 0 := by simp
    rw [hzero]
    have : (0:ℝ) ≤ 32 ^ (1/4:ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ)) := by positivity
    exact this

private lemma summable_phiSq : Summable (fun q : ℕ => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by
  have hmain : Summable (fun q : ℕ => (32:ℝ) ^ (1/4:ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ))) := by
    have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ) < 5/4)
    exact Summable.mul_left _ h
  exact Summable.of_nonneg_of_le phiSq_nonneg phiSq_le hmain

private lemma cN_abs_le (N : ℕ) (hN : 1 ≤ N) (q : ℕ) :
    |(ramanujan q (N : ℤ)).re| ≤ ∑ e ∈ N.divisors, (e : ℝ) := by
  rw [cN_eq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hmu1 : ∀ d : ℕ, |((moebius d : ℤ) : ℝ)| ≤ 1 := by
    intro d
    have h := abs_moebius_le_one (n := d)
    rw [abs_le] at h ⊢
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hstep1 : ∑ d ∈ q.divisors,
      |((moebius d : ℤ) : ℝ) * (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)|
      ≤ ∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro d _
    rw [abs_mul]
    have hmu := hmu1 d
    have hnn : (0 : ℝ) ≤ (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
      split_ifs <;> positivity
    calc |((moebius d : ℤ) : ℝ)| * |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)|
        ≤ 1 * |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ = |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)| := one_mul _
      _ = (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := abs_of_nonneg hnn
  refine le_trans hstep1 ?_
  have himg : (q.divisors.filter (fun d => (q / d : ℕ) ∣ N)).image (fun d => q / d) ⊆ N.divisors := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have hdN : (q / d : ℕ) ∣ N := (Finset.mem_filter.mp hd).2
    exact Nat.mem_divisors.mpr ⟨hdN, by omega⟩
  have hinj : Set.InjOn (fun d => q / d) ↑(q.divisors.filter (fun d => (q / d : ℕ) ∣ N)) := by
    intro d hd d' hd' heq
    have hd1 : d ∈ q.divisors := Finset.mem_of_mem_filter d hd
    have hd1' : d' ∈ q.divisors := Finset.mem_of_mem_filter d' hd'
    obtain ⟨hdq, hq0⟩ := Nat.mem_divisors.mp hd1
    obtain ⟨hdq', -⟩ := Nat.mem_divisors.mp hd1'
    have h1 : q / (q / d) = d := Nat.div_div_self hdq hq0
    have h2 : q / (q / d') = d' := Nat.div_div_self hdq' hq0
    have heq' : q / d = q / d' := heq
    rw [heq'] at h1
    rw [h1] at h2
    exact h2
  calc ∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)
      = ∑ d ∈ q.divisors.filter (fun d => (q / d : ℕ) ∣ N), ((q / d : ℕ) : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ = ∑ e ∈ (q.divisors.filter (fun d => (q / d : ℕ) ∣ N)).image (fun d => q / d), (e : ℝ) :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ e ∈ N.divisors, (e : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun e _ _ => by positivity)

private lemma summable_singTerm (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re) := by
  set C : ℝ := ∑ e ∈ N.divisors, (e : ℝ) with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg (fun e _ => by positivity)
  refine Summable.of_norm_bounded (summable_phiSq.mul_left C) ?_
  intro q
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2| = ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((moebius q : ℤ) : ℝ)^2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.totient:ℝ)^2)]
  rw [h1]
  calc ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * |(ramanujan q (N : ℤ)).re| ≤ ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (cN_abs_le N hN q) (phiSq_nonneg q)
    _ = C * (((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by ring

private lemma singTerm_one (N : ℕ) :
    ((moebius 1 : ℤ) : ℝ) ^ 2 / ((1).totient : ℝ) ^ 2 * (ramanujan 1 (N : ℤ)).re = 1 := by
  simp [cN_one]

private lemma div_sq_mul_div_sq (a b c d e k : ℝ) :
    (a * d) ^ 2 / ((b * e) ^ 2) * (c * k) = (a ^ 2 / b ^ 2 * c) * (d ^ 2 / e ^ 2 * k) := by
  by_cases hb : b = 0
  · simp [hb]
  by_cases he : e = 0
  · simp [he]
  field_simp

private lemma singTerm_mul (N : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    ((moebius (m * n) : ℤ) : ℝ) ^ 2 / ((m * n).totient : ℝ) ^ 2 * (ramanujan (m * n) (N : ℤ)).re = (((moebius (m) : ℤ) : ℝ) ^ 2 / (((m).totient : ℝ) ^ 2) * (ramanujan (m) (N : ℤ)).re) * (((moebius (n) : ℤ) : ℝ) ^ 2 / (((n).totient : ℝ) ^ 2) * (ramanujan (n) (N : ℤ)).re) := by
  rw [Nat.totient_mul hmn, cN_mul N hmn,
    IsMultiplicative.map_mul_of_coprime isMultiplicative_moebius hmn]
  push_cast
  exact div_sq_mul_div_sq _ _ _ _ _ _

private lemma singTerm_isMultiplicative (N : ℕ) :
    IsMultiplicative (⟨fun q => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re, by simp⟩ : ArithmeticFunction ℝ) :=
  ⟨singTerm_one N, fun {_ _} hmn => singTerm_mul N hmn⟩

private lemma tsum_singTerm_prime (N p : ℕ) (hp : p.Prime) :
    ∑' e : ℕ, (((moebius (p ^ e) : ℤ) : ℝ) ^ 2 / (((p ^ e).totient : ℝ) ^ 2) * (ramanujan (p ^ e) (N : ℤ)).re) = 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 := by
  have hsupp : ∀ e ∉ Finset.range 2, (((moebius (p ^ e) : ℤ) : ℝ) ^ 2 / (((p ^ e).totient : ℝ) ^ 2) * (ramanujan (p ^ e) (N : ℤ)).re) = 0 := by
    intro e he
    simp only [Finset.mem_range, not_lt] at he
    have hμ : moebius (p ^ e) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega : e ≠ 0)]
      rw [if_neg (by omega : ¬ e = 1)]
    rw [hμ]
    simp
  rw [tsum_eq_sum hsupp, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : p ^ 0 = 1 := by simp
  have h1 : p ^ 1 = p := by simp
  rw [h0, h1, singTerm_one, Nat.totient_prime hp]
  have hcast : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hmu : ((moebius p : ℤ) : ℝ) ^ 2 = 1 := by
    rw [moebius_apply_prime hp]
    norm_num
  rw [hcast, hmu, one_div, div_eq_mul_inv]
  ring

private lemma summable_norm_singTerm (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ‖(((moebius (q) : ℤ) : ℝ) ^ 2 / (((q).totient : ℝ) ^ 2) * (ramanujan (q) (N : ℤ)).re)‖) := by
  set C : ℝ := ∑ e ∈ N.divisors, (e : ℝ) with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg (fun e _ => by positivity)
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (summable_phiSq.mul_left C)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2| = ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((moebius q : ℤ) : ℝ)^2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.totient:ℝ)^2)]
  rw [h1]
  calc ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * |(ramanujan q (N : ℤ)).re| ≤ ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (cN_abs_le N hN q) (phiSq_nonneg q)
    _ = C * (((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by ring

set_option maxHeartbeats 1000000 in
private lemma eulerProduct_singTerm (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
      Filter.atTop (nhds (∑' q : ℕ, (((moebius (q) : ℤ) : ℝ) ^ 2 / (((q).totient : ℝ) ^ 2) * (ramanujan (q) (N : ℤ)).re))) := by
  let F : ArithmeticFunction ℝ :=
    ⟨fun q => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re, by simp⟩
  have hFone : F 1 = 1 := by
    show ((moebius 1 : ℤ) : ℝ) ^ 2 / ((1).totient : ℝ) ^ 2 * (ramanujan 1 (N : ℤ)).re = 1
    exact singTerm_one N
  have hFmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
    intro m n hmn
    exact singTerm_mul N hmn
  have hFm : F.IsMultiplicative := ⟨hFone, fun {_ _} hmn => hFmul hmn⟩
  have hFs : Summable (fun q : ℕ => ‖F q‖) := by
    show Summable (fun q : ℕ => ‖((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re‖)
    exact summable_norm_singTerm N hN
  have h := IsMultiplicative.eulerProduct hFm hFs
  have h2 : (fun n : ℕ => ∏ p ∈ n.primesBelow, ∑' e : ℕ, F (p ^ e))
      = (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2)) := by
    funext n
    exact Finset.prod_congr rfl (fun p hp => tsum_singTerm_prime N p (Nat.mem_primesBelow.mp hp).2)
  rw [h2] at h
  exact h

private lemma prod_one_sub_inv_sq {M : ℕ} (hM : 1 ≤ M) :
    ∏ m ∈ Finset.Icc 2 M, (1 - 1 / (m : ℝ) ^ 2) = ((M : ℝ) + 1) / (2 * (M : ℝ)) := by
  induction M with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have h1 : 1 ≤ k := hk
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ k + 1), ih h1]
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hk2 : (2 * (k : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- The odd-prime factor in the singular series: `∏_{2 ≤ m ≤ M}(1 - 1/m²) ≥ 1/2`. -/
private lemma half_le_prod_one_sub_inv_sq {M : ℕ} (hM : 1 ≤ M) :
    (1 / 2 : ℝ) ≤ ∏ m ∈ Finset.Icc 2 M, (1 - 1 / (m : ℝ) ^ 2) := by
  rw [prod_one_sub_inv_sq hM]
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [le_div_iff₀ (by positivity)]
  linarith

private lemma one_le_prod_of_one_le {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ p ∈ s, 1 ≤ f p) :
    (1 : ℝ) ≤ ∏ p ∈ s, f p := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hA : 1 ≤ f a := h a (Finset.mem_insert_self a s)
    have hB : 1 ≤ ∏ x ∈ s, f x :=
      ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    have hB0 : (0 : ℝ) ≤ ∏ x ∈ s, f x := le_trans zero_le_one hB
    nlinarith

private lemma prod_le_prod' {s : Finset ℕ} {f g : ℕ → ℝ} (h0 : ∀ p ∈ s, 0 ≤ g p)
    (h : ∀ p ∈ s, g p ≤ f p) : ∏ p ∈ s, g p ≤ ∏ p ∈ s, f p := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hA0 : 0 ≤ g a := h0 a (Finset.mem_insert_self a s)
    have hA : g a ≤ f a := h a (Finset.mem_insert_self a s)
    have hB0 : 0 ≤ ∏ x ∈ s, g x :=
      Finset.prod_nonneg (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
    have hB : ∏ x ∈ s, g x ≤ ∏ x ∈ s, f x :=
      ih (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
        (fun p hp => h p (Finset.mem_insert_of_mem hp))
    have hfB0 : 0 ≤ ∏ x ∈ s, f x := le_trans hB0 hB
    nlinarith

private lemma cN_two (N : ℕ) (hEven : Even N) : (ramanujan 2 (N : ℤ)).re = 1 := by
  rw [cN_prime N 2 Nat.prime_two, if_pos (even_iff_two_dvd.mp hEven)]
  norm_num

private lemma local_factor_ge (N p : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have h2 : 2 ≤ p := hp.two_le
    have h3 : 3 ≤ p := by omega
    exact_mod_cast h3
  have hden : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hge : -1 ≤ (ramanujan p (N : ℤ)).re := by
    rw [cN_prime N p hp]
    split_ifs with h
    · linarith
    · norm_num
  have key := div_le_div_of_nonneg_right hge hden.le
  have e : (-1 : ℝ) / ((p : ℝ) - 1) ^ 2 = -(1 / ((p : ℝ) - 1) ^ 2) := by ring
  rw [e] at key
  linarith

private lemma half_le_prod_odd {n : ℕ} :
    (1 / 2 : ℝ) ≤ ∏ p ∈ (n.primesBelow).erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · have hempty : (n.primesBelow).erase 2 = ∅ := by
      ext p
      constructor
      · intro hp
        exfalso
        obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp hp
        have hlt : p < n := (Nat.mem_primesBelow.mp hp').1
        have h2 : 2 ≤ p := (Nat.mem_primesBelow.mp hp').2.two_le
        omega
      · intro hp
        exact absurd hp (by simp)
    rw [hempty, Finset.prod_empty]
    norm_num
  · have hprime : ∀ p ∈ (n.primesBelow).erase 2, Nat.Prime p := fun p hp =>
      (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2
    have h3le : ∀ p ∈ (n.primesBelow).erase 2, 3 ≤ p := by
      intro p hp
      have h2 : 2 ≤ p := (hprime p hp).two_le
      have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
      omega
    have hinj : Set.InjOn (fun (p : ℕ) => p - 1) ↑((n.primesBelow).erase 2) := by
      intro a ha b hb h
      have ha3 : 3 ≤ a := h3le a ha
      have hb3 : 3 ≤ b := h3le b hb
      simp only at h
      omega
    have hprod : ∏ p ∈ (n.primesBelow).erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2)
        = ∏ a ∈ ((n.primesBelow).erase 2).image (fun (p : ℕ) => p - 1),
            (1 - 1 / ((a : ℝ)) ^ 2) := by
      rw [Finset.prod_image (g := fun (p : ℕ) => p - 1)
        (f := fun a : ℕ => 1 - 1 / ((a : ℝ)) ^ 2) hinj]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have hp1 : 1 ≤ p := by have := h3le p hp; omega
      rw [Nat.cast_sub hp1]
      norm_num
    rw [hprod]
    have hsub : ((n.primesBelow).erase 2).image (fun (p : ℕ) => p - 1) ⊆ Finset.Icc 2 n := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      have hlt : p < n := (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).1
      have h3 := h3le p hp
      simp only [Finset.mem_Icc]
      omega
    set U : Finset ℕ := ((n.primesBelow).erase 2).image (fun (p : ℕ) => p - 1) with hU
    have h0I : ∀ a ∈ Finset.Icc 2 n, (0 : ℝ) ≤ 1 - 1 / ((a : ℝ)) ^ 2 := by
      intro a ha
      have ha2 : (2 : ℝ) ≤ (a : ℝ) := by
        have : 2 ≤ a := (Finset.mem_Icc.mp ha).1
        exact_mod_cast this
      have h4 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith [ha2]
      have h5 : 1 / ((a : ℝ)) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h4
      rw [sub_nonneg]
      exact h5
    have h1I : ∀ a ∈ Finset.Icc 2 n, (1 - 1 / ((a : ℝ)) ^ 2) ≤ 1 := by
      intro a ha
      have h : (0 : ℝ) ≤ 1 / ((a : ℝ)) ^ 2 := by positivity
      linarith
    have hfill : ∏ a ∈ Finset.Icc 2 n \ U, (1 - 1 / ((a : ℝ)) ^ 2) ≤ 1 := by
      refine prod_le_one_of_le_one (fun a ha => ?_) (fun a ha => ?_)
      · exact h0I a (Finset.mem_sdiff.mp ha).1
      · exact h1I a (Finset.mem_sdiff.mp ha).1
    have hUprod0 : (0 : ℝ) ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) :=
      Finset.prod_nonneg (fun a ha => h0I a (hsub ha))
    have hle : ∏ a ∈ Finset.Icc 2 n, (1 - 1 / ((a : ℝ)) ^ 2)
        ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) := by
      rw [← Finset.prod_sdiff hsub]
      have h := mul_le_mul_of_nonneg_right hfill hUprod0
      linarith [h]
    calc (1 / 2 : ℝ) ≤ ∏ a ∈ Finset.Icc 2 n, (1 - 1 / ((a : ℝ)) ^ 2) :=
          half_le_prod_one_sub_inv_sq (M := n) (by omega)
      _ ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) := hle

private lemma one_le_prod_local (N n : ℕ) (hEven : Even N) :
    (1 : ℝ) ≤ ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · apply one_le_prod_of_one_le
    intro p hp
    have hp' := Nat.mem_primesBelow.mp hp
    have h2 : 2 ≤ p := hp'.2.two_le
    have h3 : p < n := hp'.1
    have hp2 : p = 2 := by omega
    rw [hp2, cN_two N hEven]
    norm_num
  · have h2mem : (2 : ℕ) ∈ n.primesBelow := by
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, Nat.prime_two⟩
    rw [← Finset.mul_prod_erase n.primesBelow (fun p => 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) h2mem]
    have h2val : (1 + (ramanujan 2 (N : ℤ)).re / ((↑(2 : ℕ) : ℝ) - 1) ^ 2) = 2 := by
      rw [cN_two N hEven]; norm_num
    rw [h2val]
    have hodd : (1 / 2 : ℝ) ≤ ∏ p ∈ (n.primesBelow).erase 2,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := by
      refine le_trans (half_le_prod_odd (n := n)) ?_
      refine prod_le_prod' (fun p hp => ?_) (fun p hp => ?_)
      · have h3 : 3 ≤ p := by
          have h2 : 2 ≤ p := (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2.two_le
          have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
          omega
        have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
        have : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
        have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        linarith
      · exact local_factor_ge N p (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2
          (Finset.ne_of_mem_erase hp)
    linarith

private lemma one_le_singular (N : ℕ) (hN : 1 ≤ N) (hEven : Even N) : 1 ≤ singular N := by
  have hlim := eulerProduct_singTerm N hN
  have hfac : ∀ n : ℕ, (1 : ℝ) ≤ ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) :=
    fun n => one_le_prod_local N n hEven
  have h1 : (1 : ℝ) ≤ ∑' q : ℕ, ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hfac)
  exact h1

/-! ### The representation error half of `exceptional_gap150`: `r2 N ≤ N/4`

`r2 N` counts weighted representations of `N` as a sum of two prime powers. If `N` is not a sum
of two primes then every contributing pair has a coordinate which is a *proper* prime power, of
which there are at most `log₂N·(√N+1)` below `N`; that gives `r2 N ≤ 8√N (log N)³ ≤ N/4` for
`N ≥ 2^64`. -/

private lemma r2_eq_sum_range (N : ℕ) :
    r2 N = ∑ k ∈ Finset.range (N + 1), vonMangoldt k * vonMangoldt (N - k) := by
  unfold r2
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => vonMangoldt a * vonMangoldt b) N

private lemma vM_le_log {N k : ℕ} (hk : k ≤ N) (hN : 1 ≤ N) :
    vonMangoldt k ≤ Real.log N := by
  refine le_trans vonMangoldt_le_log ?_
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    simpa using Real.log_nonneg (by exact_mod_cast hN : (1:ℝ) ≤ (N:ℝ))
  · have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast h
    have hle : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast hk
    exact Real.log_le_log hkR hle

/-- The indicator of a proper prime power, weighted by `Λ`. -/
private lemma properPP_nonneg (j : ℕ) :
    0 ≤ (if IsPrimePow j ∧ ¬ j.Prime then vonMangoldt j else 0) := by
  split_ifs with h
  · exact vonMangoldt_nonneg
  · exact le_refl 0

private lemma properPP_le_log {N j : ℕ} (hk : j ≤ N) (hN : 1 ≤ N) :
    (if IsPrimePow j ∧ ¬ j.Prime then vonMangoldt j else 0) ≤ Real.log N := by
  split_ifs with h
  · exact vM_le_log hk hN
  · exact Real.log_nonneg (by exact_mod_cast hN)

private lemma r2_term_le {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) (hg : ¬ IsGoldbachSum N) :
    vonMangoldt k * vonMangoldt (N - k) ≤ Real.log N *
      ((if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0)
        + (if IsPrimePow (N - k) ∧ ¬ (N - k).Prime then vonMangoldt (N - k) else 0)) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hsum : 0 ≤ (if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0)
      + (if IsPrimePow (N - k) ∧ ¬ (N - k).Prime then vonMangoldt (N - k) else 0) :=
    add_nonneg (properPP_nonneg k) (properPP_nonneg (N - k))
  rcases eq_or_ne (vonMangoldt k) 0 with hk0 | hk0
  · calc vonMangoldt k * vonMangoldt (N - k) = 0 := by rw [hk0, zero_mul]
      _ ≤ Real.log N * ((if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0)
            + (if IsPrimePow (N - k) ∧ ¬ (N - k).Prime then vonMangoldt (N - k) else 0)) :=
          mul_nonneg hlogN hsum
  · have hppk : IsPrimePow k := vonMangoldt_ne_zero_iff.mp hk0
    rcases eq_or_ne (vonMangoldt (N - k)) 0 with hb0 | hb0
    · calc vonMangoldt k * vonMangoldt (N - k) = 0 := by rw [hb0, mul_zero]
        _ ≤ Real.log N * ((if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0)
              + (if IsPrimePow (N - k) ∧ ¬ (N - k).Prime then vonMangoldt (N - k) else 0)) :=
            mul_nonneg hlogN hsum
    · have hppb : IsPrimePow (N - k) := vonMangoldt_ne_zero_iff.mp hb0
      have hb1 : vonMangoldt (N - k) ≤ Real.log N := vM_le_log (Nat.sub_le N k) hN
      have hs : vonMangoldt k * vonMangoldt (N - k) ≤ vonMangoldt k * Real.log N :=
        mul_le_mul_of_nonneg_left hb1 vonMangoldt_nonneg
      by_cases hpk : k.Prime
      · have hpb : ¬ (N - k).Prime := by
          intro hpb'
          exact hg ⟨k, N - k, hpk, hpb', by omega⟩
        have hk1 : vonMangoldt k ≤ Real.log N := vM_le_log hk hN
        rw [if_neg (fun h => h.2 hpk), if_pos ⟨hppb, hpb⟩, zero_add]
        nlinarith [hk1, hb1, hlogN, vonMangoldt_nonneg (n := k), vonMangoldt_nonneg (n := N - k)]
      · rw [if_pos ⟨hppk, hpk⟩]
        nlinarith [hs, hlogN, properPP_nonneg (N - k), vonMangoldt_nonneg (n := k)]

private lemma sum_filter_vM_eq (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0)
      = ∑ k ∈ (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime),
          vonMangoldt k := by
  rw [Finset.sum_filter]

private lemma sum_reflect_vM (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
        (if IsPrimePow (N - k) ∧ ¬ (N - k).Prime then vonMangoldt (N - k) else 0)
      = ∑ k ∈ Finset.range (N + 1),
          (if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0) := by
  rw [← Finset.sum_range_reflect
    (f := fun j => if IsPrimePow j ∧ ¬ j.Prime then vonMangoldt j else 0) (n := N + 1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [show N + 1 - 1 - k = N - k by omega]

private lemma r2_le_logN {N : ℕ} (hN : 1 ≤ N) (hg : ¬ IsGoldbachSum N) :
    r2 N ≤ 2 * Real.log N *
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime),
        vonMangoldt k := by
  rw [r2_eq_sum_range]
  have hterm : ∑ k ∈ Finset.range (N + 1), vonMangoldt k * vonMangoldt (N - k) ≤
      ∑ k ∈ Finset.range (N + 1), Real.log N *
        ((if IsPrimePow k ∧ ¬ k.Prime then vonMangoldt k else 0)
          + (if IsPrimePow (N - k) ∧ ¬ (N - k).Prime then vonMangoldt (N - k) else 0)) :=
    Finset.sum_le_sum (fun k hk => r2_term_le hN (by simpa using hk) hg)
  refine le_trans hterm ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_filter_vM_eq, sum_reflect_vM,
    sum_filter_vM_eq]
  rw [show Real.log N * (∑ x ∈ (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime), vonMangoldt x
      + ∑ x ∈ (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime), vonMangoldt x)
      = 2 * Real.log N * ∑ x ∈ (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime), vonMangoldt x
      from by ring]

private lemma card_proper_le (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime)).card
      ≤ Nat.log 2 N * (Nat.sqrt N + 1) := by
  classical
  set A := (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime) with hA
  set B := Finset.range (Nat.sqrt N + 1) ×ˢ Finset.Icc 2 (Nat.log 2 N) with hB
  have hsub : A ⊆ B.image (fun x : ℕ × ℕ => x.1 ^ x.2) := by
    intro k hk
    rw [hA, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, hpp, hnp⟩ := hk
    have hkN' : k ≤ N := by omega
    obtain ⟨p, j, hprime, hjpos, hpj⟩ := (isPrimePow_def k).mp hpp
    have hprime : p.Prime := Nat.prime_iff.mpr hprime
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · have hj1 : j = 1 := by omega
        subst hj1
        rw [pow_one] at hpj
        have hnp2 : ¬ p.Prime := by rw [hpj]; exact hnp
        exact absurd hprime hnp2
      · exact h
    have hpsqrt : p ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      have h2 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hprime.one_le hj2
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ j := h2
        _ = k := hpj
        _ ≤ N := hkN'
    have hk2 : 2 ≤ k := by
      have hp2 : 2 ≤ p := hprime.two_le
      have hpp : 2 ^ 2 ≤ p ^ j := by
        calc 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
          _ ≤ p ^ j := Nat.pow_le_pow_right hprime.one_le hj2
      calc 2 ≤ 2 ^ 2 := by norm_num
        _ ≤ p ^ j := hpp
        _ = k := hpj
    have hjlog : j ≤ Nat.log 2 N := by
      rw [Nat.le_log_iff_pow_le (by norm_num) (by omega : N ≠ 0)]
      calc 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hprime.two_le j
        _ = k := hpj
        _ ≤ N := hkN'
    refine Finset.mem_image.mpr ⟨(p, j), ?_, hpj⟩
    rw [hB, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    exact ⟨by omega, hj2, hjlog⟩
  calc A.card ≤ (B.image (fun x : ℕ × ℕ => x.1 ^ x.2)).card := Finset.card_le_card hsub
    _ ≤ B.card := Finset.card_image_le
    _ = (Nat.sqrt N + 1) * (Nat.log 2 N + 1 - 2) := by
        rw [hB, Finset.card_product, Nat.card_Icc, Finset.card_range]
    _ ≤ Nat.log 2 N * (Nat.sqrt N + 1) := by
        rw [mul_comm]
        apply Nat.mul_le_mul_right
        omega

private lemma log_cube_le_quarter {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ^ 3 ≤ 1728 * (N : ℝ) ^ (1/4 : ℝ) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h1 : Real.log N ≤ 12 * (N:ℝ)^(1/12:ℝ) := by
    have h := Real.log_le_rpow_div hNpos.le (by norm_num : (0:ℝ) < 1/12)
    have e : (N:ℝ)^(1/12:ℝ)/(1/12) = 12 * (N:ℝ)^(1/12:ℝ) := by ring
    rw [e] at h
    exact h
  have ha3 : ((N:ℝ)^(1/12:ℝ))^3 = (N:ℝ)^(1/4:ℝ) := by
    rw [← Real.rpow_natCast ((N:ℝ)^(1/12:ℝ)) 3, ← Real.rpow_mul hNpos.le]
    norm_num
  have h3 := pow_le_pow_left₀ hlog0 h1 3
  have e2 : (12 * (N:ℝ)^(1/12:ℝ))^3 = 1728 * (N:ℝ)^(1/4:ℝ) := by
    rw [mul_pow, ha3]; norm_num
  rw [e2] at h3
  exact h3

private lemma big_sqrt {N : ℕ} (hN : 2 ^ 64 ≤ N) :
    (55296 : ℝ) * (N : ℝ) ^ (3/4 : ℝ) ≤ (N : ℝ) := by
  have hNR : (2:ℝ)^64 ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (0:ℝ) < (2:ℝ)^64 := by positivity
    linarith
  have h4 : (55296:ℝ)^4 ≤ (N:ℝ) := by
    have h2 : (55296:ℝ)^4 ≤ (2:ℝ)^64 := by norm_num
    linarith
  have hquarter : (55296:ℝ) ≤ (N:ℝ) ^ (1/4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ (55296:ℝ)^4) h4
      (by norm_num : (0:ℝ) ≤ (1/4 : ℝ))
    have hq : ((55296:ℝ)^4) ^ (1/4:ℝ) = 55296 := by
      rw [← Real.rpow_natCast (55296:ℝ) 4, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (55296:ℝ)),
        show ((4:ℕ):ℝ) * (1/4) = 1 by norm_num, Real.rpow_one]
    rwa [hq] at h
  have h3q : (N:ℝ) ^ (3/4:ℝ) * (N:ℝ) ^ (1/4:ℝ) = (N:ℝ) := by
    rw [← Real.rpow_add hNpos, show (3/4:ℝ) + 1/4 = 1 by norm_num, Real.rpow_one]
  calc (55296:ℝ) * (N:ℝ)^(3/4:ℝ) ≤ (N:ℝ)^(1/4:ℝ) * (N:ℝ)^(3/4:ℝ) :=
        mul_le_mul_of_nonneg_right hquarter (Real.rpow_nonneg hNpos.le _)
    _ = (N:ℝ) := by rw [mul_comm, h3q]

/-- `r2 N ≤ N/4` for a large even `N` that is not a sum of two primes: every contributing pair of
the antidiagonal has a coordinate which is a *proper* prime power, there are at most
`log₂N·(√N+1)` of those below `N`, and `4√N (log N)³ ≤ N/4` for `N ≥ 2^64`. -/
private lemma r2_le_div_four {N : ℕ} (hN : 2 ^ 64 ≤ N) (hg : ¬ IsGoldbachSum N) :
    r2 N ≤ (N : ℝ) / 4 := by
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ 2 ^ 64 := by norm_num
    omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast hN1)
  set A := (Finset.range (N + 1)).filter (fun k => IsPrimePow k ∧ ¬ k.Prime) with hA
  have hSA : ∑ k ∈ A, vonMangoldt k ≤ ((A.card : ℝ)) * Real.log N := by
    calc ∑ k ∈ A, vonMangoldt k ≤ ∑ k ∈ A, Real.log N := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [hA, Finset.mem_filter, Finset.mem_range] at hk
          exact vM_le_log (by omega) hN1
      _ = ((A.card : ℝ)) * Real.log N := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((A.card : ℝ)) ≤ (Nat.log 2 N : ℝ) * ((Nat.sqrt N : ℝ) + 1) := by
    exact_mod_cast card_proper_le N
  have hlog2 : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
    have hpow : (2:ℝ) ^ (Nat.log 2 N) ≤ (N:ℝ) := by
      have h := Nat.pow_log_le_self 2 (x := N) (by omega)
      exact_mod_cast h
    have hlt : (0:ℝ) < (2:ℝ) ^ (Nat.log 2 N) := by positivity
    have hlog := Real.log_le_log hlt hpow
    rw [Real.log_pow] at hlog
    have h2 : (1/2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have : (0:ℝ) < Real.log 2 := by linarith
    have hcast : ((Nat.log 2 N : ℕ) : ℝ) * Real.log 2 ≤ Real.log N := hlog
    nlinarith [hcast, h2, Real.log_nonneg (by exact_mod_cast hN1 : (1:ℝ) ≤ (N:ℝ))]
  have hsqrt2 : (Nat.sqrt N : ℝ) + 1 ≤ 2 * Real.sqrt N := by
    have h1 : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    linarith
  have hcardNN : 0 ≤ (A.card : ℝ) := by positivity
  have h1 : r2 N ≤ 2 * Real.log N * (((A.card : ℝ)) * Real.log N) := by
    refine le_trans (r2_le_logN hN1 hg) ?_
    exact mul_le_mul_of_nonneg_left hSA (by positivity)
  have h2 : 2 * Real.log N * (((A.card : ℝ)) * Real.log N)
      ≤ 2 * Real.log N * (((Nat.log 2 N : ℝ) * ((Nat.sqrt N : ℝ) + 1)) * Real.log N) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hcard hlogN
  have h3 : 2 * Real.log N * (((Nat.log 2 N : ℝ) * ((Nat.sqrt N : ℝ) + 1)) * Real.log N)
      ≤ 2 * Real.log N * (((2 * Real.log N) * (2 * Real.sqrt N)) * Real.log N) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ hlogN
    exact mul_le_mul hlog2 hsqrt2 (by linarith) (by linarith)
  have h4 : 2 * Real.log N * (((2 * Real.log N) * (2 * Real.sqrt N)) * Real.log N)
      = 8 * Real.sqrt N * (Real.log N)^3 := by ring
  have h5 : 8 * Real.sqrt N * (Real.log N)^3 ≤ 8 * Real.sqrt N * (1728 * (N:ℝ)^(1/4:ℝ)) := by
    refine mul_le_mul_of_nonneg_left (log_cube_le_quarter hN1) (by positivity)
  have h6 : 8 * Real.sqrt N * (1728 * (N:ℝ)^(1/4:ℝ)) = 13824 * (Real.sqrt N * (N:ℝ)^(1/4:ℝ)) := by ring
  have h7 : Real.sqrt N * (N:ℝ)^(1/4:ℝ) = (N:ℝ)^(3/4:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]
    norm_num
  have h8 : 13824 * (N:ℝ)^(3/4:ℝ) ≤ (N:ℝ)/4 := by
    have hbig := big_sqrt hN
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [hbig]
  calc r2 N ≤ 2 * Real.log N * (((A.card : ℝ)) * Real.log N) := h1
    _ ≤ 2 * Real.log N * (((Nat.log 2 N : ℝ) * ((Nat.sqrt N : ℝ) + 1)) * Real.log N) := h2
    _ ≤ 2 * Real.log N * (((2 * Real.log N) * (2 * Real.sqrt N)) * Real.log N) := h3
    _ = 8 * Real.sqrt N * (Real.log N)^3 := h4
    _ ≤ 8 * Real.sqrt N * (1728 * (N:ℝ)^(1/4:ℝ)) := h5
    _ = 13824 * (Real.sqrt N * (N:ℝ)^(1/4:ℝ)) := h6
    _ = 13824 * (N:ℝ)^(3/4:ℝ) := by rw [h7]
    _ ≤ (N:ℝ)/4 := h8

/-- LEAF. Page 13, the singular series lower bound and removal of proper prime powers.
For large even exceptions the representation error has size at least a fixed multiple of N.
OPEN. The singular series lower bound is also discussed on page 6. -/
theorem exceptional_gap150 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N → ¬ IsGoldbachSum N → c * N ≤ |E2 N| := by
  refine ⟨1/4, by norm_num, 2 ^ 64, fun N hN hEven hg => ?_⟩
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ 2 ^ 64 := by norm_num
    omega
  have hS : (1:ℝ) ≤ singular N := one_le_singular N hN1 hEven
  have hr2 : r2 N ≤ (N:ℝ)/4 := r2_le_div_four hN hg
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hE : E2 N = r2 N - (N:ℝ) * singular N := rfl
  have hmain : (N:ℝ) * 1 ≤ (N:ℝ) * singular N := mul_le_mul_of_nonneg_left hS hNnn
  have hnonpos : E2 N ≤ 0 := by
    rw [hE]
    linarith
  rw [abs_of_nonpos hnonpos, hE]
  nlinarith [hmain, hr2, hNnn]

/-- Counting lemma, the Chebyshev step of page 13 in the form the paper uses it: a second-moment
bound `∑ n² ≤ K t^{γ+2}` over a set of naturals forces the number of its elements below `t` to be
`O(t^γ)`. The proof splits the count at `t/2` and iterates that split, which is what makes the
exponent improve from `γ + 2` to `γ`. -/
private lemma card_filter_le_of_sum_sq_le {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) (T : Finset ℕ)
    (hT : ∀ n ∈ T, 4 ≤ n)
    (hsum : ∀ t : ℕ, 1 ≤ t →
      ∑ n ∈ T.filter (fun m => m ≤ t), (n : ℝ) ^ 2 ≤ K * (t : ℝ) ^ (γ + 2)) :
    ∀ X : ℕ, ((T.filter (fun m => m ≤ X)).card : ℝ) ≤
      4 * K / (1 - 2 ^ (-γ)) * (X : ℝ) ^ γ := by
  have h2lt : (2 : ℝ) ^ (-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : (0 : ℝ) < 1 - 2 ^ (-γ) := by linarith
  have hcoef : (0 : ℝ) < 4 * K / (1 - 2 ^ (-γ)) := by positivity
  have key : ∀ t : ℕ, ∀ m ≤ t, ((T.filter (fun k => k ≤ m)).card : ℝ) ≤
      4 * K / (1 - 2 ^ (-γ)) * (m : ℝ) ^ γ := by
    intro t
    induction t with
    | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      have hempty : T.filter (fun k => k ≤ 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n hn
        have := hT n hn
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hcoef.le (Real.zero_rpow_nonneg γ)
    | succ t ih =>
      intro m hm
      rcases Nat.lt_or_ge m (t + 1) with hlt | hge
      · exact ih m (by omega)
      · have hm' : m = t + 1 := by omega
        subst hm'
        have hpos : 0 < t + 1 := Nat.succ_pos t
        have hdiv : (t + 1) / 2 < t + 1 := Nat.div_lt_self hpos (by norm_num)
        have hIHE := ih ((t + 1) / 2) (by omega)
        set S : Finset ℕ := T.filter (fun n => (t + 1) / 2 < n ∧ n ≤ t + 1) with hSdef
        have hsplit : T.filter (fun n => n ≤ t + 1) =
            T.filter (fun n => n ≤ (t + 1) / 2) ∪ S := by
          rw [hSdef]
          ext n
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hnT, hnt⟩
            by_cases h : n ≤ (t + 1) / 2
            · exact Or.inl ⟨hnT, h⟩
            · exact Or.inr ⟨hnT, Nat.lt_of_not_le h, hnt⟩
          · rintro (⟨hnT, h⟩ | ⟨hnT, h1, h2⟩)
            · exact ⟨hnT, le_trans h (Nat.div_le_self (t + 1) 2)⟩
            · exact ⟨hnT, h2⟩
        have hdisj : Disjoint (T.filter (fun n => n ≤ (t + 1) / 2)) S := by
          rw [Finset.disjoint_left]
          intro n hn1 hn2
          simp only [Finset.mem_filter, hSdef] at hn1 hn2
          omega
        have hcard : ((T.filter (fun n => n ≤ t + 1)).card : ℝ)
            = ((T.filter (fun n => n ≤ (t + 1) / 2)).card : ℝ) + (S.card : ℝ) := by
          rw [hsplit, Finset.card_union_of_disjoint hdisj]
          push_cast
          ring
        have hhalf : (((t + 1) / 2 : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) / 2 := by
          have h := Nat.div_mul_le_self (t + 1) 2
          have h' : (((t + 1) / 2 : ℕ) : ℝ) * 2 ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast h
          linarith
        have hSge : ∀ n ∈ S, (((t + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
          intro n hn
          simp only [hSdef, Finset.mem_filter] at hn
          have hnat : t + 1 ≤ 2 * n := by omega
          have hcast2 : ((t + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hnat
          have hle : ((t + 1 : ℕ) : ℝ) / 2 ≤ (n : ℝ) := by linarith
          have h0 : (0 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) / 2 := by positivity
          exact pow_le_pow_left₀ h0 hle 2
        have hSsum : (S.card : ℝ) * (((t + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ ∑ n ∈ S, (n : ℝ) ^ 2 := by
          have h1 := Finset.card_nsmul_le_sum S (fun n => (n : ℝ) ^ 2)
            ((((t + 1 : ℕ) : ℝ) / 2) ^ 2) hSge
          simpa [nsmul_eq_mul] using h1
        have hSle : ∑ n ∈ S, (n : ℝ) ^ 2 ≤ K * ((t + 1 : ℕ) : ℝ) ^ (γ + 2) := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hsum (t + 1) (by omega))
          · intro n hn
            simp only [hSdef, Finset.mem_filter] at hn ⊢
            exact ⟨hn.1, hn.2.2⟩
          · intro n _ _
            positivity
        have hSpow : ((t + 1 : ℕ) : ℝ) ^ (γ + 2)
            = ((t + 1 : ℕ) : ℝ) ^ γ * ((t + 1 : ℕ) : ℝ) ^ 2 := by
          have ht0 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by positivity
          have h2 : ((t + 1 : ℕ) : ℝ) ^ (2 : ℝ) = ((t + 1 : ℕ) : ℝ) ^ 2 := by
            simp
          rw [Real.rpow_add ht0 γ 2, h2]
        have hcardS : (S.card : ℝ) ≤ 4 * K * ((t + 1 : ℕ) : ℝ) ^ γ := by
          rw [hSpow] at hSle
          have ht2 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) ^ 2 := by positivity
          have hR : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) ^ γ := Real.rpow_pos_of_pos (by positivity) γ
          have hsq : (((t + 1 : ℕ) : ℝ) / 2) ^ 2 = ((t + 1 : ℕ) : ℝ) ^ 2 / 4 := by ring
          rw [hsq] at hSsum
          nlinarith [hSsum, hSle, ht2, hR, hK]
        have hstep : 4 * K / (1 - 2 ^ (-γ)) * (((t + 1) / 2 : ℕ) : ℝ) ^ γ
            ≤ 4 * K / (1 - 2 ^ (-γ)) * (((t + 1 : ℕ) : ℝ) / 2) ^ γ := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhalf hγ.le) hcoef.le
        have hfin : 4 * K / (1 - 2 ^ (-γ)) * (((t + 1 : ℕ) : ℝ) / 2) ^ γ
            = (4 * K / (1 - 2 ^ (-γ)) * 2 ^ (-γ)) * ((t + 1 : ℕ) : ℝ) ^ γ := by
          have h2γ : (2 : ℝ) ^ γ ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) γ).ne'
          have hc0 : (1 : ℝ) - 2 ^ (-γ) ≠ 0 := ne_of_gt hden
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num)]
          field_simp
        have hconst : 4 * K / (1 - 2 ^ (-γ)) * 2 ^ (-γ) + 4 * K = 4 * K / (1 - 2 ^ (-γ)) := by
          have hc0 : (1 : ℝ) - 2 ^ (-γ) ≠ 0 := ne_of_gt hden
          field_simp
          ring
        calc ((T.filter (fun n => n ≤ t + 1)).card : ℝ)
            = ((T.filter (fun n => n ≤ (t + 1) / 2)).card : ℝ) + (S.card : ℝ) := hcard
          _ ≤ 4 * K / (1 - 2 ^ (-γ)) * ((((t + 1) / 2 : ℕ)) : ℝ) ^ γ
                + 4 * K * ((t + 1 : ℕ) : ℝ) ^ γ := add_le_add hIHE hcardS
          _ ≤ 4 * K / (1 - 2 ^ (-γ)) * (((t + 1 : ℕ) : ℝ) / 2) ^ γ
                + 4 * K * ((t + 1 : ℕ) : ℝ) ^ γ := by linarith [hstep]
          _ = (4 * K / (1 - 2 ^ (-γ)) * 2 ^ (-γ) + 4 * K) * ((t + 1 : ℕ) : ℝ) ^ γ := by
              rw [hfin]; ring
          _ = 4 * K / (1 - 2 ^ (-γ)) * ((t + 1 : ℕ) : ℝ) ^ γ := by rw [hconst]
  intro X
  exact key X X le_rfl

/-- LEAF. Page 13, Chebyshev on dyadic intervals and summation over the intervals.
The restriction a greater than two makes the final exponent positive.
OPEN. Finite initial exceptions must be absorbed into the constant. -/
theorem moment_to_count150 (a : ℝ) (ha : 2 < a) (bad : ℕ → Prop)
    [DecidablePred bad] (f : ℕ → ℝ)
    (hgap : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → bad N → c * N ≤ |f N|)
    (hmean : ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, (f N) ^ 2 ≤ C * (X : ℝ) ^ a) :
    ∃ D : ℝ, ∀ X : ℕ, 1 ≤ X →
      (((Finset.Icc 4 X).filter bad).card : ℝ) ≤ D * (X : ℝ) ^ (a - 2) := by
  obtain ⟨c, hc, N₀, hgap⟩ := hgap
  obtain ⟨C₀, hC₀⟩ := hmean
  have hCpos : (0 : ℝ) < max C₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hγ : (0 : ℝ) < a - 2 := by linarith
  have hKpos : (0 : ℝ) < max C₀ 1 / c ^ 2 := by positivity
  have h2lt : (2 : ℝ) ^ (-(a - 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : (0 : ℝ) < 1 - 2 ^ (-(a - 2)) := by linarith
  refine ⟨((max 4 N₀ : ℕ) : ℝ) + 1 + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))), ?_⟩
  intro X hX
  have hDD : (0 : ℝ) ≤ 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))) :=
    div_nonneg (by positivity) hden.le
  have hM0 : (0 : ℝ) ≤ ((max 4 N₀ : ℕ) : ℝ) + 1 := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hXγ : (1 : ℝ) ≤ (X : ℝ) ^ (a - 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (a - 2) := (Real.one_rpow _).symm
      _ ≤ (X : ℝ) ^ (a - 2) := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hX) hγ.le
  have hXγpos : (0 : ℝ) < (X : ℝ) ^ (a - 2) := lt_of_lt_of_le one_pos hXγ
  -- the set of exceptions inside `[max 4 N₀, X]`, where the gap hypothesis applies
  have hT4 : ∀ n ∈ (Finset.Icc (max 4 N₀) X).filter bad, 4 ≤ n := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    omega
  have hpoint : ∀ n ∈ (Finset.Icc (max 4 N₀) X).filter bad,
      c ^ 2 * (n : ℝ) ^ 2 ≤ (f n) ^ 2 := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h4, _⟩, hb⟩ := hn
    have hN₀ : N₀ ≤ n := by omega
    have h := hgap n hN₀ hb
    have h0 : (0 : ℝ) ≤ c * n := by positivity
    calc c ^ 2 * (n : ℝ) ^ 2 = (c * n) ^ 2 := by ring
      _ ≤ |f n| ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = (f n) ^ 2 := sq_abs _
  have hsum : ∀ t : ℕ, 1 ≤ t →
      ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (n : ℝ) ^ 2
        ≤ (max C₀ 1 / c ^ 2) * (t : ℝ) ^ ((a - 2) + 2) := by
    intro t ht
    have hTA : ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t)
        ⊆ Finset.Icc 1 t := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    have h1 : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (n : ℝ) ^ 2
        ≤ ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
            (f n) ^ 2 / c ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hp := hpoint n (Finset.mem_of_mem_filter n hn)
      have hc2 : (0 : ℝ) < c ^ 2 := by positivity
      rw [le_div_iff₀ hc2]
      linarith [hp]
    have h2 : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
          (f n) ^ 2 / c ^ 2
        = (∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (f n) ^ 2)
          / c ^ 2 := by
      rw [Finset.sum_div]
    have h3 : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (f n) ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 t, (f n) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hTA (fun n _ _ => by positivity)
    have h4 := hC₀ t ht
    have h5 : C₀ * (t : ℝ) ^ a ≤ max C₀ 1 * (t : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hnum : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
        (f n) ^ 2 ≤ max C₀ 1 * (t : ℝ) ^ a := le_trans h3 (le_trans h4 h5)
    have hexp : (t : ℝ) ^ ((a - 2) + 2) = (t : ℝ) ^ a := by
      have h : (a - 2) + 2 = a := by ring
      rw [h]
    rw [hexp]
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    calc ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (n : ℝ) ^ 2
        ≤ ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
            (f n) ^ 2 / c ^ 2 := h1
      _ = (∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
            (f n) ^ 2) * (c ^ 2)⁻¹ := by rw [h2, div_eq_mul_inv]
      _ ≤ (max C₀ 1 * (t : ℝ) ^ a) * (c ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = max C₀ 1 / c ^ 2 * (t : ℝ) ^ a := by
          rw [div_eq_mul_inv]
          ring

  have hmain := card_filter_le_of_sum_sq_le hKpos hγ
    ((Finset.Icc (max 4 N₀) X).filter bad) hT4 hsum X
  have hTeq : ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ X)
      = (Finset.Icc (max 4 N₀) X).filter bad := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, by omega⟩
  rw [hTeq] at hmain
  -- absorb the finitely many exceptions below `max 4 N₀`
  have hsub : (Finset.Icc 4 X).filter bad
      ⊆ Finset.range (max 4 N₀ + 1) ∪ (Finset.Icc (max 4 N₀) X).filter bad := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_range] at hn ⊢
    obtain ⟨⟨h4, hX'⟩, hb⟩ := hn
    by_cases h : n ≤ max 4 N₀
    · exact Or.inl (by omega)
    · exact Or.inr ⟨⟨by omega, hX'⟩, hb⟩
  have hcard1 : ((Finset.Icc 4 X).filter bad).card
      ≤ (max 4 N₀ + 1) + ((Finset.Icc (max 4 N₀) X).filter bad).card := by
    calc ((Finset.Icc 4 X).filter bad).card
        ≤ (Finset.range (max 4 N₀ + 1) ∪ (Finset.Icc (max 4 N₀) X).filter bad).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.range (max 4 N₀ + 1)).card + ((Finset.Icc (max 4 N₀) X).filter bad).card :=
          Finset.card_union_le _ _
      _ = (max 4 N₀ + 1) + ((Finset.Icc (max 4 N₀) X).filter bad).card := by
          rw [Finset.card_range]
  have hc1 : (((Finset.Icc 4 X).filter bad).card : ℝ)
      ≤ ((max 4 N₀ + 1 : ℕ) : ℝ) + (((Finset.Icc (max 4 N₀) X).filter bad).card : ℝ) := by
    have h : (((max 4 N₀ + 1) + ((Finset.Icc (max 4 N₀) X).filter bad).card : ℕ) : ℝ)
        = ((max 4 N₀ + 1 : ℕ) : ℝ) + (((Finset.Icc (max 4 N₀) X).filter bad).card : ℝ) := by
      push_cast
      ring
    rw [← h]
    exact_mod_cast hcard1
  calc (((Finset.Icc 4 X).filter bad).card : ℝ)
      ≤ ((max 4 N₀ + 1 : ℕ) : ℝ) + (((Finset.Icc (max 4 N₀) X).filter bad).card : ℝ) := hc1
    _ ≤ ((max 4 N₀ + 1 : ℕ) : ℝ) + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))) * (X : ℝ) ^ (a - 2) := by
        linarith [hmain]
    _ ≤ (((max 4 N₀ : ℕ) : ℝ) + 1 + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2)))) * (X : ℝ) ^ (a - 2) := by
        have hcast : ((max 4 N₀ + 1 : ℕ) : ℝ) = ((max 4 N₀ : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        rw [hcast]
        have hid :
            (((max 4 N₀ : ℕ) : ℝ) + 1 + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))))
                * (X : ℝ) ^ (a - 2) =
              (((max 4 N₀ : ℕ) : ℝ) + 1) * (X : ℝ) ^ (a - 2)
                + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))) * (X : ℝ) ^ (a - 2) := by
          ring
        have hstep : (((max 4 N₀ : ℕ) : ℝ) + 1) ≤ (((max 4 N₀ : ℕ) : ℝ) + 1) * (X : ℝ) ^ (a - 2) := by
          simpa using mul_le_mul_of_nonneg_left hXγ hM0
        rw [hid]
        linarith [hstep]

/-- Positive even integers have singular series at least one.
Source: P0029 page 6 display 2.10. This exposes the existing private Euler product proof. -/
theorem singular_ge_one461 (N : ℕ) (hEven : Even N) (hN : 0 < N) :
    (1 : ℝ) ≤ singular N := by
  exact one_le_singular N (by omega) hEven

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000
