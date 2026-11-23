module

public import LeanLab.HelfgottMajor.Decomp454c
public import LeanLab.HelfgottMajor.Decomp526a
public import LeanLab.HelfgottMajor.Decomp503a
public import LeanLab.HelfgottMajor.Lemma41Terms
public import LeanLab.HelfgottArcs.Statements
public import LeanLab.HelfgottMajor.TailIntegral123
public import LeanLab.HelfgottMajor.ZeroCount1623
public import LeanLab.HelfgottMajor.HalfMoment389
public import LeanLab.HelfgottMajor.Sec45
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Analytic.Order

/-!
Route burst 2026-11-12, split of Decomp123.gaussian_explicit_estimate.
P0014 Proposition 4.6, pages 43 and 44, display 4.43, with the recorded factor 6 repair.
The proof of Proposition 4.6 applies Lemma 4.1, the explicit formula with residue R,
then Lemma 4.4 to the zeros up to T and Lemma 4.5 to the zeros above T.
This file holds the shared development and the five analytic pieces that stay OPEN, each
one a named paper step and marked LEAF in its doc comment: Lemma 4.1 with its residue,
the logarithmic derivative bound of pages 36 and 37, Lemma 4.4 in the range above height
1, Corollary 3.2 at k equal to 0, and Lemma 4.5 as the zero sum step. The three statements
Decomp123 needs are proved from them in SplitGaussian123, which imports this file. The
namespace stays LeanLab.HelfgottMajor.SplitGaussian123, so every name Decomp123 and the
rest of the lab refer to is unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- A zero contribution with its analytic multiplicity, as in display 4.1 on page 31. -/
noncomputable def zeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (ρ : ℂ) : ℂ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ •
    (gaussianMellin δ ρ * (x : ℂ) ^ ρ)

/-- The zero sum over zeros of height at most T, Lemma 4.4, display 4.29 on page 39. -/
noncomputable def lowZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, zeroTerm χ δ x ρ.val

/-- The zero sum over zeros of height above T, Lemma 4.5 on page 40. -/
noncomputable def highZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, zeroTerm χ δ x ρ.val

/-! ## Route burst session 9 split, 2026-11-12

The three open pieces below are split further along P0014. Lemma 4.4 is split at height 1 as on
page 39; its very low range is PROVED from the shared lab zero count ZeroCount1623 and the
Gaussian half moment of display 4.42. Lemma 4.5 is reduced to its zero sum step, displays 4.33
to 4.35, with the integral bounds 4.36 and 4.41 PROVED in TailIntegral123.
These mirror Zeros269, Decomp269b and Decomp269c, which this file cannot import because they
import Decomp123, which imports this file. AI wrote this Lean code. Binary Goldbach is open.
-/

section RouteBurst9
open MeasureTheory

/-- PROVED. The critical line gives the square root of x in the proof of Proposition 4.6,
page 43. Copy of Zeros269.zero_term_norm. -/
theorem zero_term_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (hx : 0 < x) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    ‖zeroTerm χ δ x ρ‖ = mellinMassTerm χ δ ρ * sqrt x := by
  rw [zeroTerm, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ, ← sqrt_eq_rpow, mellinMassTerm]
  ring

/-- PROVED. P0014 page 43, proof of Proposition 4.6: the zeros up to T, all on the critical
line, contribute their Mellin mass times sqrt x. CONDITIONAL ON hzeros and hbudget only.
The index set is finite by ZeroCount1623.stripZeros_finite, with no hypothesis. -/
theorem low_zero_bound_of_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T B : ℝ) (hx : 0 < x)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hbudget : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) ≤ B) :
    ‖lowZeros χ δ x T‖ ≤ B * sqrt x := by
  haveI := ZeroCount1623.zeroIdx_finite χ T
  unfold lowZeros
  calc
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, ‖zeroTerm χ δ x ρ.val‖ :=
      norm_tsum_le_tsum_norm (Summable.of_finite)
    _ = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val * sqrt x := by
      apply tsum_congr
      intro ρ
      exact zero_term_norm χ δ x hx ρ.val
        (hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2)
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) * sqrt x :=
      tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (sqrt_nonneg x)

/-- PROVED. P0014 page 43, proof of Proposition 4.6: the zeros above T contribute at most their
Mellin mass times x, since the real part of each zero is below 1 and x is at least 1.
CONDITIONAL ON hsum and hbudget only. Copy of Zeros269.high_zero_bound_of_mellin_sum. -/
theorem high_zero_bound_of_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T B : ℝ) (hx : 1 ≤ x)
    (hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val))
    (hbudget : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤ B) :
    ‖highZeros χ δ x T‖ ≤ B * x := by
  have hx0 : 0 < x := by linarith
  have hpoint : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ‖zeroTerm χ δ x ρ.val‖ ≤
        mellinMassTerm χ δ ρ.val * x := by
    intro ρ
    rw [zeroTerm, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, mellinMassTerm]
    have hp : x ^ ρ.val.re ≤ x := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx ρ.property.2.2.1.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hz := (hsum.mul_right x).of_norm_bounded hpoint
  unfold highZeros
  calc
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ‖zeroTerm χ δ x ρ.val‖ :=
      norm_tsum_le_tsum_norm hz.norm
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val * x :=
      hz.norm.tsum_le_tsum hpoint (hsum.mul_right x)
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) * x := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hx0.le

/-- The part of the low Mellin mass with absolute imaginary part at most 1, P0014 page 39. -/
noncomputable def veryLowMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- PROVED. The partition at height 1 in the proof of Lemma 4.4, P0014 page 39.
No hypothesis: the index set is finite. -/
theorem mass_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) =
      veryLowMass χ δ T + middleMass χ δ T := by
  classical
  haveI := ZeroCount1623.zeroIdx_finite χ T
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := Summable.of_finite
  unfold veryLowMass middleMass
  rw [← (hm.indicator _).tsum_add (hm.indicator _)]
  apply tsum_congr
  intro ρ
  by_cases h : |ρ.val.im| ≤ 1 <;> simp [Set.indicator, h]

/-- LEAF: OPEN. P0014 Corollary 3.2, page 10, display 3.4 with k equal to 0 and c0 equal to 4.226:
for s with real part in the closed unit interval and abs Im s at least max(100, 4π² abs δ),
the Mellin transform F_δ of e^(-t²/2) e(δt) satisfies abs F_δ(s) + abs F_δ(1 - s) at most
c0 times the envelope. A statement about the Gaussian alone, with no zeros. It rests on
Theorem 3.1, pages 9 and 10, the saddle point analysis of Section 3. -/
theorem corollary_3_2_k0 (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im := by
  exact Decomp503a.corollary_from_saddle_pieces δ s hσ0 hσ1 hτ

/-- PROVED. The envelope of display 3.4 is at most the sum of its two nonnegative branches,
the Gaussian branch being absent at zero shift, where the first case of 3.4 is empty. -/
theorem corEnvelope_le (δ τ : ℝ) :
    corEnvelope δ τ ≤ exp (-0.1598 * |τ|) +
      if δ = 0 then 0 else exp (-0.1065 * (|τ| / (π * |δ|)) ^ 2) := by
  unfold corEnvelope
  by_cases hδ : δ = 0
  · subst hδ
    have h : ¬ |τ| < 3 / 2 * (π * 0) ^ 2 := by
      simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact not_lt.mpr (abs_nonneg τ)
    rw [if_neg h, if_pos rfl, add_zero]
  · have hsq : (τ / (π * δ)) ^ 2 = (|τ| / (π * |δ|)) ^ 2 := by
      rw [div_pow, div_pow, sq_abs, mul_pow, mul_pow, sq_abs]
    rw [ite_cond_eq_false _ _ (eq_false hδ), hsq]
    have h1 := exp_pos (-0.1598 * |τ|)
    have h2 := exp_pos (-0.1065 * (|τ| / (π * |δ|)) ^ 2)
    split_ifs <;> linarith

/-- PROVED, CONDITIONAL ON hcor, the k equal to 0 case of Corollary 3.2 on page 10:
one zero above height T has multiplicity weighted Mellin norm at most 4.226 times its
multiplicity times the envelope, as used in display 4.33 on page 41. -/
theorem zero_mass_le_envelope {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) :
    mellinMassTerm χ δ ρ.val ≤
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (4.226 * corEnvelope δ ρ.val.im) := by
  have hT' : max 100 (4 * π ^ 2 * |δ|) ≤ |ρ.val.im| := by
    rw [max_comm]; exact hT.trans ρ.property.2.2.2.le
  have h := hcor ρ.val ρ.property.2.1.le ρ.property.2.2.1.le hT'
  have hn : ‖gaussianMellin δ ρ.val‖ ≤ 4.226 * corEnvelope δ ρ.val.im := by
    linarith [norm_nonneg (gaussianMellin δ (1 - ρ.val))]
  unfold mellinMassTerm
  exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

end RouteBurst9

/-! ## Route burst session 9 split of Lemma 4.1, 2026-11-12

explicit_formula_remainder is split as in P0014 pages 31 to 37 and 44: Lemma 4.1 with its
residue R of display 4.2 written exactly, up to the O star of c0 in display 4.3; then the bound
of display 4.23 on the L'/L part of R. The arithmetic of page 44 is PROVED.
AI wrote this Lean code. Binary Goldbach is open.
-/

section RouteBurst9Lemma41

/-- The main part of the residue R of display 4.2, page 31, for the Gaussian, where η♥(0) is 1
as stated on page 44: log 2π for q equal to 1, and log(2π/q) + γ - L'(1, χ)/L(1, χ) else. -/
noncomputable def residueMain {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  if q = 1 then (log (2 * π) : ℂ) else
    ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

end RouteBurst9Lemma41

/-- PROVED. P0014 page 44, last display of the proof of Proposition 4.6:
(6.01 - 6)(1 + 6 abs delta) + 13.347 abs delta + 16.695 is below 14 abs delta + 17,
so the extra 0.01 of the contour term is absorbed into the residue budget for x at least 1. -/
theorem contour_residue_budget (q δ x : ℝ) (hx : 1 ≤ x) (hδ : 0 ≤ δ) :
    (log q + 6.01) * (1 + 6 * δ) / sqrt x + 3 * log q + 13.347 * δ + 16.695 ≤
      (log q + 6) * (1 + 6 * δ) / sqrt x + 3 * log q + 14 * δ + 17 := by
  have h := div_le_self (show 0 ≤ (0.01 : ℝ) * (1 + 6 * δ) by positivity)
    (one_le_sqrt.mpr hx)
  have hr := Lemma41Terms.repaired_R hδ
  have he : (log q + 6.01) * (1 + 6 * δ) / sqrt x =
      (log q + 6) * (1 + 6 * δ) / sqrt x + 0.01 * (1 + 6 * δ) / sqrt x := by ring
  rw [he]
  linarith

/-- PROVED. P0014 pages 43 and 44, the triangle inequality and arithmetic that combine
Lemmas 4.1, 4.4 and 4.5 into display 4.43, written out without Decomp123.gaussianError. -/
theorem assembly_of_components (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hformula : ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x)
    (hL : ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x)
    (hH : ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x := by
  obtain ⟨R, hR, hE⟩ := hformula
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hbudget := contour_residue_budget (q : ℝ) |δ| x hx (abs_nonneg δ)
  have htri : ‖Schi etaHeart χ δ x -
      (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ +
        ‖lowZeros χ δ x T‖ + ‖highZeros χ δ x T‖ + ‖R‖ := by
    calc
      _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T + R) -
          lowZeros χ δ x T - highZeros χ δ x T - R‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  have heq :
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x =
      log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) *
          sqrt x + (3 * log q + 14 * |δ| + 17) +
        (log q + 6) * (1 + 6 * |δ|) / sqrt x := by
    generalize hroot : sqrt x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    have hsne : s ≠ 0 := by rw [← hroot]; exact hs0.ne'
    rw [hxx]
    field_simp [hsne]
  rw [heq]
  linarith

end LeanLab.HelfgottMajor.SplitGaussian123

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real MeasureTheory

/-- Derived convergence support for P0014 page 41 display 4.33.
The two sided exponential and Gaussian envelope is summable under a polynomial
multiplicity count in each unit shell. No pairing or sharp density bound is used.
CONDITIONAL ON hcount, the explicit count input. -/
theorem tail_envelope_summable_of_shell_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T C : ℝ) (hT : 1 ≤ T)
    (hcount : ∀ n : ℕ,
      (∑' ρ : {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} // ⌊|ρ.val.im|⌋₊ = n},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ)) ≤
          C * ((n : ℝ) + 1) ^ 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
  classical
  let I := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}
  have hfinite (n : ℕ) : {ρ : I | ⌊|ρ.val.im|⌋₊ = n}.Finite := by
    apply ((ZeroCount1623.stripZeros_finite χ ((n : ℝ) + 1)).preimage
      (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro ρ hρ
    refine ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2.1, ?_⟩
    have h := Nat.lt_floor_add_one |ρ.val.im|
    rw [hρ] at h
    exact h.le
  have hs (a : ℝ) (ha : 0 < a) :
      Summable (fun ρ : I =>
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          exp (-a * |ρ.val.im|)) :=
    Decomp454c.summable_exp_real_of_shell_count (fun ρ : I => |ρ.val.im|)
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))
      C a ha (fun _ => Nat.cast_nonneg _) (fun _ => abs_nonneg _) hfinite hcount
  have he := hs 0.1598 (by norm_num)
  have hg : Summable (fun ρ : I =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
    by_cases hδ : δ = 0
    · simp [hδ]
    · simp only [if_neg hδ]
      have hd : 0 < (π * |δ|) ^ 2 := sq_pos_of_pos (mul_pos pi_pos (abs_pos.mpr hδ))
      apply (hs (0.1065 / (π * |δ|) ^ 2) (by positivity)).of_norm_bounded
      intro ρ
      rw [Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply exp_le_exp.mpr
      have ht : 1 ≤ |ρ.val.im| := hT.trans ρ.property.2.2.2.le
      have hsquare : |ρ.val.im| ≤ |ρ.val.im| ^ 2 := by nlinarith
      rw [div_pow]
      have hh := div_le_div_of_nonneg_right hsquare hd.le
      convert mul_le_mul_of_nonpos_left hh (show -(0.1065 : ℝ) ≤ 0 by norm_num) using 1 <;> ring
  convert he.add hg using 1
  ext ρ
  exact mul_add _ _ _

/-- A pairing free comparison for P0014 page 41 display 4.33.
CONDITIONAL ON hcor and the explicit summability hsum.
Both signs and analytic multiplicities remain in the envelope sum. -/
theorem tail_mass_le_two_sided_envelope {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)))) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
  have hp (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) :
      mellinMassTerm χ δ ρ.val ≤
        4.226 * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
    refine (zero_mass_le_envelope χ δ T hT hcor ρ).trans ?_
    have he := mul_le_mul_of_nonneg_left (corEnvelope_le δ ρ.val.im)
      (show 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * 4.226
        by positivity)
    convert he using 1 <;> ring
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
    apply (hsum.mul_left 4.226).of_norm_bounded
    intro ρ
    rw [Real.norm_of_nonneg (by unfold mellinMassTerm; positivity)]
    exact hp ρ
  refine ⟨hm, ?_⟩
  exact (hm.tsum_le_tsum hp (hsum.mul_left 4.226)).trans_eq (tsum_mul_left)

end LeanLab.HelfgottMajor.SplitGaussian123
