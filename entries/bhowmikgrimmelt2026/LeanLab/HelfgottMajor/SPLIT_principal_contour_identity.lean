module

public import LeanLab.HelfgottMajor.SPLIT_explicit_formula_remainder_E
public import LeanLab.HelfgottMajor.Principal457
public import LeanLab.HelfgottMajor.Contour457
public import LeanLab.HelfgottMajor.Decomp457b
public import LeanLab.PNTPort.ExplicitPsi1.ZeroSum
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
Split of `principal_contour_identity` in `Decomp457a.lean`.

The one identity of the target combines four analytic steps.  This file cuts it along
exactly those steps, each carried on its own vertical contour, in the sign convention of
the logarithmic derivative, which is minus the Dirichlet series of the weighted von
Mangoldt sum:

1. the weighted prime sum is minus the vertical integral at real part two of the
   logarithmic derivative of the L-function against the shifted Gaussian transform and
   the scale factor (Dirichlet series to contour);
2. moving that line from real part two down to real part minus one half, in one step as
   P0014 Lemma 4.1 does at page 33 display 4.7, crosses the pole at one, whose residue is
   minus the main term, every nontrivial zero, which gives the two zero sums split at the
   height `T`, and the pole at zero, which gives log of two pi; the main term exists only
   at conductor one, which is the branching guard;
3. retired by U-1648: the first cut stopped at real part one half, which is not a contour,
   since the logarithmic derivative has a non integrable pole at every zero on that line;
4. at conductor one the L-function is the Riemann zeta function, so that last contour is
   the principal contour of the target.

Each leaf is one of those steps, so no leaf restates the target; the assembly at the end
chains the three live leaves and its own argument is rewriting and ring only.

Degenerate values.  Every contour below is an integral over all of `ℝ` on a line at real
part two or minus one half, where the integrand is continuous, so the integration variable
never divides.  The only division is the
fixed factor `1 / (2 * π)`, and `2 * π` is not zero.  The branching term `if q = 1` is
kept verbatim in every statement that has it, so it is the main term at `q = 1` and zero
otherwise.  At `δ = 0` the shift term `-δ` is `0`, the transform is the plain Gaussian and
the height hypothesis `max (4 * π ^ 2 * |δ|) 100 ≤ T` reads `100 ≤ T`, so no leaf
degenerates at the unshifted frequency.  The scale hypothesis is only `1 ≤ x`, so the
admissible range is `x ≥ 1`: no negative and no zero scale occurs, every power
`(x : ℂ) ^ s` is taken at positive base, and at `x = 1` the scale factor is `1` unless the
exponent is `0`.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

open scoped ArithmeticFunction

/-- The complex `enorm` is the `ofReal` of the norm. -/
private theorem wip_enorm_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg z)]
  rfl

/-- The von Mangoldt function vanishes at zero. -/
private theorem wip_vonMangoldt_zero : ArithmeticFunction.vonMangoldt 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg not_isPrimePow_zero]

/-! ### A. Integrability on the line of real part two -/

/-- The uniform bound of the Gaussian Mellin transform on a vertical line, at natural
real part. -/
private theorem gaussian_line_norm_le (δ : ℝ) (m : ℕ) (t : ℝ) :
    ‖gaussianMellin δ ((m : ℂ) + t * Complex.I)‖ ≤
      ∫ x in Set.Ioi (0 : ℝ), x ^ ((m : ℝ) - 1) * exp (-x ^ 2 / 2) := by
  have h := Gaussian269.mellin_norm_le δ ((m : ℂ) + t * Complex.I)
  simpa using h

/-- One recurrence step at natural real part: a factor `m + it` is gained. -/
private theorem gaussian_line_step (δ : ℝ) (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ‖gaussianMellin δ ((m : ℂ) + t * Complex.I)‖ * ‖((m : ℂ) + t * Complex.I)‖ ≤
      ‖gaussianMellin δ (((m + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ *
          ‖gaussianMellin δ (((m + 1 : ℕ) : ℂ) + t * Complex.I)‖ := by
  have hrec := Continuation457.gaussian_mellin_recurrence δ ((m : ℂ) + t * Complex.I)
    (by simpa using hm)
  have e2 : ((m : ℂ) + t * Complex.I) + 2 = ((m + 2 : ℕ) : ℂ) + t * Complex.I := by
    push_cast; ring
  have e1 : ((m : ℂ) + t * Complex.I) + 1 = ((m + 1 : ℕ) : ℂ) + t * Complex.I := by
    push_cast; ring
  rw [e2, e1] at hrec
  have hnorm : ‖((m : ℂ) + t * Complex.I) * gaussianMellin δ ((m : ℂ) + t * Complex.I)‖
      = ‖gaussianMellin δ ((m : ℂ) + t * Complex.I)‖ * ‖((m : ℂ) + t * Complex.I)‖ := by
    rw [norm_mul, mul_comm]
  rw [← hnorm, hrec]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul]

/-- `‖m + it‖` dominates `sqrt (1 + t^2)` for real part at least one. -/
private theorem gaussian_line_norm_sqrt (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    sqrt (1 + t ^ 2) ≤ ‖((m : ℂ) + t * Complex.I)‖ := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : ‖((m : ℂ) + t * Complex.I)‖ ^ 2 = (m : ℝ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hrew : sqrt ((m : ℝ) ^ 2 + t ^ 2) = ‖((m : ℂ) + t * Complex.I)‖ := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [← hrew]
  apply sqrt_le_sqrt
  nlinarith

/-- The decay bound on the line of real part two. -/
private theorem gaussian_line_decay (δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖gaussianMellin δ (2 + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  set B2 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB2
  set B3 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((3 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB3
  set B4 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((4 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB4
  set B5 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((5 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB5
  set B6 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((6 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB6
  have hB40 : 0 ≤ B4 := by
    rw [hB4]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  have hB50 : 0 ≤ B5 := by
    rw [hB5]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  have hB60 : 0 ≤ B6 := by
    rw [hB6]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  refine ⟨B6 + c * B5 + c * (B5 + c * B4), ?_, fun t => ?_⟩
  · have h1 : 0 ≤ B6 + c * B5 := by nlinarith
    have h2 : 0 ≤ B5 + c * B4 := by nlinarith
    nlinarith
  · have hsq : (0 : ℝ) < sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h5' : ‖gaussianMellin δ (((3 + 2 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B5 := by
      have h5 := gaussian_line_norm_le δ 5 t
      rw [hB5]
      simpa using h5
    have h4' : ‖gaussianMellin δ (((3 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B4 := by
      have h4 := gaussian_line_norm_le δ 4 t
      rw [hB4]
      simpa using h4
    have s3 : ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ * ‖((3 : ℂ) + t * Complex.I)‖
        ≤ B5 + c * B4 := by
      have hraw := gaussian_line_step δ 3 (by norm_num) t
      rw [← hc] at hraw
      have hcd : c * ‖gaussianMellin δ (((3 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ c * B4 :=
        mul_le_mul_of_nonneg_left h4' hc0
      calc ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ * ‖((3 : ℂ) + t * Complex.I)‖
          ≤ ‖gaussianMellin δ (((3 + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
            c * ‖gaussianMellin δ (((3 + 1 : ℕ) : ℂ) + t * Complex.I)‖ := hraw
        _ ≤ B5 + c * B4 := by linarith
    have h6'' : ‖gaussianMellin δ (((4 + 2 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B6 := by
      have h6 := gaussian_line_norm_le δ 6 t
      rw [hB6]
      simpa using h6
    have h5'' : ‖gaussianMellin δ (((4 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B5 := by
      have h5 := gaussian_line_norm_le δ 5 t
      rw [hB5]
      simpa using h5
    have s4 : ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ * ‖((4 : ℂ) + t * Complex.I)‖
        ≤ B6 + c * B5 := by
      have hraw := gaussian_line_step δ 4 (by norm_num) t
      rw [← hc] at hraw
      have hcd : c * ‖gaussianMellin δ (((4 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ c * B5 :=
        mul_le_mul_of_nonneg_left h5'' hc0
      calc ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ * ‖((4 : ℂ) + t * Complex.I)‖
          ≤ ‖gaussianMellin δ (((4 + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
            c * ‖gaussianMellin δ (((4 + 1 : ℕ) : ℂ) + t * Complex.I)‖ := hraw
        _ ≤ B6 + c * B5 := by linarith
    have hs3 : (0 : ℝ) < ‖((3 : ℂ) + t * Complex.I)‖ :=
      lt_of_lt_of_le hsq (gaussian_line_norm_sqrt 3 (by norm_num) t)
    have hs4 : (0 : ℝ) < ‖((4 : ℂ) + t * Complex.I)‖ :=
      lt_of_lt_of_le hsq (gaussian_line_norm_sqrt 4 (by norm_num) t)
    have sq3 := gaussian_line_norm_sqrt 3 (by norm_num) t
    have sq4 := gaussian_line_norm_sqrt 4 (by norm_num) t
    have sq2 := gaussian_line_norm_sqrt 2 (by norm_num) t
    have d3 : ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ ≤ (B5 + c * B4) / sqrt (1 + t ^ 2) := by
      have h1 : ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ ≤
          (B5 + c * B4) / ‖((3 : ℂ) + t * Complex.I)‖ := by
        rw [le_div_iff₀ hs3]; linarith
      exact h1.trans (div_le_div_of_nonneg_left (by nlinarith) hsq sq3)
    have d4 : ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ ≤ (B6 + c * B5) / sqrt (1 + t ^ 2) := by
      have h1 : ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ ≤
          (B6 + c * B5) / ‖((4 : ℂ) + t * Complex.I)‖ := by
        rw [le_div_iff₀ hs4]; linarith
      exact h1.trans (div_le_div_of_nonneg_left (by nlinarith) hsq sq4)
    have hraw := gaussian_line_step δ 2 (by norm_num) t
    rw [← hc] at hraw
    have d3' : ‖gaussianMellin δ (((2 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤
        (B5 + c * B4) / sqrt (1 + t ^ 2) := d3
    have d4' : ‖gaussianMellin δ (((2 + 2 : ℕ) : ℂ) + t * Complex.I)‖ ≤
        (B6 + c * B5) / sqrt (1 + t ^ 2) := d4
    have hprod : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * ‖((2 : ℂ) + t * Complex.I)‖
        ≤ (B6 + c * B5 + c * (B5 + c * B4)) / sqrt (1 + t ^ 2) := by
      have hcd : c * ‖gaussianMellin δ (((2 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤
          c * ((B5 + c * B4) / sqrt (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left d3' hc0
      have heq : (B6 + c * B5) / sqrt (1 + t ^ 2) +
          c * ((B5 + c * B4) / sqrt (1 + t ^ 2)) =
          (B6 + c * B5 + c * (B5 + c * B4)) / sqrt (1 + t ^ 2) := by
        field_simp
      calc ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * ‖((2 : ℂ) + t * Complex.I)‖
          ≤ ‖gaussianMellin δ (((2 + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
            c * ‖gaussianMellin δ (((2 + 1 : ℕ) : ℂ) + t * Complex.I)‖ := hraw
        _ ≤ (B6 + c * B5) / sqrt (1 + t ^ 2) +
            c * ((B5 + c * B4) / sqrt (1 + t ^ 2)) := add_le_add d4' hcd
        _ = _ := heq
    have key : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * (1 + t ^ 2) ≤
        B6 + c * B5 + c * (B5 + c * B4) := by
      have h1 : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ *
          ‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2) ≤
          B6 + c * B5 + c * (B5 + c * B4) := by
        have h := mul_le_mul_of_nonneg_right hprod hsq.le
        rwa [div_mul_cancel₀ _ hsq.ne'] at h
      have h3 : sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2) = 1 + t ^ 2 :=
        Real.mul_self_sqrt (by positivity)
      have h4 : sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2)
          ≤ ‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right sq2 hsq.le
      rw [h3] at h4
      calc ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * (1 + t ^ 2)
          ≤ ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ *
            (‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
        _ = ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ *
            ‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2) := by ring
        _ ≤ _ := h1
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
    simpa using key

/-- The Gaussian Mellin transform is integrable on the line of real part two. -/
private theorem gaussian_line_integrable (δ : ℝ) :
    Integrable (fun t : ℝ => gaussianMellin δ (2 + t * Complex.I)) := by
  obtain ⟨C, hC0, hC⟩ := gaussian_line_decay δ
  have hcont : Continuous (fun t : ℝ => gaussianMellin δ (2 + t * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hpos : 0 < ((2 : ℂ) + t * Complex.I).re := by simp
    exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * Complex.I)
      (Continuation457.gaussian_mellin_differentiable δ _ hpos).continuousAt (by fun_prop)
  refine Integrable.mono' (g := fun t : ℝ => C * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable ?_
  filter_upwards with t
  simpa [div_eq_mul_inv] using hC t

/-! ### B. The logarithmic derivative as the twisted von Mangoldt series -/

/-- `logDeriv (LFunction χ) s` is minus the Dirichlet series of `χ * Λ` on `Re s > 1`. -/
private theorem logDeriv_LFunction_eq_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      - LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
          fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
  have h1 : logDeriv (DirichletCharacter.LFunction χ) s =
      deriv (LSeries (χ ·)) s / LSeries (χ ·) s := by
    rw [logDeriv, Pi.div_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
  have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have htw2 : LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
      fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
      - deriv (LSeries (χ ·)) s / LSeries (χ ·) s := by
    simpa using htw
  rw [h1]
  have hneg : deriv (LSeries (χ ·)) s / LSeries (χ ·) s =
      - LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
          fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    have h2 := congrArg Neg.neg htw2
    simp only [neg_div, neg_neg] at h2
    exact h2.symm
  exact hneg

/-! ### C. Pointwise Mellin inversion at real part two -/

/-- `(x / n) ^ s = ((n / x)) ^ (-s)` for positive `x` and `n`. -/
private theorem cpow_div_neg (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ((x / n : ℝ) : ℂ) ^ s = (((n : ℝ) / x : ℝ) : ℂ) ^ (-s) := by
  have hz : ((x / n : ℝ) : ℂ) = (((n : ℝ) / x : ℝ) : ℂ)⁻¹ := by
    have hreal : (x / (n : ℝ) : ℝ) = ((n : ℝ) / x)⁻¹ := by field_simp
    rw [hreal]
    push_cast
    ring
  rw [hz, Complex.inv_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / x) s,
    Complex.cpow_neg]

/-- The pointwise Mellin inversion: the vertical integral at real part two recovers the
Gaussian weight at `n / x`, up to the factor `2 * π`. -/
private theorem mellin_inversion_line (δ : ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) =
      (exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x)) := by
  have hy : (0 : ℝ) < (n : ℝ) / x := by positivity
  have hcont2 : Continuous (fun u : ℝ => (exp (-u ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * u)) := by
    unfold LeanLab.HelfgottArcs.e
    fun_prop
  have hinv := mellinInv_mellin_eq 2 (fun u : ℝ => (exp (-u ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * u)) hy
    (Gaussian269.mellin_integrable δ 2 (by norm_num)) (gaussian_line_integrable δ) hcont2.continuousAt
  have hpt : ∀ t : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℕ) : ℂ) + t * Complex.I)) =
      ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) := by
    intro t
    have h := cpow_div_neg x hx n hn (((2 : ℕ) : ℂ) + t * Complex.I)
    rw [h]
  have hgoal : (1 / (2 * π) : ℂ) * ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℕ) : ℂ) + t * Complex.I)) *
          gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) := by
    congr 1
    congr 1
    funext t
    rw [hpt t]
    ring
  rw [hgoal]
  simpa [mellinInv, gaussianMellin] using hinv

/-! ### D. Interchange of the sum over `n` and the integral over `t` -/

/-- `x ^ s * n ^ (-s) = (x / n) ^ s` for positive `x` and `n`. -/
private theorem cpow_div_eq (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (x : ℂ) ^ s * (n : ℂ) ^ (-s) = ((x / n : ℝ) : ℂ) ^ s := by
  have h1 : ((x / n : ℝ) : ℂ) ^ s =
      (x : ℂ) ^ s * (((1 : ℝ) / n : ℝ) : ℂ) ^ s := by
    rw [show (x / n : ℝ) = x * (1 / (n : ℝ)) by ring]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (by positivity) s]
  have h2 : (((1 : ℝ) / n : ℝ) : ℂ) ^ s = ((n : ℂ) ^ s)⁻¹ := by
    rw [show ((1 : ℝ) / n : ℝ) = ((n : ℝ))⁻¹ by ring]
    rw [Complex.ofReal_inv]
    exact Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg n) s
  rw [h1, h2, Complex.cpow_neg]

/-- The pure interchange: no constant is pulled out of any integral. -/
private theorem series_integral_swap (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    (∫ t : ℝ, ∑' n : ℕ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
      ∑' n : ℕ, ∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) := by
  have hx0 : 0 < x := by linarith
  have hGc : Continuous (fun t : ℝ => gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hpos : 0 < ((((2 : ℕ) : ℂ) + t * Complex.I)).re := by simp
    exact ContinuousAt.comp (f := fun t : ℝ => (((2 : ℕ) : ℂ) + t * Complex.I))
      (Continuation457.gaussian_mellin_differentiable δ _ hpos).continuousAt (by fun_prop)
  have hGint : Integrable (fun t : ℝ => ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖) := by
    simpa using (gaussian_line_integrable δ).norm
  have hGfin : ∫⁻ t : ℝ,
      ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ < ⊤ := by
    have h := hGint.hasFiniteIntegral
    rw [HasFiniteIntegral] at h
    simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _)] using h
  have hmaj : ∀ (n : ℕ) (t : ℝ),
      ‖-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖ ≤
      (Λ n : ℝ) * (x / n) ^ 2 * ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
    intro n t
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hxn : (0 : ℝ) < x / n := div_pos hx0 hnpos
      have hchi : ‖(χ ((n : ℕ) : ZMod q) : ℂ)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one (χ := χ) ((n : ℕ) : ZMod q)
      have hcp : ‖((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)‖ = (x / n) ^ 2 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxn]
        norm_num
      have hΛ : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hstep : ‖(χ ((n : ℕ) : ZMod q) : ℂ)‖ * (x / n) ^ 2 *
          ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ ≤
          1 * (x / n) ^ 2 * ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
        have hz : (0 : ℝ) ≤ (x / n) ^ 2 * ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
          positivity
        nlinarith [norm_nonneg (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I))]
      rw [norm_neg, norm_mul, norm_mul, norm_mul, hcp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hΛ]
      nlinarith [hstep, hΛ]
  have hbase : Summable (fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ 2) := by
    have hC : Summable (fun n : ℕ => ((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (2 : ℂ)) := by
      have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) (by norm_num)
      rw [LSeriesSummable] at h
      unfold LSeries.term at h
      exact h.congr fun n => by
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, ite_false]
    have hL : Summable (fun n : ℕ => ‖((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (2 : ℂ)‖) := hC.norm
    have heq : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (2 : ℂ)‖ =
        (Λ n : ℝ) / (n : ℝ) ^ 2 := by
      intro n
      rcases eq_or_ne n 0 with h0 | h0
      · subst h0
        simp [wip_vonMangoldt_zero]
      · have hΛ : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) from by norm_num, Complex.cpow_natCast, norm_div,
          norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hΛ]
    simpa only [heq] using hL
  have hcoef : Summable (fun n : ℕ => (Λ n : ℝ) * (x / n) ^ 2) := by
    have h2 : Summable (fun n : ℕ => (x : ℝ) ^ 2 * ((Λ n : ℝ) / (n : ℝ) ^ 2)) :=
      hbase.mul_left _
    refine h2.congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn]
    · field_simp
  have hcoef0 : ∀ n : ℕ, (0 : ℝ) ≤ (Λ n : ℝ) * (x / n) ^ 2 := by
    intro n
    have hΛ : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  have hmaj2 : ∀ n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) *
        (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖ ≤
      ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
        ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
    intro n
    calc ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
          (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
            ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
          refine lintegral_mono fun t => ?_
          calc ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
                (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
                  ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖
              ≤ ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2 *
                  ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖) :=
                ENNReal.ofReal_le_ofReal (hmaj n t)
            _ = ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
                  ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
                ENNReal.ofReal_mul (hcoef0 n)
      _ = ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
            ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
          lintegral_const_mul'' _ (hGc.aemeasurable.norm.ennreal_ofReal)
  have hf : ∀ n : ℕ, AEStronglyMeasurable (fun t : ℝ =>
      -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) := by
    intro n
    by_cases hn : n = 0
    · have hzero : (fun t : ℝ => -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
          (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) = fun _ => 0 := by
        funext t
        simp [hn]
      rw [hzero]
      exact aestronglyMeasurable_const
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hxn : (0 : ℝ) < x / n := div_pos hx0 hnpos
      have hcc : Continuous fun t : ℝ =>
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) := by
        refine Continuous.comp ?_ (by fun_prop : Continuous fun t : ℝ => (((2 : ℕ) : ℂ) + t * Complex.I))
        exact continuous_iff_continuousAt.mpr fun z =>
          continuousAt_const_cpow (by exact_mod_cast hxn.ne')
      exact ((hGc.mul hcc).const_mul _).neg.aestronglyMeasurable
  have hf' : (∑' n : ℕ, ∫⁻ t : ℝ, ‖-(((Λ n : ℝ) : ℂ) *
        (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖ₑ) ≠ ⊤ := by
    have hof : (∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) *
          (χ ((n : ℕ) : ZMod q) : ℂ) *
          (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖) ≠ ⊤ := by
      have hsum : ∑' n : ℕ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) ≠ ⊤ := by
        have h := ENNReal.ofReal_tsum_of_nonneg (f := fun n : ℕ => (Λ n : ℝ) * (x / n) ^ 2)
          hcoef0 hcoef
        rw [← h]
        exact ENNReal.ofReal_ne_top
      refine ne_of_lt ?_
      calc ∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) *
            (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖
          ≤ ∑' n : ℕ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
              ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
            ENNReal.tsum_le_tsum hmaj2
        _ = (∑' n : ℕ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2)) *
              ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
            ENNReal.tsum_mul_right
        _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hsum) hGfin
    simpa only [wip_enorm_eq_ofReal] using hof
  rw [integral_tsum hf hf']

/-! ### E. The per-`n` value of the vertical integral, and the leaf -/

/-- `etaHeart` is the plain Gaussian on the positive half line. -/
private theorem etaHeart_eq_exp {y : ℝ} (hy : 0 < y) :
    etaHeart y = Real.exp (-y ^ 2 / 2) := by
  rw [etaHeart, if_pos hy]

/-- The `n`-th vertical integral: the `2 π` times the Gaussian weight at `n / x`. -/
private theorem integral_summand (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (n : ℕ) :
    (∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
      -(2 * π * (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        ((etaHeart ((n : ℝ) / x) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))))) := by
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    simp [wip_vonMangoldt_zero]
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    have hx0 : (0 : ℝ) < x := by linarith
    have hpi : (2 * π : ℂ) ≠ 0 := by
      have h : (0 : ℝ) < 2 * π := by positivity
      exact_mod_cast ne_of_gt h
    have hpull : (∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
        (-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ))) *
          ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) := by
      rw [show (fun t : ℝ => -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
          (fun t : ℝ => (-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ))) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) from by
        funext t
        ring]
      rw [integral_const_mul]
    have hI : (∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)) =
        2 * π * ((Real.exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) *
          LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))) := by
      have h := mellin_inversion_line δ x hx0 n hn
      have hinv : (1 / (2 * π) : ℂ)⁻¹ = 2 * π := by
        rw [one_div, inv_inv]
      have hne : (1 / (2 * π) : ℂ) ≠ 0 := by
        rw [one_div]
        exact inv_ne_zero hpi
      calc (∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))
          = (1 / (2 * π) : ℂ)⁻¹ * ((1 / (2 * π) : ℂ) *
              ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
                ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
        _ = (1 / (2 * π) : ℂ)⁻¹ * ((Real.exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) *
              LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))) := by rw [h]
        _ = 2 * π * ((Real.exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) *
              LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))) := by rw [hinv]
    rw [hpull, hI, ← etaHeart_eq_exp (by positivity : (0 : ℝ) < (n : ℝ) / x)]
    ring

/-- The pointwise expansion of the integrand as the twisted von Mangoldt series. -/
private theorem integrand_tsum (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (t : ℝ) :
    logDeriv (DirichletCharacter.LFunction χ) (((2 : ℕ) : ℂ) + t * Complex.I) *
        gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) =
      ∑' n : ℕ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) := by
  set s : ℂ := ((2 : ℕ) : ℂ) + t * Complex.I with hsv
  have hs : 1 < s.re := by simp [s]
  have hx0 : (0 : ℝ) < x := by linarith
  have hterm : ∀ n : ℕ,
      LSeries.term ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
          fun n : ℕ => ((Λ n : ℝ) : ℂ)) s n =
        (χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
    intro n
    unfold LSeries.term
    by_cases hn : n = 0
    · simp [hn, wip_vonMangoldt_zero]
    · simp only [hn, if_false, Pi.mul_apply, div_eq_mul_inv]
      rw [← Complex.cpow_neg]
      try ring
  have hkey : logDeriv (DirichletCharacter.LFunction χ) s =
      ∑' n : ℕ, -((χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
    rw [logDeriv_LFunction_eq_series (q := q) χ hs]
    rw [show -LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
        fun n : ℕ => ((Λ n : ℝ) : ℂ)) s = -(∑' n : ℕ,
        (χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) from by
      unfold LSeries
      exact congrArg Neg.neg (tsum_congr hterm)]
    rw [← tsum_neg]
  rw [hkey, ← tsum_mul_right, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn, wip_vonMangoldt_zero]
  · have hnn : 0 < n := Nat.pos_of_ne_zero hn
    rw [show -((χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) *
          gaussianMellin δ s * (x : ℂ) ^ s =
        -(((χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ)) * gaussianMellin δ s *
          ((x : ℂ) ^ s * (n : ℂ) ^ (-s))) from by ring]
    rw [cpow_div_eq x hx0 n hnn s]
    ring

/-- LEAF. Step one, the Dirichlet series as a contour integral.  The weighted prime sum
`Schi` is minus the vertical integral at real part two of the logarithmic derivative of
the L-function times the shifted Gaussian transform times the scale factor.  The line at
real part two lies in the half plane of absolute convergence, no zero of the L-function
lies on it, and this step moves no contour: it only writes the sum as an integral. -/
theorem principal_prime_sum_mellin_contour (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    Schi etaHeart χ δ x =
      -((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hint : (∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) (((2 : ℕ) : ℂ) + t * Complex.I) *
        gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)) =
      -(2 * π * Schi etaHeart χ δ x) := by
    calc (∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) (((2 : ℕ) : ℂ) + t * Complex.I) *
          gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          (x : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))
        = ∫ t : ℝ, ∑' n : ℕ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) := by
          simp only [integrand_tsum x hx q χ δ]
      _ = ∑' n : ℕ, ∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) :=
          series_integral_swap x hx q χ δ
      _ = ∑' n : ℕ, -(2 * π * (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            ((etaHeart ((n : ℝ) / x) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))))) :=
          tsum_congr fun n => integral_summand x hx q χ δ n
      _ = -(2 * π * ∑' n : ℕ, (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            ((etaHeart ((n : ℝ) / x) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))))) := by
          rw [tsum_neg, tsum_mul_left]
      _ = -(2 * π * Schi etaHeart χ δ x) := by
          rw [show Schi etaHeart χ δ x = ∑' n : ℕ,
              (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
                ((etaHeart ((n : ℝ) / x) : ℂ) *
                  LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x)))) from by
            unfold Schi
            refine tsum_congr fun n => ?_
            have he : LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x)) =
                LeanLab.HelfgottArcs.e (δ * (n : ℝ) / x) := by
              congr 1
              ring
            rw [he]
            ring]
  simp only [Nat.cast_ofNat] at hint ⊢
  rw [hint]
  have h3 : -((1 / (2 * π) : ℂ) * -(2 * π * Schi etaHeart χ δ x)) =
      Schi etaHeart χ δ x := by
    have hpi : (2 * π : ℂ) ≠ 0 := by
      have h : (0 : ℝ) < 2 * π := by positivity
      exact_mod_cast ne_of_gt h
    field_simp
  rw [h3]

/-! ### F. The residue at one, for the contour shift of the second leaf -/

/-- The residue at the pole at one, written as the main term.  The Fourier transform of the
Gaussian weight at `-δ` is the Mellin transform of the shifted Gaussian at `1`, which is the
value the logarithmic derivative of zeta carries there: `logDeriv riemannZeta` has residue
`-1` at the simple pole `1` of zeta, so the residue of
`logDeriv * gaussianMellin δ · * x ^ ·` at `1` is minus this number times `x`.  This
identifies the main term `fhat etaHeart (-δ) * x` of the shifts in this file with a value of
`gaussianMellin`, so that leaf two's `- fhat etaHeart (-δ) * x` is the crossing of the pole
at one with the sign the downward shift gives.  At `δ = 0` it reads `sqrt (2 * π) / 2`,
which is `Gaussian123.fhat_etaHeart_zero`. -/
private theorem fhat_etaHeart_neg_eq_gaussianMellin_one (δ : ℝ) :
    fhat etaHeart (-δ) = gaussianMellin δ 1 := by
  have h1 : gaussianMellin δ 1 =
      ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * t) := by
    norm_num [gaussianMellin, mellin, smul_eq_mul]
  rw [h1, fhat, ← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioi (0 : ℝ))
    (f := fun y : ℝ => LeanLab.HelfgottArcs.e (-(y * -δ)) * (etaHeart y : ℂ)) ?_]
  · refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    dsimp only
    rw [show -(y * -δ) = δ * y by ring]
    simp only [etaHeart, if_pos hy0]
    ring
  · intro y hy
    have hy' : ¬ (0 < y) := by simpa using hy
    simp [etaHeart, hy']


/-- LEAF. Step four, the conductor one identification.  At conductor one the character is
the trivial one and its L-function is the Riemann zeta function, so the contour at real
part minus one half written with the L-function is literally the principal contour of the
target, which is written with the zeta function.  This step is a naming step: no contour
moves and no sum occurs. -/
theorem principal_contour_conductor_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : q = 1) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) =
      principalContour δ x := by
  subst hq
  unfold principalContour
  congr 1
  congr
  funext t
  congr 2
  have h_triv : χ = 1 := Subsingleton.elim χ 1
  rw [h_triv, DirichletCharacter.LFunction_modOne_eq]


end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

/-! ### The primitive `L`-function on the left of the critical strip (copied verbatim from
`LeanLab/Linnik/ExplicitFormula/LeftHalf.lean`, whose declarations are all lemmas and theorems;
`mult_zero_le_one` is omitted because it is the only one that names the `mult` of that file's
`Defs` and nothing here uses it). -/

namespace LeanLab.Linnik.ExplicitFormula

open Complex

lemma gf_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]; apply Gammaℝ_ne_zero_of_re_pos; simp; linarith

/-- Davenport ch. 9: `Λ(s, χ) = L(s, χ) γ(s, χ)` where the gamma factor is finite and nonzero. -/
lemma completed_eq_L_mul_gf {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : s ≠ 0 ∨ q ≠ 1) (hΓ : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DirichletCharacter.completedLFunction χ s =
      χ.LFunction s * DirichletCharacter.gammaFactor χ s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s h, div_mul_cancel₀ _ hΓ]

/-- elementary: a primitive character mod `q ≠ 1` is nontrivial. -/
lemma ne_one_of_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) : χ ≠ 1 := by
  intro h; apply hq
  rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hχ
  exact hχ.symm

/-- Davenport ch. 9: the root number of a primitive character is nonzero, from the functional
equation and `Λ(2, χ) ≠ 0`. -/
lemma rootNumber_ne_zero' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    DirichletCharacter.rootNumber χ ≠ 0 := by
  rcases eq_or_ne q 1 with rfl | hN
  · rw [DirichletCharacter.rootNumber_modOne]; exact one_ne_zero
  have hne := ne_one_of_primitive hχ hN
  intro hRoot
  have h := hχ.completedLFunction_one_sub (-1 : ℂ)
  rw [hRoot, mul_zero, zero_mul] at h
  have h2 : DirichletCharacter.completedLFunction χ (2 : ℂ) = 0 := by
    convert h using 2; ring
  have hΓ := gf_ne_zero_of_re_pos χ (s := 2) (by norm_num)
  rw [completed_eq_L_mul_gf χ (Or.inr hN) hΓ] at h2
  exact mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
    (by norm_num)) hΓ h2

/-- Davenport ch. 9: for primitive `χ`, `Λ(s, χ) ≠ 0` on `Re s ≤ 0`, by the functional equation
and the nonvanishing of `L(s, χ̄)` on `Re s ≥ 1`; the point `s = 0` needs `χ ≠ 1`. -/
lemma completed_ne_zero_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) (h : s ≠ 0 ∨ χ ≠ 1) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hfe := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  rw [hfe]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have h1 : 0 < (1 - s).re := by simp; linarith
  have h1' : 1 - s ≠ 0 := by intro e; rw [e] at h1; simp at h1
  have hΓ := gf_ne_zero_of_re_pos χ⁻¹ h1
  refine mul_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hq0)) (rootNumber_ne_zero' hχ)) ?_
  rw [completed_eq_L_mul_gf χ⁻¹ (Or.inl h1') hΓ]
  refine mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ ?_ (by simp; linarith))
    hΓ
  rcases h with h | h
  · right; intro e; apply h; linear_combination -e
  · left; exact inv_ne_one.mpr h

/-- Davenport ch. 9: the gamma factor is nonzero in `-1/2 ≤ Re s ≤ 0` away from `s = 0`. -/
lemma gf_ne_zero_left {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (hs : s ≠ 0) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · apply hs; simpa using hn
    · have := congrArg Complex.re hn
      simp at this
      have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      linarith
  · rw [hχ.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Davenport ch. 9 and 12: for primitive `χ`, a zero with `-1/2 ≤ Re ρ ≤ 0` is `ρ = 0`. -/
theorem zero_left_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : χ.LFunction ρ = 0) (h1 : -1 / 2 ≤ ρ.re) (h2 : ρ.re ≤ 0) : ρ = 0 := by
  by_contra hne
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hne)] at hρ
  exact div_ne_zero (completed_ne_zero_of_re_nonpos hχ h2 (Or.inl hne))
    (gf_ne_zero_left χ h1 hne) hρ

/-- No zero on the line `Re s = -1/2`. -/
theorem no_zero_left_line {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (t : ℝ) : χ.LFunction (-1 / 2 + t * I) ≠ 0 := by
  intro h
  have := zero_left_strip hχ h (by simp) (by simp; norm_num)
  have h' := congrArg Complex.re this
  simp at h'

/-- elementary: the gamma factor is differentiable wherever it is nonzero, since its inverse
is entire. -/
lemma gf_diff_of_ne {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with he | ho
  · have e : DirichletCharacter.gammaFactor χ = fun s => ((Gammaℝ s)⁻¹)⁻¹ := by
      funext s; rw [he.gammaFactor_def, inv_inv]
    rw [he.gammaFactor_def] at h
    rw [e]; exact (differentiable_Gammaℝ_inv s).inv (inv_ne_zero h)
  · have e : DirichletCharacter.gammaFactor χ = fun s => ((Gammaℝ (s + 1))⁻¹)⁻¹ := by
      funext s; rw [ho.gammaFactor_def, inv_inv]
    rw [ho.gammaFactor_def] at h
    rw [e]
    have hd : DifferentiableAt ℂ (fun s : ℂ => (Gammaℝ (s + 1))⁻¹) s :=
      DifferentiableAt.comp (g := fun s : ℂ => (Gammaℝ s)⁻¹) s (differentiable_Gammaℝ_inv _)
        (differentiableAt_id.add_const 1)
    exact hd.inv (inv_ne_zero h)

/-- Davenport ch. 9, the functional equation differentiated logarithmically on `Re s = -1/2`:
`L'/L(s, χ) = -log q - γ'/γ(1 - s, χ̄) - γ'/γ(s, χ) - L'/L(1 - s, χ̄)`, with `1 - s = 3/2 - it`. -/
theorem logDeriv_fe_left {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (t : ℝ) :
    deriv χ.LFunction (-1 / 2 + t * I) / χ.LFunction (-1 / 2 + t * I) =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (3 / 2 + (-t : ℝ) * I)
        - logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)
        - logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I) := by
  set s0 : ℂ := -1 / 2 + t * I with hs0
  have h1s : 1 - s0 = 3 / 2 + (-t : ℝ) * I := by rw [hs0]; push_cast; ring
  have hre0 : s0.re = -1 / 2 := by simp [hs0]
  have hs0ne : s0 ≠ 0 := by intro e; rw [e] at hre0; norm_num at hre0
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  set A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ * (q : ℂ) ^ ((1 - s) - 1 / 2) with hA
  set ref : ℂ → ℂ := fun s => 1 - s with href
  set B : ℂ → ℂ := DirichletCharacter.gammaFactor χ⁻¹ ∘ ref with hB
  set Cc : ℂ → ℂ := (χ⁻¹).LFunction ∘ ref with hCc
  have hev : χ.LFunction =ᶠ[nhds s0] A * B * Cc / DirichletCharacter.gammaFactor χ := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show s0.re < 0 by rw [hre0]; norm_num)] with s hs
    have hs : s.re < 0 := hs
    have hsne : s ≠ 0 := by intro e; rw [e] at hs; simp at hs
    have hr1 : 0 < (1 - s).re := by simp; linarith
    have h1ne : 1 - s ≠ 0 := by intro e; rw [e] at hr1; simp at hr1
    have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne), hfe,
      completed_eq_L_mul_gf χ⁻¹ (Or.inl h1ne) (gf_ne_zero_of_re_pos χ⁻¹ hr1)]
    simp only [Pi.mul_apply, Pi.div_apply, hA, hB, hCc, href, Function.comp_apply]
    ring
  have hr1 : 0 < (1 - s0).re := by rw [Complex.sub_re, Complex.one_re, hre0]; norm_num
  have hrefd : DifferentiableAt ℂ ref s0 := (differentiableAt_const _).sub differentiableAt_id
  have hderef : deriv ref s0 = -1 := by
    have hd : HasDerivAt ref (-1) s0 := by
      simpa using (hasDerivAt_id s0).const_sub (1 : ℂ)
    exact hd.deriv
  have hgfi := gf_ne_zero_of_re_pos χ⁻¹ hr1
  have hgfid : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ⁻¹) (ref s0) :=
    gf_diff_of_ne χ⁻¹ hgfi
  have hL1 : (1 - s0) ≠ 1 := by intro e; apply hs0ne; linear_combination -e
  have hLi : (χ⁻¹).LFunction (ref s0) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr hL1)
      (by show 1 ≤ (1 - s0).re; rw [Complex.sub_re, Complex.one_re, hre0]; norm_num)
  have hLid : DifferentiableAt ℂ (χ⁻¹).LFunction (ref s0) :=
    DirichletCharacter.differentiableAt_LFunction χ⁻¹ _ (Or.inl hL1)
  have hgf0 := gf_ne_zero_left χ (s := s0) (by rw [hre0]) hs0ne
  have hgf0d := gf_diff_of_ne χ hgf0
  have hAne : A s0 ≠ 0 := mul_ne_zero (rootNumber_ne_zero' hχ) (cpow_ne_zero_iff.mpr (Or.inl hq0))
  have hAd : HasDerivAt A (DirichletCharacter.rootNumber χ *
      ((q : ℂ) ^ ((1 - s0) - 1 / 2) * Complex.log q * (-1))) s0 := by
    have h1 : HasDerivAt (fun s : ℂ => (1 - s) - 1 / 2) (-1) s0 := by
      simpa using ((hasDerivAt_id s0).const_sub (1 : ℂ)).sub_const (1 / 2 : ℂ)
    exact (h1.const_cpow (Or.inl hq0)).const_mul _
  have hBne : B s0 ≠ 0 := hgfi
  have hCne : Cc s0 ≠ 0 := hLi
  have hBd : DifferentiableAt ℂ B s0 := hgfid.comp s0 hrefd
  have hCd : DifferentiableAt ℂ Cc s0 := hLid.comp s0 hrefd
  have hlogA : logDeriv A s0 = -(Real.log q : ℂ) := by
    rw [logDeriv_apply, hAd.deriv, Complex.natCast_log]
    simp only [hA]
    have hc : (q : ℂ) ^ ((1 - s0) - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hq0)
    rw [div_eq_iff (mul_ne_zero (rootNumber_ne_zero' hχ) hc)]
    ring
  rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_div (f := A * B * Cc) (g := DirichletCharacter.gammaFactor χ) s0 (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
      ((hAd.differentiableAt.mul hBd).mul hCd) hgf0d,
    logDeriv_mul (f := A * B) (g := Cc) s0 (mul_ne_zero hAne hBne) hCne (hAd.differentiableAt.mul hBd) hCd,
    logDeriv_mul (f := A) (g := B) s0 hAne hBne hAd.differentiableAt hBd, hlogA,
    hB, hCc, logDeriv_comp hgfid hrefd, logDeriv_comp hLid hrefd, hderef]
  simp only [href, h1s]
  ring

/-- Davenport ch. 16: `|L'/L(3/2 + it, χ)| ≤ -ζ'/ζ(3/2) = Σ Λ(n) n^(-3/2)`, uniformly in `χ`. -/
theorem logDeriv_L_three_half_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ), ‖logDeriv χ.LFunction (3 / 2 + t * I)‖ ≤ C := by
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsumN : Summable fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.mpr hsum
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun q _ χ t => ?_⟩
  set s : ℂ := 3 / 2 + t * I with hs
  have hre : 1 < s.re := by simp [hs]; norm_num
  have hconv : -deriv χ.LFunction s / χ.LFunction s =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
    convert h.symm using 3
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  have hpt : ∀ n, ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · exact le_rfl
    · have hsr : s.re = (3 / 2 : ℂ).re := by simp [hs]
      rw [hsr]
      gcongr
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum2 : Summable fun n =>
      ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumN
  rw [logDeriv_apply, ← norm_neg, ← neg_div, hconv, LSeries]
  exact (norm_tsum_le_tsum_norm hsum2).trans (hsum2.tsum_le_tsum hpt hsumN)

/-- Davenport ch. 10: `Γℝ'/Γℝ(s) = -(log π)/2 + ψ(s/2)/2` away from the poles. -/
lemma logDeriv_Gammaℝ {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    logDeriv Gammaℝ s = -(Complex.log (Real.pi : ℂ)) / 2 + digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hP : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have h1 : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const (2 : ℂ)
    exact h1.const_cpow (Or.inl hpi)
  have hPne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hh : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const 2
  have hGd : DifferentiableAt ℂ Gamma (s / 2) := differentiableAt_Gamma _ hs
  have hGne : Gamma (s / 2) ≠ 0 := Gamma_ne_zero hs
  have e : Gammaℝ = (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) * (Gamma ∘ fun s : ℂ => s / 2) := by
    funext s; simp [Gammaℝ_def]
  have hdh : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
    have : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℂ)
    exact this.deriv
  rw [e, logDeriv_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) (g := Gamma ∘ fun s : ℂ => s / 2)
    s hPne hGne hP.differentiableAt (hGd.comp s hh), logDeriv_comp (f := Gamma) (g := fun s : ℂ => s / 2) hGd hh, hdh, logDeriv_apply,
    hP.deriv, ← digamma_def]
  field_simp

/-- elementary: `ψ(conj z) = conj ψ(z)`, from `Γ(conj z) = conj Γ(z)`. -/
lemma digamma_conj' (z : ℂ) : digamma (starRingEnd ℂ z) = starRingEnd ℂ (digamma z) := by
  have hG : (starRingEnd ℂ ∘ Gamma ∘ starRingEnd ℂ) = Gamma := by
    funext w; simp [Function.comp, Gamma_conj]
  have h1 := congrFun (deriv_conj_conj (f := Gamma)) z
  rw [hG] at h1
  simp only [Function.comp_apply] at h1
  have hd : deriv Gamma (starRingEnd ℂ z) = starRingEnd ℂ (deriv Gamma z) := by
    rw [h1, Complex.conj_conj]
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hd, Gamma_conj, map_div₀]

/-- elementary: the four lines avoid the poles of `Γ`, in the open strip `|Re z - σ| < 1/8`. -/
lemma not_pole_of_near {σ : ℝ} (hσ : σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) {z : ℂ}
    (hz : |z.re - σ| < 1 / 8) : ∀ m : ℕ, z ≠ -m := by
  intro m hm
  rw [hm] at hz
  simp at hz
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_lt] at hz
  rcases hσ with h | h | h | h <;> rw [h] at hz
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; norm_num at hz
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
      linarith [hz.1, hz.2]
  all_goals linarith [hz.1, hz.2]

/-- elementary, by compactness: `ψ` is bounded on the segment `σ + iu`, `|u| ≤ 1`. -/
lemma digamma_bdd_segment {σ : ℝ} (hσ : σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) :
    ∃ M : ℝ, ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖digamma ((σ : ℂ) + u * I)‖ ≤ M := by
  set U : Set ℂ := {z | |z.re - σ| < 1 / 8} with hU
  have hUo : IsOpen U :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
  have hd : DifferentiableOn ℂ Gamma U := fun z hz =>
    (differentiableAt_Gamma z (not_pole_of_near hσ hz)).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv Gamma) U := hd.deriv hUo
  have hcont : ∀ z ∈ U, ContinuousAt digamma z := by
    intro z hz
    have e : digamma = fun w => deriv Gamma w / Gamma w := by
      funext w; rw [digamma_def, logDeriv_apply]
    rw [e]
    exact ((hdd.differentiableAt (hUo.mem_nhds hz)).continuousAt).div
      ((hd.differentiableAt (hUo.mem_nhds hz)).continuousAt)
      (Gamma_ne_zero (not_pole_of_near hσ hz))
  have hcon : ContinuousOn (fun u : ℝ => digamma ((σ : ℂ) + u * I)) (Set.Icc (-1 : ℝ) 1) := by
    intro u _
    have hm : (σ : ℂ) + u * I ∈ U := by simp [hU]
    have hl : Continuous fun u : ℝ => (σ : ℂ) + u * I := by fun_prop
    exact (ContinuousAt.comp (f := fun u : ℝ => (σ : ℂ) + u * I) (hcont _ hm)
      hl.continuousAt).continuousWithinAt
  exact isCompact_Icc.exists_bound_of_continuousOn hcon

/-- Davenport ch. 10, Stirling, on one of the four lines. -/
lemma digamma_line_bound {σ : ℝ} (hσ : σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 2) := by
  obtain ⟨Ks, hKs, hst⟩ := LeanLab.PNTPort.ZetaZeros.digamma_strip
  obtain ⟨M, hM⟩ := digamma_bdd_segment hσ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hσ1 : -1 ≤ σ ∧ σ ≤ 2 := by
    rcases hσ with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  set K := max M 0 / Real.log 2 + 2 * Ks + 2 / Real.log 2 with hK
  refine ⟨K, by positivity, ?_⟩
  have pos : ∀ u : ℝ, 1 ≤ u → ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 2) := by
    intro u hu
    have h := hst u hu σ hσ1.1 hσ1.2
    rw [abs_of_nonneg (by linarith)]
    have hl : Real.log 2 ≤ Real.log (u + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h3 : Real.log (u + 3) ≤ 2 * Real.log (u + 2) := by
      rw [show 2 * Real.log (u + 2) = Real.log ((u + 2) ^ 2) by rw [Real.log_pow]; norm_num]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h2 : 2 ≤ 2 / Real.log 2 * Real.log (u + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
    have hM0 : 0 ≤ max M 0 / Real.log 2 * Real.log (u + 2) :=
      mul_nonneg (by positivity) (hl2.le.trans hl)
    calc _ ≤ Ks * Real.log (u + 3) + 2 := h
      _ ≤ Ks * (2 * Real.log (u + 2)) + 2 / Real.log 2 * Real.log (u + 2) := by gcongr
      _ ≤ K * Real.log (u + 2) := by rw [hK]; nlinarith
  intro u
  rcases le_or_gt 1 u with hu | hu
  · exact pos u hu
  rcases le_or_gt u (-1) with hu' | hu'
  · have e : (σ : ℂ) + u * I = starRingEnd ℂ ((σ : ℂ) + ((-u : ℝ) : ℂ) * I) := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [e, digamma_conj', Complex.norm_conj]
    have := pos (-u) (by linarith)
    rwa [abs_neg] at this
  · have hm := hM u ⟨hu'.le, hu.le⟩
    have hl : Real.log 2 ≤ Real.log (|u| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg u])
    have h1 : max M 0 ≤ max M 0 / Real.log 2 * Real.log (|u| + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hl (le_max_right _ _)
    have hL0 : 0 ≤ Real.log (|u| + 2) := hl2.le.trans hl
    have h2 : 0 ≤ (2 * Ks + 2 / Real.log 2) * Real.log (|u| + 2) := by positivity
    calc _ ≤ max M 0 := hm.trans (le_max_left _ _)
      _ ≤ K * Real.log (|u| + 2) := by rw [hK]; nlinarith

/-- Davenport ch. 10, Stirling: `|ψ(σ + iu)| ≤ K log(|u| + 2)` on the four vertical lines
`σ = -1/4, 1/4, 3/4, 5/4`, which avoid the poles of `ψ`. -/
theorem digamma_vert_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ,
    (σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) → ∀ u : ℝ,
      ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 2) := by
  obtain ⟨K1, h1, b1⟩ := digamma_line_bound (σ := -1 / 4) (Or.inl rfl)
  obtain ⟨K2, h2, b2⟩ := digamma_line_bound (σ := 1 / 4) (Or.inr (Or.inl rfl))
  obtain ⟨K3, h3, b3⟩ := digamma_line_bound (σ := 3 / 4) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨K4, h4, b4⟩ := digamma_line_bound (σ := 5 / 4) (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨K1 + K2 + K3 + K4, by positivity, fun σ hσ u => ?_⟩
  have hL : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
  rcases hσ with rfl | rfl | rfl | rfl
  · exact (b1 u).trans (by nlinarith)
  · exact (b2 u).trans (by nlinarith)
  · exact (b3 u).trans (by nlinarith)
  · exact (b4 u).trans (by nlinarith)

/-- Davenport ch. 10 and 16, Stirling for the digamma function: the log derivative of the gamma
factor at `Re s = -1/2` and at `Re s = 3/2` is `O(log(|t| + 2))`, uniformly in `χ`. -/
theorem logDeriv_gf_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    ‖logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖ ≤ C * Real.log (|t| + 2) ∧
    ‖logDeriv (DirichletCharacter.gammaFactor χ) (3 / 2 + t * I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨K, hK, hb⟩ := digamma_vert_bound
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  refine ⟨2 / Real.log 2 + K, by positivity, fun q χ t => ?_⟩
  have ht2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hhalf : Real.log (|t / 2| + 2) ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  -- the generic estimate at a point `w` with `w/2 = σ + i t/2`
  have key : ∀ w : ℂ, ∀ σ : ℝ, (σ = -1 / 4 ∨ σ = 1 / 4 ∨ σ = 3 / 4 ∨ σ = 5 / 4) →
      w / 2 = (σ : ℂ) + ((t / 2 : ℝ) : ℂ) * I →
      ‖logDeriv Gammaℝ w‖ ≤ (2 / Real.log 2 + K) * Real.log (|t| + 2) := by
    intro w σ hσ hw
    have hnp : ∀ m : ℕ, w / 2 ≠ -m := by
      intro m hm
      have := congrArg Complex.re (hw.symm.trans hm)
      simp at this
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rcases hσ with h | h | h | h <;> rw [h] at this
      · have : (m : ℝ) = 1 / 4 := by linarith
        have h4 : (4 * m : ℝ) = 1 := by linarith
        have : 4 * m = 1 := by exact_mod_cast h4
        omega
      all_goals linarith
    rw [logDeriv_Gammaℝ hnp, hw]
    have hd := hb σ hσ (t / 2)
    calc _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖digamma ((σ : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖ :=
          norm_add_le _ _
      _ ≤ 3 / 2 + K * Real.log (|t| + 2) / 2 := by
          rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
          gcongr
          exact hd.trans (mul_le_mul_of_nonneg_left hhalf hK)
      _ ≤ (2 / Real.log 2 + K) * Real.log (|t| + 2) := by
          have h1 : 2 ≤ 2 / Real.log 2 * Real.log (|t| + 2) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
          have h0 : 0 ≤ K * Real.log (|t| + 2) :=
            mul_nonneg hK (le_trans hl2.le ht2)
          nlinarith
  rcases χ.even_or_odd with he | ho
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [e]
    refine ⟨key _ (-1 / 4) (Or.inl rfl) ?_, key _ (3 / 4) (Or.inr (Or.inr (Or.inl rfl))) ?_⟩ <;>
      push_cast <;> ring
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ ∘ fun s => s + 1 :=
      funext ho.gammaFactor_def
    have hGd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Gammaℝ z := fun z hz => by
      have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) z :=
        (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
      simpa only [inv_inv] using h
    have hcomp : ∀ w : ℂ, 0 < (w + 1).re → logDeriv (DirichletCharacter.gammaFactor χ) w =
        logDeriv Gammaℝ (w + 1) := by
      intro w hw
      rw [e, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + 1) (hGd _ hw)
        (differentiableAt_id.add_const 1)]
      simp
    refine ⟨?_, ?_⟩
    · rw [hcomp _ (by simp; norm_num)]
      exact key _ (1 / 4) (Or.inr (Or.inl rfl)) (by push_cast; ring)
    · rw [hcomp _ (by simp; norm_num)]
      exact key _ (5 / 4) (Or.inr (Or.inr (Or.inr rfl))) (by push_cast; ring)

/-- Davenport ch. 16 via the functional equation: `|L'/L(-1/2 + it, χ)| ≤ C log(q(|t| + 2))`,
uniformly in the primitive character. -/
theorem logDeriv_left_line : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ t : ℝ,
      ‖deriv χ.LFunction (-1 / 2 + t * I) / χ.LFunction (-1 / 2 + t * I)‖ ≤
        C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C2, hC2, h2⟩ := logDeriv_L_three_half_le
  obtain ⟨C3, hC3, h3⟩ := logDeriv_gf_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 2 * C3 + C2 / Real.log 2, by positivity, fun q _ χ hχ t => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  set L := Real.log (q * (|t| + 2)) with hL
  have hlq : Real.log q ≤ L := Real.log_le_log (by linarith) (by nlinarith)
  have hlt : Real.log (|t| + 2) ≤ L := Real.log_le_log (by linarith) (by nlinarith)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [logDeriv_fe_left hχ t]
  have e1 : ‖(Real.log q : ℂ)‖ = Real.log q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlq0]
  have a1 := (h3 q χ⁻¹ (-t)).2
  have a2 := (h3 q χ t).1
  have a3 := h2 q χ⁻¹ (-t)
  rw [abs_neg] at a1
  have hC2L : C2 ≤ C2 / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; exact mul_le_mul_of_nonneg_left hL2 hC2
  calc _ ≤ ‖-(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (3 / 2 + (-t : ℝ) * I) - logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖
          + ‖logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I)‖ := norm_sub_le _ _
    _ ≤ ‖-(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (3 / 2 + (-t : ℝ) * I)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖
          + ‖logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ ‖-(Real.log q : ℂ)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (3 / 2 + (-t : ℝ) * I)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ) (-1 / 2 + t * I)‖
          + ‖logDeriv (χ⁻¹).LFunction (3 / 2 + (-t : ℝ) * I)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.log q + C3 * Real.log (|t| + 2) + C3 * Real.log (|t| + 2) + C2 := by
        rw [norm_neg, e1]; gcongr
    _ ≤ L + C3 * L + C3 * L + C2 / Real.log 2 * L := by gcongr
    _ = (1 + 2 * C3 + C2 / Real.log 2) * L := by ring

end LeanLab.Linnik.ExplicitFormula

namespace LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

open scoped ArithmeticFunction

/-! ### The contour shift of the second leaf (copied verbatim from
`LeanLab/HelfgottMajor/SPLIT_principal_contour_shift_two_to_minus_half.lean`, which imports the
file it restates and so cannot be imported back). -/


/-! ### A. The line of real part two is the prime sum -/

/-- LEAF. Step one, the line of real part two.  The vertical integral at real part two of
the logarithmic derivative of the `L`-function against the shifted Gaussian transform and
the scale factor is minus the twisted von Mangoldt sum.  The line lies in the half plane of
absolute convergence, no zero of the `L`-function lies on it, and this step moves no
contour: it only writes the prime sum as an integral.  It says nothing about the line of
real part minus one half, about log of two pi, or about either zero sum.  It is the
negation of `principal_prime_sum_mellin_contour` of the imported file, which is already
proved there, and the repair pass takes it from that theorem. -/
theorem principal_two_line_prime_sum (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) = - Schi etaHeart χ δ x := by
  rw [principal_prime_sum_mellin_contour x hx q χ δ]
  ring

/-! ### C. The line of real part minus one half at conductor one -/

/-- LEAF. Step three, the conductor one identification.  At conductor one the character is
the trivial one and its `L`-function is the Riemann zeta function, so the vertical integral
at real part minus one half of the logarithmic derivative against the continued Gaussian
transform and the scale factor is literally the principal contour of the target.  This is a
naming step: no contour moves and no sum occurs.  It is the theorem
`principal_contour_conductor_one` of the imported file restated with the binders in the
order this assembly uses, and the repair pass takes it from that theorem. -/
theorem principal_half_line_conductor_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) = principalContour δ x := by
  exact principal_contour_conductor_one x hx q χ hq δ


/-! #### A0. The Gaussian Mellin transform decays on every vertical line of real part at
least one half -/

/-- A uniform bound for the Gaussian Mellin transform on a fixed vertical line. -/
private theorem pcst_mellin_line_constant (δ σ : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0 : ℝ), x ^ (σ - 1) * exp (-x ^ 2 / 2)) + 1, ?_, ?_⟩
  · have h0 : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), x ^ (σ - 1) * exp (-x ^ 2 / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun x hx =>
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
    linarith
  · intro t
    have h := Gaussian269.mellin_norm_le δ ((σ : ℂ) + t * Complex.I)
    have hre : ((σ : ℂ) + t * Complex.I).re = σ := by simp
    rw [hre] at h
    linarith

/-- One recurrence step for the Gaussian Mellin transform, in norm form. -/
private theorem pcst_mellin_step (δ : ℝ) (u : ℂ) (hu : 0 < u.re) :
    ‖gaussianMellin δ u‖ * ‖u‖ ≤
      ‖gaussianMellin δ (u + 2)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖gaussianMellin δ (u + 1)‖ := by
  have h := Continuation457.gaussian_mellin_recurrence δ u hu
  calc ‖gaussianMellin δ u‖ * ‖u‖ = ‖u * gaussianMellin δ u‖ := by rw [norm_mul, mul_comm]
    _ = ‖gaussianMellin δ (u + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (u + 1)‖ := by
        rw [h]
    _ ≤ ‖gaussianMellin δ (u + 2)‖ +
          ‖(2 * π * Complex.I * δ) * gaussianMellin δ (u + 1)‖ := norm_sub_le _ _
    _ = ‖gaussianMellin δ (u + 2)‖ +
          ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖gaussianMellin δ (u + 1)‖ := by rw [norm_mul]

/-- Three recurrence steps give quadratic decay of the Gaussian Mellin transform on every
vertical line of real part at least one half. -/
private theorem pcst_mellin_decay_half (δ σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨B2, hB2, hB2'⟩ := pcst_mellin_line_constant δ (σ + 2)
  obtain ⟨B3, hB3, hB3'⟩ := pcst_mellin_line_constant δ (σ + 3)
  obtain ⟨B4, hB4, hB4'⟩ := pcst_mellin_line_constant δ (σ + 4)
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hP : 0 ≤ B4 + c * B3 + c * (B3 + c * B2) := by
    have h1 : 0 ≤ c * B3 := mul_nonneg hc0 hB3.le
    have h2 : 0 ≤ c * (B3 + c * B2) :=
      mul_nonneg hc0 (by have := mul_nonneg hc0 hB2.le; linarith)
    linarith
  refine ⟨4 * (B4 + c * B3 + c * (B3 + c * B2)) + 1, by linarith, fun t => ?_⟩
  set a : ℂ := (σ : ℂ) + t * Complex.I with ha
  have hare : a.re = σ := by rw [ha]; simp
  have ha2 : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : a.re = σ := hare
    have h2 : a.im = t := by rw [ha]; simp
    rw [h1, h2]
    nlinarith
  have hb2 : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : (a + 1).re = σ + 1 := by rw [ha]; simp
    have h2 : (a + 1).im = t := by rw [ha]; simp
    rw [h1, h2]
    nlinarith
  have hquarter : (0 : ℝ) < (1 / 4 : ℝ) + t ^ 2 := by positivity
  have hapos : 0 < ‖a‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : a.re = 0 := by rw [h]; simp
    rw [hare] at h1
    linarith
  have hbpos : 0 < ‖a + 1‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (a + 1).re = 0 := by rw [h]; simp
    have h2 : (a + 1).re = σ + 1 := by rw [ha]; simp
    rw [h2] at h1
    linarith
  have ha1 : 0 < (a + 1).re := by rw [ha]; simp; linarith
  have ha2' : 0 < (a + 2).re := by rw [ha]; simp; linarith
  have hstep1 := pcst_mellin_step δ a (by rw [hare]; linarith)
  have hstep2 := pcst_mellin_step δ (a + 1) ha1
  have hstep3 := pcst_mellin_step δ (a + 2) ha2'
  have e2 : a + 2 = ((σ + 2 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have e3 : a + 3 = ((σ + 3 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have e4 : a + 4 = ((σ + 4 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have h3 : ‖gaussianMellin δ (a + 2)‖ * ‖a + 2‖ ≤ B4 + c * B3 := by
    have hb : ‖gaussianMellin δ ((a + 2) + 2)‖ ≤ B4 := by
      rw [show (a + 2) + 2 = a + 4 by ring, e4]; exact hB4' t
    have hc1 : ‖gaussianMellin δ ((a + 2) + 1)‖ ≤ B3 := by
      rw [show (a + 2) + 1 = a + 3 by ring, e3]; exact hB3' t
    calc ‖gaussianMellin δ (a + 2)‖ * ‖a + 2‖
        ≤ ‖gaussianMellin δ ((a + 2) + 2)‖ + c * ‖gaussianMellin δ ((a + 2) + 1)‖ := hstep3
      _ ≤ B4 + c * B3 := by
          refine add_le_add hb (mul_le_mul_of_nonneg_left hc1 hc0)
  have h2 : ‖gaussianMellin δ (a + 1)‖ * ‖a + 1‖ ≤ B3 + c * B2 := by
    have hb : ‖gaussianMellin δ ((a + 1) + 2)‖ ≤ B3 := by
      rw [show (a + 1) + 2 = a + 3 by ring, e3]; exact hB3' t
    have hc1 : ‖gaussianMellin δ ((a + 1) + 1)‖ ≤ B2 := by
      rw [show (a + 1) + 1 = a + 2 by ring, e2]; exact hB2' t
    calc ‖gaussianMellin δ (a + 1)‖ * ‖a + 1‖
        ≤ ‖gaussianMellin δ ((a + 1) + 2)‖ + c * ‖gaussianMellin δ ((a + 1) + 1)‖ := hstep2
      _ ≤ B3 + c * B2 := by
          refine add_le_add hb (mul_le_mul_of_nonneg_left hc1 hc0)
  have h2pos : 0 < ‖a + 2‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (a + 2).re = 0 := by rw [h]; simp
    linarith
  have hquot2 : ‖gaussianMellin δ (a + 2)‖ ≤ (B4 + c * B3) / ‖a + 2‖ := by
    rw [le_div_iff₀ h2pos]
    linarith [h3]
  have hquot1 : ‖gaussianMellin δ (a + 1)‖ ≤ (B3 + c * B2) / ‖a + 1‖ := by
    rw [le_div_iff₀ hbpos]
    linarith [h2]
  have hle : ‖a + 1‖ ≤ ‖a + 2‖ := by
    have hn1 : Complex.normSq (a + 1) = (σ + 1) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply]
      have h1 : (a + 1).re = σ + 1 := by rw [ha]; simp
      have h2 : (a + 1).im = t := by rw [ha]; simp
      rw [h1, h2]; ring
    have hn2 : Complex.normSq (a + 2) = (σ + 2) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply]
      have h1 : (a + 2).re = σ + 2 := by rw [ha]; simp
      have h2 : (a + 2).im = t := by rw [ha]; simp
      rw [h1, h2]; ring
    rw [show ‖a + 1‖ = Real.sqrt (Complex.normSq (a + 1)) by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
      show ‖a + 2‖ = Real.sqrt (Complex.normSq (a + 2)) by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
    apply Real.sqrt_le_sqrt
    rw [hn1, hn2]
    nlinarith
  have hsum : ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖ ≤
      B4 + c * B3 + c * (B3 + c * B2) := by
    have hb1 : (B4 + c * B3) / ‖a + 2‖ ≤ (B4 + c * B3) / ‖a + 1‖ := by
      have hnum : (0 : ℝ) ≤ B4 + c * B3 := by
        have := mul_nonneg hc0 hB3.le; linarith [hB4.le]
      exact div_le_div_of_nonneg_left hnum hbpos hle
    have hmid : ‖gaussianMellin δ a‖ * ‖a‖ ≤
        (B4 + c * B3 + c * (B3 + c * B2)) / ‖a + 1‖ := by
      have hb2' : c * ((B3 + c * B2) / ‖a + 1‖) = c * (B3 + c * B2) / ‖a + 1‖ := by ring
      calc ‖gaussianMellin δ a‖ * ‖a‖
          ≤ ‖gaussianMellin δ (a + 2)‖ + c * ‖gaussianMellin δ (a + 1)‖ := hstep1
        _ ≤ (B4 + c * B3) / ‖a + 2‖ + c * ((B3 + c * B2) / ‖a + 1‖) := by
            refine add_le_add hquot2 (mul_le_mul_of_nonneg_left hquot1 hc0)
        _ ≤ (B4 + c * B3) / ‖a + 1‖ + c * (B3 + c * B2) / ‖a + 1‖ := by
            rw [hb2']
            exact add_le_add hb1 le_rfl
        _ = (B4 + c * B3 + c * (B3 + c * B2)) / ‖a + 1‖ := by ring
    calc ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖
        ≤ ((B4 + c * B3 + c * (B3 + c * B2)) / ‖a + 1‖) * ‖a + 1‖ :=
          mul_le_mul_of_nonneg_right hmid hbpos.le
      _ = B4 + c * B3 + c * (B3 + c * B2) := by field_simp
  have hmain : ‖gaussianMellin δ a‖ ≤
      (B4 + c * B3 + c * (B3 + c * B2)) / (‖a‖ * ‖a + 1‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖a‖ * ‖a + 1‖)]
    calc ‖gaussianMellin δ a‖ * (‖a‖ * ‖a + 1‖) =
        ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖ := by ring
      _ ≤ _ := hsum
  have hden : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a‖ * ‖a + 1‖ := by
    have h1 : 0 ≤ ‖a‖ := norm_nonneg _
    have h2 : 0 ≤ ‖a + 1‖ := norm_nonneg _
    nlinarith [ha2, hb2]
  have hfin : ‖gaussianMellin δ a‖ ≤
      (B4 + c * B3 + c * (B3 + c * B2)) / ((1 / 4 : ℝ) + t ^ 2) :=
    hmain.trans (div_le_div_of_nonneg_left hP hquarter hden)
  have hfour : (B4 + c * B3 + c * (B3 + c * B2)) / ((1 / 4 : ℝ) + t ^ 2) ≤
      (4 * (B4 + c * B3 + c * (B3 + c * B2)) + 1) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hquarter (by positivity : (0 : ℝ) < 1 + t ^ 2)]
    nlinarith [hP]
  simpa [ha] using hfin.trans hfour

/-- The continued Gaussian transform decays quadratically on the line of real part minus one
half. -/
private theorem pcst_continuedGaussian_decay (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨K1, hK1, hK1'⟩ := pcst_mellin_decay_half δ (1 / 2) le_rfl
  obtain ⟨K2, hK2, hK2'⟩ := pcst_mellin_decay_half δ (3 / 2) (by norm_num)
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hP : 0 ≤ K2 + c * K1 := by
    have h := mul_nonneg hc0 hK1.le
    linarith [hK2.le]
  refine ⟨2 * (K2 + c * K1) + 1, by linarith, fun t => ?_⟩
  set s : ℂ := (-1 / 2 : ℂ) + t * Complex.I with hs
  have hsre : s.re = -1 / 2 := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hsq : ‖s‖ ^ 2 = (1 / 4 : ℝ) + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hsre, hsim]
    ring
  have h2 : (1 / 2 : ℝ) ≤ ‖s‖ := by
    have h0 : 0 ≤ ‖s‖ := norm_nonneg _
    nlinarith [sq_nonneg t]
  have hun : continuedGaussian δ s =
      (gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) / s :=
    rfl
  have e1 : s + 1 = ((1 / 2 : ℝ) : ℂ) + t * Complex.I := by rw [hs]; push_cast; ring
  have e2 : s + 2 = ((3 / 2 : ℝ) : ℂ) + t * Complex.I := by rw [hs]; push_cast; ring
  have hden1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hb1 : ‖gaussianMellin δ (s + 1)‖ ≤ K1 / (1 + t ^ 2) := by rw [e1]; exact hK1' t
  have hb2v : ‖gaussianMellin δ (s + 2)‖ ≤ K2 / (1 + t ^ 2) := by rw [e2]; exact hK2' t
  have hnum : ‖gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ ≤
      (K2 + c * K1) / (1 + t ^ 2) := by
    calc ‖gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖
        ≤ ‖gaussianMellin δ (s + 2)‖ +
            ‖(2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
      _ = ‖gaussianMellin δ (s + 2)‖ + c * ‖gaussianMellin δ (s + 1)‖ := by rw [norm_mul, hc]
      _ ≤ K2 / (1 + t ^ 2) + c * (K1 / (1 + t ^ 2)) := by
          refine add_le_add hb2v (mul_le_mul_of_nonneg_left hb1 hc0)
      _ = (K2 + c * K1) / (1 + t ^ 2) := by ring
  have hmul : ‖continuedGaussian δ s‖ ≤ ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) := by
    rw [hun, norm_div]
    have hstep1 : ‖gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ / ‖s‖ ≤
        ‖gaussianMellin δ (s + 2) -
          (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) h2
    have hstep2 : ‖gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ / (1 / 2) ≤
        ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) :=
      div_le_div_of_nonneg_right hnum (by norm_num)
    exact hstep1.trans hstep2
  have hfin : ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) ≤
      (2 * (K2 + c * K1) + 1) / (1 + t ^ 2) := by
    have he : ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) =
        2 * (K2 + c * K1) / (1 + t ^ 2) := by field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ hden1.le
    linarith
  simpa [hs] using hmul.trans hfin

/-! #### A1. The logarithmic derivative of the L-function on the line of real part minus
one half, for every Dirichlet character -/

/-- The cast of a natural number to the complexes, through the reals. -/
private theorem pcst_natCast_eq_ofReal (b : ℕ) : ((b : ℂ)) = ((b : ℝ) : ℂ) := by
  push_cast
  ring

/-- A Dirichlet character has unit modulus on units. -/
private theorem pcst_norm_apply_eq_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {a : ZMod d} (ha : IsUnit a) : ‖χ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have hmul : ‖χ (u : ZMod d)‖ * ‖χ (((u⁻¹ : (ZMod d)ˣ) : ZMod d))‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h1 := DirichletCharacter.norm_le_one (χ := χ) (((u⁻¹ : (ZMod d)ˣ) : ZMod d))
  have h2 := DirichletCharacter.norm_le_one (χ := χ) (u : ZMod d)
  nlinarith [norm_nonneg (χ (u : ZMod d)),
    norm_nonneg (χ (((u⁻¹ : (ZMod d)ˣ) : ZMod d)))]

/-- The L-function of a Dirichlet character is analytic away from one. -/
private theorem pcst_analyticAt_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) :=
    fun z hz =>
      (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_compl_singleton s (by simpa using hs)

/-- The primitive factorisation of the L-function: a character is a primitive one times a
finite Euler product over the primes of its level. -/
private theorem pcst_LFunction_factorization {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero (DirichletCharacter.conductor χ)] {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.LFunction χ.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-s)) := by
  have h := DirichletCharacter.LFunction_changeLevel (M := DirichletCharacter.conductor χ)
    (N := q) (DirichletCharacter.conductor_dvd_level χ) (χ := χ.primitiveCharacter) (Or.inr hs)
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  simpa only [pcst_natCast_eq_ofReal] using h

/-- No Euler factor vanishes on the line of real part minus one half. -/
private theorem pcst_prime_factor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero (DirichletCharacter.conductor χ)]
    (p : ℕ) (hp : p ∈ q.primeFactors) {s : ℂ} (hre : s.re = -1 / 2) :
    1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
      ((p : ℝ) : ℂ) ^ (-s) ≠ 0 := by
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have hre' : (-s).re = 1 / 2 := by
      rw [Complex.neg_re, hre]
      norm_num
    rw [hre']
  have hsqrt : (1 : ℝ) < (p : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) < (p : ℝ))
      (by norm_num : (0 : ℝ) < 1 / 2)
    rwa [Real.one_rpow] at h1
  rintro h
  have hz : χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
      ((p : ℝ) : ℂ) ^ (-s) = 1 := by
    linear_combination -h
  rcases eq_or_ne (χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ))) 0 with hc | hc
  · rw [hc, zero_mul] at hz
    exact zero_ne_one hz
  · have hunit : IsUnit (p : ZMod (DirichletCharacter.conductor χ)) := by
      by_contra hnu
      exact hc (MulChar.map_nonunit χ.primitiveCharacter hnu)
    have hc1 : ‖χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ))‖ = 1 :=
      pcst_norm_apply_eq_one χ.primitiveCharacter hunit
    have h2 := congrArg norm hz
    rw [norm_one, norm_mul, hc1, hnorm, one_mul] at h2
    linarith

/-- `z ↦ b ^ (-z)` differentiates to `-log b * b ^ (-z)`. -/
private theorem pcst_hasDerivAt_cpow_neg (b : ℝ) (hb : 0 < b) (w : ℂ) :
    HasDerivAt (fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z))
      (-(Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-w)) w := by
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have heq : ∀ z : ℂ, Complex.exp (Complex.log ((b : ℝ) : ℂ) * (-z)) =
      ((b : ℝ) : ℂ) ^ (-z) := by
    intro z
    rw [Complex.cpow_def_of_ne_zero hbC]
  have hinner : HasDerivAt (fun z : ℂ => Complex.log ((b : ℝ) : ℂ) * (-z))
      (Complex.log ((b : ℝ) : ℂ) * (-1)) w := by
    simpa using (hasDerivAt_id w).neg.const_mul (Complex.log ((b : ℝ) : ℂ))
  have hexp := hinner.cexp
  rw [show (fun z : ℂ => Complex.exp (Complex.log ((b : ℝ) : ℂ) * (-z)))
      = fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z) from funext heq] at hexp
  refine hexp.congr_deriv ?_
  rw [← heq w, ← Complex.ofReal_log hb.le]
  ring

/-- The logarithmic derivative of one Euler factor. -/
private theorem pcst_factor_logDeriv (b : ℝ) (hb : 0 < b) (c : ℂ) (s : ℂ) :
    logDeriv (fun z : ℂ => 1 - c * ((b : ℝ) : ℂ) ^ (-z)) s =
      c * (Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-s) / (1 - c * ((b : ℝ) : ℂ) ^ (-s)) := by
  have hd : HasDerivAt (fun z : ℂ => 1 - c * ((b : ℝ) : ℂ) ^ (-z))
      (-(c * (-(Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-s)))) s := by
    have h1 : HasDerivAt (fun z : ℂ => c * ((b : ℝ) : ℂ) ^ (-z))
        (c * (-(Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-s))) s :=
      (pcst_hasDerivAt_cpow_neg b hb s).const_mul c
    have h0 : HasDerivAt (fun _ : ℂ => (1 : ℂ)) (0 : ℂ) s := hasDerivAt_const s 1
    have hsub := h0.sub h1
    have hfun : ((fun _ : ℂ => (1 : ℂ)) - fun z : ℂ => c * ((b : ℝ) : ℂ) ^ (-z))
        = fun z : ℂ => 1 - c * ((b : ℝ) : ℂ) ^ (-z) := by
      funext z
      simp
    rw [hfun] at hsub
    convert hsub using 1
    ring
  rw [logDeriv_apply, hd.deriv]
  ring

/-- The logarithmic derivative of one Euler factor is at most four logarithms in size on the
line of real part minus one half. -/
private theorem pcst_factor_logDeriv_bound {d : ℕ} [NeZero d] (χ₀ : DirichletCharacter ℂ d)
    (p : ℕ) (hp : 2 ≤ p) {s : ℂ} (hre : s.re = -1 / 2) :
    ‖logDeriv (fun z : ℂ => 1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-z)) s‖ ≤
      4 * Real.log p := by
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hnorm : ‖((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have hre' : (-s).re = 1 / 2 := by
      rw [Complex.neg_re, hre]
      norm_num
    rw [hre']
  rw [pcst_factor_logDeriv (p : ℝ) hp0 (χ₀ (p : ZMod d)) s]
  rcases eq_or_ne (χ₀ (p : ZMod d)) 0 with hc | hc
  · rw [hc]
    simp only [zero_mul, norm_div, norm_zero, zero_div, norm_mul]
    positivity
  · have hunit : IsUnit (p : ZMod d) := by
      by_contra hnu
      exact hc (MulChar.map_nonunit χ₀ hnu)
    have hc1 : ‖χ₀ (p : ZMod d)‖ = 1 := pcst_norm_apply_eq_one χ₀ hunit
    have hznorm : ‖χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (1 / 2 : ℝ) := by
      rw [norm_mul, hc1, hnorm, one_mul]
    have hden : (p : ℝ) ^ (1 / 2 : ℝ) - 1 ≤
        ‖1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ := by
      have h := abs_norm_sub_norm_le (χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)) (1 : ℂ)
      rw [norm_one, norm_sub_rev] at h
      have h2 := le_abs_self (‖χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ - 1)
      linarith
    have hsqrt : (4 / 3 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
      have h2 : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (by linarith)
      have h0 : (0 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
      have hrw : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (p : ℝ) :=
        (Real.sqrt_eq_rpow (p : ℝ)).symm
      rw [hrw]
      nlinarith [h2, h0, hp2R]
    have hdenpos : 0 < (p : ℝ) ^ (1 / 2 : ℝ) - 1 := by linarith
    have hnum : ‖χ₀ (p : ZMod d) * (Real.log (p : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ (-s)‖ =
        (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) := by
      rw [norm_mul, norm_mul, hc1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hplog.le,
        hnorm, one_mul]
      ring
    rw [norm_div, hnum]
    have hpos : (0 : ℝ) < ‖1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ :=
      lt_of_lt_of_le hdenpos hden
    have hstep : (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) /
        ‖1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ ≤
        (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) / ((p : ℝ) ^ (1 / 2 : ℝ) - 1) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden
    have hfin : (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) / ((p : ℝ) ^ (1 / 2 : ℝ) - 1) ≤
        4 * Real.log (p : ℝ) := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hsqrt, hplog]
    linarith

/-- The left line bound for the logarithmic derivative of the L-function of an arbitrary
Dirichlet character. -/
private theorem pcst_logDeriv_LFunction_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero (DirichletCharacter.conductor χ)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C₀, hC₀, hL₀⟩ := LeanLab.Linnik.ExplicitFormula.logDeriv_left_line
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₀ + 4 * (q.primeFactors.card : ℝ) / Real.log 2, by positivity, fun t => ?_⟩
  have hne1 : ((-1 / 2 : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    norm_num at hre
  have hre : ((-1 / 2 : ℂ) + t * Complex.I).re = -1 / 2 := by simp
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds ((-1 / 2 : ℂ) + t * Complex.I)]
      fun z : ℂ => DirichletCharacter.LFunction χ.primitiveCharacter z *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) := by
    filter_upwards [isOpen_ne.mem_nhds hne1] with z hz
    exact pcst_LFunction_factorization χ hz
  have hprod : (fun z : ℂ => ∏ p ∈ q.primeFactors,
        (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z)))
      = ∏ p ∈ q.primeFactors, (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) := by
    funext z
    rw [Finset.prod_apply]
  have hne0 : DirichletCharacter.LFunction χ.primitiveCharacter
      ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 :=
    LeanLab.Linnik.ExplicitFormula.no_zero_left_line χ.primitiveCharacter_isPrimitive t
  have hneP : (∏ p ∈ q.primeFactors, (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z))) ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 := by
    rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => pcst_prime_factor_ne_zero χ p hp hre
  have hd0 : DifferentiableAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter)
      ((-1 / 2 : ℂ) + t * Complex.I) :=
    DirichletCharacter.differentiableAt_LFunction χ.primitiveCharacter _ (Or.inl hne1)
  have hdPterm : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ =>
      1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
        ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    exact ((((pcst_hasDerivAt_cpow_neg (p : ℝ) hp0 _).const_mul _)).const_sub 1).differentiableAt
  have hdP : DifferentiableAt ℂ (∏ p ∈ q.primeFactors, (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z))) ((-1 / 2 : ℂ) + t * Complex.I) :=
    DifferentiableAt.finsetProd hdPterm
  have hsplit : logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) =
      logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
          ((-1 / 2 : ℂ) + t * Complex.I) +
        ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I) := by
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    have hfun2 : (fun z : ℂ => DirichletCharacter.LFunction χ.primitiveCharacter z *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)))
        = DirichletCharacter.LFunction χ.primitiveCharacter *
            ∏ p ∈ q.primeFactors, (fun z : ℂ =>
              1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
                ((p : ℝ) : ℂ) ^ (-z)) := by
      funext z
      rw [Pi.mul_apply, Finset.prod_apply]
    rw [hfun2,
      logDeriv_mul (f := DirichletCharacter.LFunction χ.primitiveCharacter)
        (g := ∏ p ∈ q.primeFactors, (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)))
        ((-1 / 2 : ℂ) + t * Complex.I) hne0 hneP hd0 hdP,
      logDeriv_prod (fun p hp => pcst_prime_factor_ne_zero χ p hp hre) hdPterm]
  have hb0 : ‖logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
      ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      C₀ * Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) := by
    rw [logDeriv_apply]
    exact hL₀ (DirichletCharacter.conductor χ) χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive t
  have hbp : ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      4 * (q.primeFactors.card : ℝ) * Real.log q := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hterm : ∀ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ 4 * Real.log q := by
      intro p hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpdiv : p ∣ q := Nat.dvd_of_mem_primeFactors hp
      have hpq : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hpdiv
      have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by omega : 0 < p)
      have hlog : Real.log (p : ℝ) ≤ Real.log (q : ℝ) := Real.log_le_log hp0 hpqR
      calc ‖logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖
          ≤ 4 * Real.log (p : ℝ) := pcst_factor_logDeriv_bound χ.primitiveCharacter p hp2 hre
        _ ≤ 4 * Real.log (q : ℝ) := by linarith
    calc ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖
        ≤ ∑ _p ∈ q.primeFactors, 4 * Real.log (q : ℝ) := Finset.sum_le_sum hterm
      _ = 4 * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hLnonneg : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]
  have hdq_pos : 0 < ((DirichletCharacter.conductor χ : ℕ) : ℝ) := by
    have h : 0 < DirichletCharacter.conductor χ :=
      Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero (χ := χ))
    exact_mod_cast h
  have hqbound : Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) ≤
      Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by positivity)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hdvd : DirichletCharacter.conductor χ ∣ q := DirichletCharacter.conductor_dvd_level χ
    have hdq : DirichletCharacter.conductor χ ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd
    have hdc : ((DirichletCharacter.conductor χ : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    nlinarith [abs_nonneg t]
  have hlogq : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log
    · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      linarith
    · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      nlinarith [abs_nonneg t]
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcard0 : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := by positivity
  have hsumle := norm_sum_le q.primeFactors (fun p : ℕ => logDeriv (fun z : ℂ =>
    1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
      ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I))
  calc ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖
      = ‖logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
            ((-1 / 2 : ℂ) + t * Complex.I) +
          ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ := by rw [hsplit]
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
            ((-1 / 2 : ℂ) + t * Complex.I)‖ +
          ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ := norm_add_le _ _
    _ ≤ C₀ * Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) +
          ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ := by
        linarith [hb0, hsumle]
    _ ≤ C₀ * Real.log ((q : ℝ) * (|t| + 2)) + 4 * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
        have h1 : C₀ * Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) ≤
            C₀ * Real.log ((q : ℝ) * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hqbound hC₀
        linarith [h1, hbp]
    _ ≤ (C₀ + 4 * (q.primeFactors.card : ℝ) / Real.log 2) *
          Real.log ((q : ℝ) * (|t| + 2)) := by
        have key : 4 * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) ≤
            4 * (q.primeFactors.card : ℝ) / Real.log 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
          have hl21 : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            linarith
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          have hml : Real.log 2 * Real.log (q : ℝ) ≤ 1 * Real.log ((q : ℝ) * (|t| + 2)) := by
            have h1 := mul_le_mul hl21 hlogq hlogq0 (by norm_num : (0 : ℝ) ≤ 1)
            simpa using h1
          nlinarith [hcard0]
        nlinarith [key]

/-- Continuity of the logarithmic derivative of the L-function on the line of real part minus
one half. -/
private theorem pcst_logDeriv_LFunction_continuous (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero (DirichletCharacter.conductor χ)] :
    Continuous (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne1 : ((-1 / 2 : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    norm_num at hre
  have hA := pcst_analyticAt_LFunction χ hne1
  have hne : DirichletCharacter.LFunction χ ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 := by
    rw [pcst_LFunction_factorization (s := (-1 / 2 : ℂ) + t * Complex.I) χ hne1]
    refine mul_ne_zero
      (LeanLab.Linnik.ExplicitFormula.no_zero_left_line χ.primitiveCharacter_isPrimitive t) ?_
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pcst_prime_factor_ne_zero χ p hp (by simp)
  have hc : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ))
      ((-1 / 2 : ℂ) + t * Complex.I) :=
    hA.deriv.continuousAt.div hA.continuousAt hne
  exact ContinuousAt.comp (f := fun t : ℝ => (-1 / 2 : ℂ) + t * Complex.I) hc (by fun_prop)

/-- Continuity of the continued Gaussian transform on the line of real part minus one half. -/
private theorem pcst_continuedGaussian_line_continuous (δ : ℝ) :
    Continuous (fun t : ℝ => continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)) := by
  have h1 : Continuous (fun t : ℝ =>
      gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 1)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < ((((-1 / 2 : ℂ) + t * Complex.I) + 1)).re := by simp; norm_num
    exact ContinuousAt.comp (f := fun t : ℝ => ((-1 / 2 : ℂ) + t * Complex.I) + 1)
      (Continuation457.gaussian_mellin_differentiable δ _ hre).continuousAt (by fun_prop)
  have h2 : Continuous (fun t : ℝ =>
      gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < ((((-1 / 2 : ℂ) + t * Complex.I) + 2)).re := by simp; norm_num
    exact ContinuousAt.comp (f := fun t : ℝ => ((-1 / 2 : ℂ) + t * Complex.I) + 2)
      (Continuation457.gaussian_mellin_differentiable δ _ hre).continuousAt (by fun_prop)
  have hnum : Continuous (fun t : ℝ =>
      gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 1)) :=
    h2.sub (h1.const_mul _)
  have hden : Continuous (fun t : ℝ => (-1 / 2 : ℂ) + t * Complex.I) := by fun_prop
  have hdenne : ∀ t : ℝ, (-1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro t h
    have hre : (-1 / 2 : ℝ) = 0 := by simpa using congrArg Complex.re h
    norm_num at hre
  exact (hnum.div hden hdenne).congr fun t => rfl

/-- `log (|t| + 3)` is dominated by a quarter power of `1 + |t|`. -/
private theorem pcst_log_shape (t : ℝ) :
    Real.log (|t| + 3) ≤ 12 * (1 + |t|) ^ (1 / 4 : ℝ) := by
  set a := |t| with ha
  have ha0 : 0 ≤ a := abs_nonneg t
  have hpos : 0 < 1 + a := by positivity
  have hlog := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ a + 3)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hr : (a + 3) ^ (1 / 4 : ℝ) ≤ ((1 + a) * 3) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)
    simpa using h
  have hfin : (a + 3) ^ (1 / 4 : ℝ) ≤ 3 * (1 + a) ^ (1 / 4 : ℝ) := by
    calc (a + 3) ^ (1 / 4 : ℝ) ≤ ((1 + a) * 3) ^ (1 / 4 : ℝ) := hr
      _ = (1 + a) ^ (1 / 4 : ℝ) * 3 ^ (1 / 4 : ℝ) := Real.mul_rpow hpos.le (by norm_num)
      _ ≤ (1 + a) ^ (1 / 4 : ℝ) * 3 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hpos.le _)
      _ = 3 * (1 + a) ^ (1 / 4 : ℝ) := by ring
  calc Real.log (a + 3) ≤ (a + 3) ^ (1 / 4 : ℝ) / (1 / 4) := hlog
    _ = 4 * (a + 3) ^ (1 / 4 : ℝ) := by ring
    _ ≤ 4 * (3 * (1 + a) ^ (1 / 4 : ℝ)) := by linarith
    _ = 12 * (1 + a) ^ (1 / 4 : ℝ) := by ring

/-! ### D. The line of real part minus one half is an admissible contour -/

/-- LEAF. The integrand of step three is integrable on the line of real part minus one
half: the continued Gaussian transform decays faster than any power in the height, the
logarithmic derivative grows only like the logarithm of the height, and the scale factor
has the constant modulus `x ^ (-1 / 2)`.  This is one integrability statement and nothing
else; it fixes no value of the integral, no residue and no zero sum, and it needs no
hypothesis on the zeros. -/
theorem principal_half_line_integrable (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  haveI : NeZero (DirichletCharacter.conductor χ) :=
    ⟨DirichletCharacter.conductor_ne_zero (χ := χ)⟩
  obtain ⟨Cg, hCg, hGdec⟩ := pcst_continuedGaussian_decay δ
  obtain ⟨CL, hCL, hLb⟩ := pcst_logDeriv_LFunction_bound q χ
  have hcont : Continuous (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
    have h3 : Continuous (fun t : ℝ => (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ContinuousAt.comp (f := fun t : ℝ => ((-1 / 2 : ℂ) + t * Complex.I))
        (continuousAt_const_cpow (by exact_mod_cast hx0.ne')) (by fun_prop)
    exact ((pcst_logDeriv_LFunction_continuous q χ).mul
      (pcst_continuedGaussian_line_continuous δ)).mul h3
  set M : ℝ := max 1 (Real.log q) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  have hlogqM : Real.log q ≤ M := le_max_right _ _
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-(7 / 4 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (7 / 4 : ℝ)) (by norm_num))
  refine (hbase.const_mul (Cg * CL * (26 * M))).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hu1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hu0 : (0 : ℝ) < 1 + |t| := by linarith
  have hA1 : (1 : ℝ) ≤ (1 + |t|) ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hu1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using h
  have hA4 : (1 + |t|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (-(2 : ℝ)) = (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
    rw [show (-(7 / 4) : ℝ) = 1 / 4 + (-(2 : ℝ)) by norm_num, Real.rpow_add hu0]
  -- the logarithmic factor
  have hLt : Real.log (q * (|t| + 2)) ≤ 13 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hlogsplit : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
      Real.log_mul (by linarith) (by positivity)
    have hmono : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hrpow : Real.log (|t| + 3) ≤ 12 * (1 + |t|) ^ (1 / 4 : ℝ) := pcst_log_shape t
    rw [hlogsplit]
    have hqa : Real.log q ≤ M * (1 + |t|) ^ (1 / 4 : ℝ) :=
      le_trans hlogqM (le_mul_of_one_le_right hM0 hA1)
    have hmulA : (1 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ) ≤ M * (1 + |t|) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hM1 (Real.rpow_nonneg hu0.le _)
    have h2a : Real.log (|t| + 2) ≤ 12 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
      have h12 : 12 * (1 + |t|) ^ (1 / 4 : ℝ) ≤ 12 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
        nlinarith [hmulA]
      linarith
    have hsum : M * (1 + |t|) ^ (1 / 4 : ℝ) + 12 * M * (1 + |t|) ^ (1 / 4 : ℝ)
        = 13 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by ring
    linarith [hqa, h2a, hsum]
  have hL1 : ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ)) := by
    have h := hLb t
    have hCL0 : 0 ≤ CL := hCL
    calc ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖
        ≤ CL * Real.log (q * (|t| + 2)) := h
      _ ≤ CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hLt hCL0
  have hG1 : ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      Cg * (2 * (1 + |t|) ^ (-(2 : ℝ))) := by
    have h := hGdec t
    have h1 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith [sq_nonneg (|t| - 1)]
    have hdec : 1 / (1 + t ^ 2) ≤ 2 * (1 + |t|) ^ (-(2 : ℝ)) := by
      have h2 : (1 + |t|) ^ (-(2 : ℝ)) = 1 / (1 + |t|) ^ 2 := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
      rw [h2, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1]
    calc ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Cg / (1 + t ^ 2) := h
      _ = Cg * (1 / (1 + t ^ 2)) := by ring
      _ ≤ Cg * (2 * (1 + |t|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hdec hCg.le
  have hP1 : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_zero, add_zero]
    calc x ^ (-1 / 2 : ℝ) ≤ x ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = 1 := Real.rpow_zero x
  rw [norm_mul, norm_mul]
  have hstep : ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖ *
      ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ *
        ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      (CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ))) *
        (Cg * (2 * (1 + |t|) ^ (-(2 : ℝ)))) * 1 := by
    have hMA : 0 ≤ 13 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
      have h1 : 0 ≤ 13 * M := by linarith
      exact mul_nonneg h1 (Real.rpow_nonneg (by linarith [abs_nonneg t]) _)
    have hb_nonneg : 0 ≤ CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ)) := mul_nonneg hCL hMA
    have hd_nonneg : 0 ≤ Cg * (2 * (1 + |t|) ^ (-(2 : ℝ))) :=
      mul_nonneg hCg.le (by positivity)
    exact mul_le_mul (mul_le_mul hL1 hG1 (norm_nonneg _) hb_nonneg) hP1 (norm_nonneg _)
      (mul_nonneg hb_nonneg hd_nonneg)
  have heq : (CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ))) *
      (Cg * (2 * (1 + |t|) ^ (-(2 : ℝ)))) * 1 = (Cg * CL * (26 * M)) * (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
    rw [← hA4]
    ring
  linarith [hstep, heq]

/-! ### F. Towards leaf B: the Gaussian kernel's pole structure in the strip

Leaf B is the exact contour shift of the logarithmic derivative from real part two down to
real part minus one half.  The integrand of the shift is
`F(s) = -(L'/L)(s) * continuedGaussian δ s * x ^ s`: it restricts to the leaf's integrand on
both lines, since `continuedGaussian` agrees with `gaussianMellin` in the half plane of
absolute convergence (`Continuation457.continuedGaussian_eq`), and its poles are one at
`1` (from `zeta`), one at `0` (from the continued Gaussian, with residue one) and the
nontrivial zeros with their multiplicities.  The lemmas below supply the pole structure of
the Gaussian factor, which the lab does not have. -/

open Filter
open scoped Topology

/-- The numerator of the continued Gaussian kernel, away from zero. -/
private theorem pcsB_cont_mul (δ : ℝ) {s : ℂ} (hs : s ≠ 0) :
    s * continuedGaussian δ s =
      gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1) := by
  unfold continuedGaussian
  field_simp

/-- The numerator of the continued Gaussian kernel is differentiable near zero, both Mellin
factors having real part at least one there. -/
private theorem pcsB_num_differentiableAt (δ : ℝ) {s : ℂ} (hre : -1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => gaussianMellin δ (z + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) s := by
  have h2 : DifferentiableAt ℂ (fun z : ℂ => gaussianMellin δ (z + 2)) s := by
    have hd := Continuation457.gaussian_mellin_differentiable δ (s + 2) (by
      have hre' : (s + 2).re = s.re + 2 := by simp
      rw [hre']; linarith)
    exact hd.comp s (differentiableAt_id.add (differentiableAt_const _))
  have h1 : DifferentiableAt ℂ (fun z : ℂ => gaussianMellin δ (z + 1)) s := by
    have hd := Continuation457.gaussian_mellin_differentiable δ (s + 1) (by
      have hre' : (s + 1).re = s.re + 1 := by simp
      rw [hre']; linarith)
    exact hd.comp s (differentiableAt_id.add (differentiableAt_const _))
  exact h2.sub (h1.const_mul _)

/-- The numerator of the continued Gaussian kernel has value one at zero, for every shift. -/
private theorem pcsB_num_zero (δ : ℝ) :
    gaussianMellin δ 2 - (2 * π * Complex.I * δ) * gaussianMellin δ 1 = 1 :=
  Continuation457.shifted_first_moment δ

/-- The continued Gaussian kernel has a simple pole of residue one at zero:
the limit of `s * F(s)` along the punctured neighbourhood of zero is one. -/
private theorem pcsB_cont_residue_zero (δ : ℝ) :
    Tendsto (fun s : ℂ => s * continuedGaussian δ s) (𝓝[≠] 0) (𝓝 1) := by
  have hc : Tendsto (fun s : ℂ => gaussianMellin δ (s + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) (𝓝 0) (𝓝 1) := by
    have h := (Continuation457.regular_numerator_continuous δ).tendsto
    have hv : (fun s : ℂ => gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) 0 = 1 := by
      simpa using pcsB_num_zero δ
    simpa only [hv] using h
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (pcsB_cont_mul δ hs).symm

/-- The continued Gaussian kernel is differentiable in the strip `Re s > -1` away from
zero. -/
private theorem pcsB_cont_differentiableAt (δ : ℝ) {s : ℂ} (hs : s ≠ 0) (hre : -1 < s.re) :
    DifferentiableAt ℂ (continuedGaussian δ) s := by
  have hnum := pcsB_num_differentiableAt δ hre
  have heq : continuedGaussian δ = (fun z : ℂ => gaussianMellin δ (z + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) * (fun z : ℂ => z)⁻¹ := rfl
  rw [heq]
  exact hnum.mul (differentiableAt_id.inv hs)

/-- The continued Gaussian kernel is analytic in the strip `Re s > -1` away from zero. -/
private theorem pcsB_cont_analyticAt (δ : ℝ) {s : ℂ} (hs : s ≠ 0) (hre : -1 < s.re) :
    AnalyticAt ℂ (continuedGaussian δ) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_ne.mem_nhds hs,
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz hzre
  exact pcsB_cont_differentiableAt δ hz hzre

/-- The numerator of the continued Gaussian kernel is analytic in the strip `Re s > -1`. -/
private theorem pcsB_num_analyticAt (δ : ℝ) {s : ℂ} (hre : -1 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => gaussianMellin δ (z + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
  exact pcsB_num_differentiableAt δ hz

/-- The continued Gaussian kernel has a pole of order exactly minus one at zero. -/
private theorem pcsB_cont_order_zero (δ : ℝ) :
    meromorphicOrderAt (continuedGaussian δ) 0 = ((-1 : ℤ) : WithTop ℤ) := by
  have hnum : AnalyticAt ℂ (fun z : ℂ => gaussianMellin δ (z + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) 0 :=
    pcsB_num_analyticAt δ (s := 0) (by simp)
  have hnum0 : (fun z : ℂ => gaussianMellin δ (z + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) 0 ≠ 0 := by
    have hv : (fun z : ℂ => gaussianMellin δ (z + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) 0 = 1 := by
      simpa using pcsB_num_zero δ
    rw [hv]; exact one_ne_zero
  have hm : MeromorphicAt (continuedGaussian δ) 0 := by
    have heq : continuedGaussian δ = (fun z : ℂ => gaussianMellin δ (z + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) * (fun z : ℂ => z)⁻¹ := rfl
    rw [heq]
    exact hnum.meromorphicAt.mul (analyticAt_id.meromorphicAt.inv)
  rw [meromorphicOrderAt_eq_int_iff hm]
  refine ⟨fun z : ℂ => gaussianMellin δ (z + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1), hnum, hnum0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  show continuedGaussian δ s = (s - 0) ^ (-1 : ℤ) •
    (gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1))
  rw [sub_zero, zpow_neg_one, smul_eq_mul, inv_mul_eq_div]
  rfl

/-! #### F2. The integrand of the shift: its poles and their residues -/

open LeanLab.PNTPort.ExplicitPsi1 in
/-- `x ^ s` is analytic in `s` for a positive scale. -/
private lemma pcsB_xpow_analyticAt {x : ℝ} (hx : 0 < x) (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
  analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx)

/-- The Gaussian kernel times the scale factor is analytic in the strip, away from zero. -/
private lemma pcsB_kernel_analyticAt (δ : ℝ) {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : z ≠ 0)
    (hre : -1 < z.re) :
    AnalyticAt ℂ (fun s : ℂ => continuedGaussian δ s * (x : ℂ) ^ s) z :=
  (pcsB_cont_analyticAt δ hz hre).mul (pcsB_xpow_analyticAt hx z)

/-- The Gaussian kernel is meromorphic in the strip. -/
private lemma pcsB_cont_meromorphicAt (δ : ℝ) {z : ℂ} (hre : -1 < z.re) :
    MeromorphicAt (continuedGaussian δ) z := by
  by_cases hz : z = 0
  · subst hz
    have heq : continuedGaussian δ = (fun z : ℂ => gaussianMellin δ (z + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (z + 1)) * (fun z : ℂ => z)⁻¹ := rfl
    rw [heq]
    exact (pcsB_num_analyticAt δ (s := 0) (by simp)).meromorphicAt.mul
      (analyticAt_id.meromorphicAt.inv)
  · exact (pcsB_cont_analyticAt δ hz hre).meromorphicAt

/-- The integrand of the shift, `-(ζ'/ζ) · G · x ^ s`, is meromorphic in the strip. -/
private lemma pcsB_F_meromorphicAt {x : ℝ} (hx : 0 < x) (δ : ℝ) {z : ℂ} (hre : -1 < z.re) :
    MeromorphicAt (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) z :=
  (((LeanLab.PNTPort.ExplicitPsi1.meromorphicAt_zeta z).deriv.div
    (LeanLab.PNTPort.ExplicitPsi1.meromorphicAt_zeta z)).neg).mul
    ((pcsB_cont_meromorphicAt δ hre).mul (pcsB_xpow_analyticAt hx z).meromorphicAt)

/-- The integrand of the shift is analytic away from zero, one and the zeros of zeta. -/
private lemma pcsB_F_analyticAt {x : ℝ} (hx : 0 < x) (δ : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hre : -1 < z.re) (h1 : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    AnalyticAt ℂ (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) z := by
  have hζa := LeanLab.PNTPort.ExplicitPsi1.analyticAt_zeta h1
  exact (hζa.deriv.div hζa hζ).neg.mul (pcsB_kernel_analyticAt δ hx hz0 hre)

/-- The integrand of the shift has at most simple poles in the strip. -/
private lemma pcsB_F_order_ge {x : ℝ} (hx : 0 < x) (δ : ℝ) {z : ℂ} (hre : -1 < z.re) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
        (continuedGaussian δ s * (x : ℂ) ^ s)) z := by
  have hzeta := LeanLab.PNTPort.ExplicitPsi1.meromorphicAt_zeta z
  by_cases hz : z = 0
  · subst hz
    have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
    have hζa := LeanLab.PNTPort.ExplicitPsi1.analyticAt_zeta (by norm_num : (0 : ℂ) ≠ 1)
    have hA : AnalyticAt ℂ (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
        (x : ℂ) ^ s) 0 := (hζa.deriv.div hζa hζ0).neg.mul (pcsB_xpow_analyticAt hx 0)
    have hG := pcsB_cont_meromorphicAt δ (z := 0) (by simp)
    have hmul : meromorphicOrderAt (fun s : ℂ =>
        (-(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s) * continuedGaussian δ s) 0 =
        meromorphicOrderAt (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
          (x : ℂ) ^ s) 0 + meromorphicOrderAt (continuedGaussian δ) 0 :=
      meromorphicOrderAt_mul hA.meromorphicAt hG
    have hswap : (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
        (continuedGaussian δ s * (x : ℂ) ^ s)) = (fun s : ℂ =>
        (-(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s) * continuedGaussian δ s) := by
      funext s; ring
    rw [hswap, hmul, pcsB_cont_order_zero δ]
    have := hA.meromorphicOrderAt_nonneg
    calc (-1 : WithTop ℤ) = 0 + -1 := by simp
      _ ≤ _ := add_le_add_left this _
  · have hk := pcsB_kernel_analyticAt δ hx hz hre
    have hmul : meromorphicOrderAt ((fun s : ℂ => -(logDeriv riemannZeta s)) *
        (fun s : ℂ => continuedGaussian δ s * (x : ℂ) ^ s)) z =
        meromorphicOrderAt (fun s : ℂ => -(logDeriv riemannZeta s)) z +
          meromorphicOrderAt (fun s : ℂ => continuedGaussian δ s * (x : ℂ) ^ s) z :=
      meromorphicOrderAt_mul (hzeta.deriv.div hzeta).neg hk.meromorphicAt
    have hprod : (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
        (continuedGaussian δ s * (x : ℂ) ^ s)) = (fun s : ℂ => -(logDeriv riemannZeta s)) *
          (fun s : ℂ => continuedGaussian δ s * (x : ℂ) ^ s) := by
      funext s; simp only [Pi.mul_apply, logDeriv_apply]
    rw [hprod, hmul]
    have h1 : meromorphicOrderAt (fun s : ℂ => -(logDeriv riemannZeta s)) z =
        meromorphicOrderAt (logDeriv riemannZeta) z :=
      (meromorphicOrderAt_neg (f := logDeriv riemannZeta)).symm
    rw [h1]
    calc (-1 : WithTop ℤ) = -1 + 0 := by simp
      _ ≤ _ := add_le_add (LeanLab.PNTPort.ExplicitPsi1.order_logDeriv_zeta_ge z)
        hk.meromorphicOrderAt_nonneg

/-- The residue of the integrand at zero is minus log of two pi. -/
private lemma pcsB_residue_F_zero {x : ℝ} (hx : 0 < x) (δ : ℝ) :
    residue (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) 0 = -((Real.log (2 * π) : ℝ) : ℂ) := by
  apply residue_eq_of_tendsto
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hζa := LeanLab.PNTPort.ExplicitPsi1.analyticAt_zeta (by norm_num : (0 : ℂ) ≠ 1)
  have hlog : ContinuousAt (fun s : ℂ => deriv riemannZeta s / riemannZeta s) 0 :=
    (hζa.deriv.div hζa hζ0).continuousAt
  have hval : deriv riemannZeta 0 / riemannZeta 0 = ((Real.log (2 * π) : ℝ) : ℂ) :=
    LeanLab.HelfgottMajor.Principal457.zeta_logDeriv_zero
  have hlog' : Tendsto (fun s : ℂ => deriv riemannZeta s / riemannZeta s) (𝓝[≠] (0 : ℂ))
      (𝓝 ((Real.log (2 * π) : ℝ) : ℂ)) := by
    have h : Tendsto (fun s : ℂ => deriv riemannZeta s / riemannZeta s) (𝓝[≠] (0 : ℂ))
        (𝓝 (deriv riemannZeta 0 / riemannZeta 0)) :=
      hlog.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hval] at h
  have hx0 : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] (0 : ℂ)) (𝓝 ((x : ℂ) ^ (0 : ℂ))) :=
      (continuousAt_const_cpow (by exact_mod_cast hx.ne')).tendsto.mono_left
        nhdsWithin_le_nhds
    simpa using h
  have hlim : Tendsto (fun s : ℂ => (-(deriv riemannZeta s / riemannZeta s)) *
      ((s * continuedGaussian δ s) * (x : ℂ) ^ s)) (𝓝[≠] (0 : ℂ))
      (𝓝 (-((Real.log (2 * π) : ℝ) : ℂ) * (1 * 1))) :=
    (hlog'.neg).mul (pcsB_cont_residue_zero δ |>.mul hx0)
  have hfun : (fun s : ℂ => (s - 0) * (-(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s : ℂ => (-(deriv riemannZeta s / riemannZeta s)) *
        ((s * continuedGaussian δ s) * (x : ℂ) ^ s)) := by
    filter_upwards with s
    ring
  have h1 : Tendsto (fun s : ℂ => (s - 0) * (-(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s))) (𝓝[≠] (0 : ℂ))
      (𝓝 (-((Real.log (2 * π) : ℝ) : ℂ) * (1 * 1))) := hlim.congr' hfun.symm
  simpa using h1

/-- The residue of the integrand at one is the main term `G(1) · x`. -/
private lemma pcsB_residue_F_one {x : ℝ} (hx : 0 < x) (δ : ℝ) :
    residue (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) 1 =
      fhat etaHeart (-δ) * (x : ℂ) := by
  apply residue_eq_of_tendsto
  have hk := pcsB_kernel_analyticAt δ hx (one_ne_zero) (by norm_num : (-1 : ℝ) < (1 : ℂ).re)
  have hlim : Tendsto (fun s : ℂ => (-((s - 1) * (deriv riemannZeta s / riemannZeta s))) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) (𝓝[≠] (1 : ℂ))
      (𝓝 (-(-1 : ℂ) * (continuedGaussian δ 1 * (x : ℂ) ^ (1 : ℂ)))) :=
    (LeanLab.PNTPort.ExplicitPsi1.tendsto_logDeriv_zeta_one.neg.mul
      (hk.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  have hfun : (fun s : ℂ => (s - 1) * (-(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s))) =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s : ℂ => (-((s - 1) * (deriv riemannZeta s / riemannZeta s))) *
        (continuedGaussian δ s * (x : ℂ) ^ s)) := by
    filter_upwards with s
    ring
  have h1 : Tendsto (fun s : ℂ => (s - 1) * (-(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s))) (𝓝[≠] (1 : ℂ))
      (𝓝 (-(-1 : ℂ) * (continuedGaussian δ 1 * (x : ℂ) ^ (1 : ℂ)))) := hlim.congr' hfun.symm
  have hval : -(-1 : ℂ) * (continuedGaussian δ 1 * (x : ℂ) ^ (1 : ℂ)) =
      fhat etaHeart (-δ) * (x : ℂ) := by
    rw [Continuation457.continuedGaussian_eq δ 1 (by norm_num),
      Gaussian269.mellin_one δ, Complex.cpow_one]
    ring
  rw [hval] at h1
  exact h1

/-- The residue of the integrand at a zero of zeta is minus the zero term. -/
private lemma pcsB_residue_F_zero_of_zeta {x : ℝ} (hx : 0 < x) (δ : ℝ) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hre : -1 < ρ.re) (hρ1 : ρ ≠ 1) :
    residue (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) ρ =
      -((analyticOrderNatAt riemannZeta ρ : ℂ) *
        (continuedGaussian δ ρ * (x : ℂ) ^ ρ)) := by
  apply residue_eq_of_tendsto
  have hk := pcsB_kernel_analyticAt δ hx hρ0 hre
  have hlim : Tendsto (fun s : ℂ => (-((s - ρ) * (deriv riemannZeta s / riemannZeta s))) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) (𝓝[≠] ρ)
      (𝓝 (-((analyticOrderNatAt riemannZeta ρ : ℂ)) *
        (continuedGaussian δ ρ * (x : ℂ) ^ ρ))) :=
    (LeanLab.PNTPort.ExplicitPsi1.tendsto_logDeriv_zeta_of_ne_one hρ1).neg.mul
      (hk.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hfun : (fun s : ℂ => (s - ρ) * (-(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s))) =ᶠ[𝓝[≠] ρ]
      (fun s : ℂ => (-((s - ρ) * (deriv riemannZeta s / riemannZeta s))) *
        (continuedGaussian δ s * (x : ℂ) ^ s)) := by
    filter_upwards with s
    ring
  have h1 := hlim.congr' hfun.symm
  simpa only [neg_mul] using h1

section
open Complex Set

/-! #### F3. The rectangle residue identity for the shifted Gaussian kernel -/

/-- Border points of `[-1/2, 2] × [-T, T]` lie on one of its four sides. -/
private lemma pcsB_border_cases {T : ℝ} {z : ℂ} (hz : z ∈ RectangleBorder ⟨-1 / 2, -T⟩ ⟨2, T⟩) :
    z.im = -T ∨ z.re = -1 / 2 ∨ z.im = T ∨ z.re = 2 := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hz
  rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Membership in `[-1/2, 2] × [-T, T]`. -/
private lemma pcsB_mem_rect {T : ℝ} (hT : 0 ≤ T) {z : ℂ} :
    z ∈ Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ ↔
      (-1 / 2 ≤ z.re ∧ z.re ≤ 2) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
  simp only [Rectangle, mem_reProdIm]
  rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2), uIcc_of_le (by linarith)]
  simp

/-- The zeros of zeta in the rectangle are finitely many. -/
private lemma pcsB_zeros_rect_finite (T : ℝ) :
    (Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ ∩ riemannZetaZeros).Finite := by
  have hc : IsCompact (Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩) :=
    (isCompact_uIcc (a := (-1 / 2 : ℝ)) (b := 2)).reProdIm
      (isCompact_uIcc (a := -T) (b := T))
  exact IsCompact.inter_riemannZetaZeros_finite hc


/-- zeta has no zero at a real point of `[-1/2, 0]`.  Off the real axis this is
`ZetaZeros.Sym.zeta_ne_zero_of_re_nonpos`; on it the functional equation writes `ζ σ` as
`2 (2π)^{-s} Γ s cos (π s / 2) ζ s` with `s = 1 - σ ∈ (1, 3/2]`, and no factor vanishes there. -/
private theorem pcsB_zeta_ne_zero_of_real_nonpos {σ : ℝ} (h1 : -(1 / 2) ≤ σ) (h2 : σ < 0) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  set w : ℂ := ((1 - σ : ℝ) : ℂ) with hw
  have hwre : w.re = 1 - σ := by rw [hw]; simp
  have harg : (1 : ℂ) - w = (σ : ℂ) := by rw [hw]; push_cast; ring
  have hne_nat : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have hre : w.re = (-(n : ℂ)).re := by rw [h]
    rw [hwre] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (1 : ℝ) < 1 - σ := by linarith
    rcases n with _ | n
    · simp at hre; linarith
    · have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      push_cast at hre
      linarith
  have hne1 : w ≠ 1 := by
    intro h
    have hre : w.re = 1 := by rw [h]; simp
    rw [hwre] at hre
    linarith
  have hfe := riemannZeta_one_sub hne_nat hne1
  rw [harg, hz] at hfe
  have hcos : Complex.cos (π * w / 2) ≠ 0 := by
    apply LeanLab.PNTPort.ZetaZeros.cos_ne_zero_of_not_odd
    intro k hk
    have hreal : (1 - σ : ℝ) = 2 * (k : ℝ) + 1 := by
      have := congrArg Complex.re hk
      rw [hw] at this
      simpa using this
    have hk1 : (0 : ℝ) < (k : ℝ) := by linarith
    have hk2 : (k : ℝ) ≤ 1 := by linarith
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk1
    have : (k : ℤ) ≤ 1 := by exact_mod_cast hk2
    interval_cases k
    norm_num at hreal
    linarith
  have hGamma : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have hre : w.re = (-(n : ℂ)).re := by rw [h]
    rw [hwre] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) < 1 - σ := by linarith
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hbase : (2 * (π : ℂ)) ^ (-w) ≠ 0 := by
    have h0 : (2 * (π : ℂ)) ≠ 0 := by
      have hπ : ((π : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_pos.ne'
      simpa using mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hπ
    rw [Complex.cpow_def_of_ne_zero h0]
    exact Complex.exp_ne_zero _
  have hfac : (2 : ℂ) * (2 * (π : ℂ)) ^ (-w) * Complex.Gamma w *
      Complex.cos (π * w / 2) * riemannZeta w ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hbase) hGamma) hcos) ?_
    exact riemannZeta_ne_zero_of_one_lt_re (by rw [hwre]; linarith)
  exact hfac hfe.symm

/-- **The residue sum over a rectangle.** If zeta has no zero on the border of
`[-1/2, 2] × [-T, T]`, then the normalized rectangle integral of the shift integrand is
minus log of two pi, plus the main term, minus the zero terms over the zeros inside. -/
private theorem pcsB_rect_residue {x T : ℝ} (hx : 0 < x) (δ : ℝ) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩, riemannZeta z ≠ 0) :
    RectangleIntegral' (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
      (continuedGaussian δ s * (x : ℂ) ^ s)) (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ =
      -(((Real.log (2 * π) : ℝ)) : ℂ) + fhat etaHeart (-δ) * (x : ℂ) -
        ∑ ρ ∈ (pcsB_zeros_rect_finite T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (gaussianMellin δ ρ * (x : ℂ) ^ ρ) := by
  set F : ℂ → ℂ := fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
    (continuedGaussian δ s * (x : ℂ) ^ s) with hFdef
  set R : Set ℂ := Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ with hRdef
  set Zf := (pcsB_zeros_rect_finite T).toFinset with hZf
  have hmem := fun z => pcsB_mem_rect (T := T) hT.le (z := z)
  have hRre : ∀ z ∈ R, -1 < z.re := by
    intro z hz
    have := ((hmem z).mp hz).1.1
    linarith
  have h0R : (0 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have h1R : (1 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> linarith
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hZfZ : ∀ ρ ∈ Zf, ρ ∈ R ∧ riemannZeta ρ = 0 := by
    intro ρ hρ
    rw [hZf, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1, hρ.2⟩
  have hgood : ∀ z ∈ R, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → 0 ≤ meromorphicOrderAt F z :=
    fun z hz h0 h1 hζ => (pcsB_F_analyticAt hx δ h0 (hRre z hz) h1 hζ).meromorphicOrderAt_nonneg
  have hbR : RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ ⊆ R :=
    rectangleBorder_subset_rectangle _ _
  have hP : ∀ z ∈ R, meromorphicOrderAt F z < 0 → z ∈ (insert 0 (insert 1 Zf) : Finset ℂ) := by
    intro z hz hneg
    by_contra hns
    simp only [Finset.mem_insert, not_or] at hns
    obtain ⟨h0, h1, hZ⟩ := hns
    have hζ : riemannZeta z ≠ 0 := by
      intro h
      apply hZ
      rw [hZf, Set.Finite.mem_toFinset]
      exact ⟨hz, h⟩
    exact absurd (hgood z hz h0 h1 hζ) (not_le.mpr hneg)
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := F)
    (z := (⟨-1 / 2, -T⟩ : ℂ)) (w := ⟨2, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z hz => pcsB_F_meromorphicAt hx δ (hRre z hz))
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      rcases pcsB_border_cases hz with h | h | h | h
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; norm_num at h)
          (by intro e; rw [e] at h; norm_num at h) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; norm_num at h)
          (by intro e; rw [e] at h; norm_num at h) (hbd z hz)) (not_le.mpr hneg))
    (by
      apply (insert 0 (insert 1 Zf) : Finset ℂ).finite_toSet.subset
      intro z ⟨hz, hneg⟩
      exact hP z hz hneg)
    (fun z hz => pcsB_F_order_ge hx δ (hRre z hz))
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt F z < 0} =
      ((insert 0 (insert 1 Zf) : Finset ℂ) : Set ℂ) ∩ {z | meromorphicOrderAt F z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hP z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩
      refine ⟨?_, hneg⟩
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact h0R
      · exact h1R
      · exact (hZfZ z hz).1
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z hzS hzP =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (pcsB_F_meromorphicAt hx δ
      (hRre z (by
        have hzR : z ∈ R := by
          simp only [Finset.mem_coe, Finset.mem_insert] at hzS
          rcases hzS with rfl | rfl | hz
          · exact h0R
          · exact h1R
          · exact (hZfZ z hz).1
        exact hzR))) (not_lt.mp hzP))]
  rw [sumResiduesIn, Finset.tsum_subtype' (insert 0 (insert 1 Zf)) (fun z => residue F z)]
  have h1Z : (1 : ℂ) ∉ Zf := fun h => by
    have := (hZfZ 1 h).2
    exact absurd this (by simpa using riemannZeta_one_ne_zero)
  have h0Z : (0 : ℂ) ∉ insert 1 Zf := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨zero_ne_one, fun h => hζ0 (hZfZ 0 h).2⟩
  rw [Finset.sum_insert h0Z, Finset.sum_insert h1Z]
  have hres0 : residue F 0 = -(((Real.log (2 * π) : ℝ)) : ℂ) := pcsB_residue_F_zero hx δ
  have hres1 : residue F 1 = fhat etaHeart (-δ) * (x : ℂ) := pcsB_residue_F_one hx δ
  rw [hres0, hres1]
  have hsum : ∑ ρ ∈ Zf, residue F ρ =
      ∑ ρ ∈ Zf, -((analyticOrderNatAt riemannZeta ρ : ℂ) *
        (gaussianMellin δ ρ * (x : ℂ) ^ ρ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    obtain ⟨hρR, hρ0⟩ := hZfZ ρ hρ
    have hρne0 : ρ ≠ 0 := by rintro rfl; exact hζ0 hρ0
    have hρne1 : ρ ≠ 1 := by rintro rfl; exact absurd hρ0 (by simpa using riemannZeta_one_ne_zero)
    have hρre : 0 < ρ.re := by
      by_contra hpos
      push_neg at hpos
      have hlow : -(1 / 2 : ℝ) ≤ ρ.re := by linarith [((hmem ρ).mp hρR).1.1]
      by_cases him : ρ.im = 0
      · have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := by
          apply Complex.ext
          · simp
          · simp [him]
        have hne0 : ρ.re ≠ 0 := by
          intro h
          have hz0 : riemannZeta ((0 : ℝ) : ℂ) = 0 := by
            rw [← h, ← hρeq]
            exact hρ0
          exact hζ0 hz0
        exact pcsB_zeta_ne_zero_of_real_nonpos hlow (lt_of_le_of_ne hpos hne0)
          (by rw [← hρeq]; exact hρ0)
      · exact LeanLab.PNTPort.ZetaZeros.zeta_ne_zero_of_re_nonpos hpos him hρ0
    rw [pcsB_residue_F_zero_of_zeta hx δ hρne0 (by linarith) hρne1,
      Continuation457.continuedGaussian_eq δ ρ hρre]
  rw [hsum, Finset.sum_neg_distrib]
  ring

/-! #### F4. The line of real part two: integrability, truncation limit and value

On `Re s = 2` the logarithmic derivative is bounded, because there it is the Dirichlet
series of the von Mangoldt function and that series converges absolutely, while the Gaussian
Mellin transform decays like `(1 + t ^ 2)⁻¹` on any vertical line of real part at least
`1 / 2`.  So the integrand is integrable on the whole line and the truncated integrals
converge to the full-line integral; that integral is `-Schi` by leaf A. -/

set_option maxHeartbeats 1200000 in
/-- Zeta's logarithmic derivative is bounded on the line of real part two: there it is minus
the absolutely convergent Dirichlet series of the von Mangoldt function. -/
private theorem pcsB_logDeriv_two_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((2 : ℂ) + t * Complex.I)‖ ≤ C := by
  set f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hf
  have hf0 : f 0 = 0 := by
    have h : ArithmeticFunction.vonMangoldt 0 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_apply]
      simp [not_isPrimePow_zero]
    simp [hf, h]
  have hC : Summable (fun n : ℕ => ‖LSeries.term f (2 : ℂ) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) (by norm_num)).norm
  have hnorms : ∀ t : ℝ, ∑' n : ℕ, ‖LSeries.term f ((2 : ℂ) + t * Complex.I) n‖ =
      ∑' n : ℕ, ‖LSeries.term f (2 : ℂ) n‖ := by
    intro t
    have hsre : ((2 : ℂ) + t * Complex.I).re = 2 := by simp
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [LSeries.term]
    · have hn0 : n ≠ 0 := hn.ne'
      simp only [LSeries.term, hn0, if_false]
      rw [norm_div, norm_div, Complex.norm_natCast_cpow_of_pos hn,
        Complex.norm_natCast_cpow_of_pos hn, hsre]
      norm_num
  refine ⟨∑' n : ℕ, ‖LSeries.term f (2 : ℂ) n‖, tsum_nonneg fun n => norm_nonneg _,
    fun t => ?_⟩
  have hsre : ((2 : ℂ) + t * Complex.I).re = 2 := by simp
  have hLs : LSeriesSummable f ((2 : ℂ) + t * Complex.I) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hsre]; norm_num)
  have hL : logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) =
      - LSeries f ((2 : ℂ) + t * Complex.I) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := (2 : ℂ) + t * Complex.I) (by rw [hsre]; norm_num)
    simp only [logDeriv_apply]
    rw [h]
    ring
  rw [hL, norm_neg]
  calc ‖LSeries f ((2 : ℂ) + t * Complex.I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term f ((2 : ℂ) + t * Complex.I) n‖ :=
        norm_tsum_le_tsum_norm hLs.norm
    _ = ∑' n : ℕ, ‖LSeries.term f (2 : ℂ) n‖ := hnorms t

/-- The integrand of the shift is integrable on the line of real part two. -/
private theorem pcsB_two_line_integrable {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Integrable (fun t : ℝ =>
      logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
        (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨C1, hC1, hC⟩ := pcsB_logDeriv_two_bound
  obtain ⟨K, hK, hKdec⟩ := pcst_mellin_decay_half δ 2 (by norm_num)
  have hcont : Continuous (fun t : ℝ =>
      logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
        (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I))) := by
    have h1 : Continuous (fun t : ℝ => logDeriv riemannZeta ((2 : ℂ) + t * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hζa : AnalyticAt ℂ riemannZeta ((2 : ℂ) + t * Complex.I) :=
        LeanLab.PNTPort.ExplicitPsi1.analyticAt_zeta (by
          intro h
          have := congrArg Complex.re h
          simp at this)
      exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * Complex.I)
        (hζa.deriv.div hζa (riemannZeta_ne_zero_of_one_lt_re (by simp))).continuousAt
        (by fun_prop)
    have h2 : Continuous (fun t : ℝ => gaussianMellin δ ((2 : ℂ) + t * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * Complex.I)
        (Continuation457.gaussian_mellin_differentiable δ _ (by simp)).continuousAt
        (by fun_prop)
    have h3 : Continuous (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * Complex.I)
        (continuousAt_const_cpow (by exact_mod_cast hx0.ne')) (by fun_prop)
    exact h1.mul (h2.mul h3)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (C1 * K * x ^ 2))
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hxpow : ‖(x : ℂ) ^ ((2 : ℂ) + t * Complex.I)‖ = x ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    norm_num [Real.rpow_two]
  have hG := hKdec t
  have hl := hC t
  rw [norm_mul, norm_mul, hxpow]
  have hGG : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * x ^ 2 ≤
      (K / (1 + t ^ 2)) * x ^ 2 :=
    mul_le_mul_of_nonneg_right hG (sq_nonneg x)
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hstep : ‖logDeriv riemannZeta ((2 : ℂ) + t * Complex.I)‖ *
      (‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * x ^ 2) ≤
      C1 * ((K / (1 + t ^ 2)) * x ^ 2) :=
    mul_le_mul hl hGG (by positivity) hC1
  have heq : C1 * ((K / (1 + t ^ 2)) * x ^ 2) = (C1 * K * x ^ 2) * (1 + t ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    ring
  rw [heq] at hstep
  simpa [div_eq_mul_inv] using hstep

/-- The truncated integrals of the shift integrand on the line of real part two converge to
the full-line integral. -/
private theorem pcsB_two_line_tendsto {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
      logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
        (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)))
      atTop (𝓝 (∫ t : ℝ, logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
        (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)))) :=
  intervalIntegral_tendsto_integral (pcsB_two_line_integrable hx δ)
    tendsto_neg_atTop_atBot tendsto_id

/-- **The value of the line of real part two.** The normalized integrals of the shift
integrand over `[-T, T]` on that line converge to minus the twisted von Mangoldt sum: the
full-line integral is leaf A, once the logarithmic derivative of the trivial character's
`L`-function is written as that of zeta. -/
private theorem pcsB_two_line_value {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Tendsto (fun T : ℝ => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
      logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
        (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)))
      atTop (𝓝 (- Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x)) := by
  have hA := principal_two_line_prime_sum x hx 1 (1 : DirichletCharacter ℂ 1) δ
  have hfun : (fun t : ℝ => logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
      (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)))
      = fun t : ℝ => logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
          ((2 : ℂ) + t * Complex.I) * gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
            (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) := by
    funext t
    simp only [DirichletCharacter.LFunction_modOne_eq]
    ring
  have hval : (1 / (2 * π) : ℂ) * ∫ t : ℝ, logDeriv riemannZeta ((2 : ℂ) + t * Complex.I) *
      (gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)) =
      - Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x := by
    rw [hfun]
    exact hA
  have hT := (pcsB_two_line_tendsto hx δ).const_mul (1 / (2 * π) : ℂ)
  rw [hval] at hT
  exact hT


/-! #### F5. Quadratic decay of the kernel in the strip, uniformly in the real part

The recurrence `s·G(s) = G(s+2) - 2πiδ·G(s+1)` turns a bound on three neighbouring vertical
lines into a bound on the strip.  The three line bounds are uniform in the real part on
`[5/2, 7]`, so the constant below does not depend on `σ`. -/

/-- A line constant for the Gaussian Mellin transform, uniform in the real part of the
exponent on `[1, b]`: on `(0, 1)` the weight `x ^ (σ - 1)` is at most one and on `(1, ∞)` it
is at most `x ^ (b - 1)`. -/
private theorem pcsB_line_constant_uniform (δ : ℝ) (b : ℝ) (hb : 1 ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ b → ∀ t : ℝ,
      ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ B := by
  have hgauss : ∀ (τ : ℝ), IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Set.Ioi (0 : ℝ)) := by
    intro τ
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (0 : ℝ)) (by norm_num)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    dsimp only
    rw [Real.rpow_zero, one_mul]
    congr 1
    ring
  have hgint := hgauss 0
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (b - 1) * Real.exp (-x ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (b - 1)) (by linarith)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    congr 1
    ring
  have hsumint : IntegrableOn (fun x : ℝ => (1 + x ^ (b - 1)) * Real.exp (-x ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    have h := hgint.add hrpow
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [Pi.add_apply]
    rw [show b - 1 = -1 + b by ring]
    ring
  refine ⟨(∫ x in Set.Ioi (0 : ℝ), (1 + x ^ (b - 1)) * Real.exp (-x ^ 2 / 2)) + 1, ?_, ?_⟩
  · have h0 : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), (1 + x ^ (b - 1)) * Real.exp (-x ^ 2 / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun x hx => by
        have hx0 : (0 : ℝ) < x := hx
        have h1 : 0 ≤ x ^ (b - 1) := Real.rpow_nonneg hx0.le _
        have h2 := Real.exp_pos (-x ^ 2 / 2)
        nlinarith
    linarith
  · intro σ hσ1 hσb t
    have hm := Gaussian269.mellin_norm_le δ ((σ : ℂ) + t * Complex.I)
    have hre : ((σ : ℂ) + t * Complex.I).re = σ := by simp
    rw [hre] at hm
    refine hm.trans ?_
    have hint : IntegrableOn (fun x : ℝ => x ^ (σ - 1) * Real.exp (-x ^ 2 / 2))
        (Set.Ioi (0 : ℝ)) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
        (s := (σ - 1)) (by linarith)
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x _
      congr 1
      ring
    refine le_trans (setIntegral_mono_on hint hsumint measurableSet_Ioi ?_)
      (le_add_of_nonneg_right zero_le_one)
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hexp : 0 < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
    have hkey : x ^ (σ - 1) ≤ 1 + x ^ (b - 1) := by
      rcases le_or_gt x 1 with h1 | h1
      · have h2 : x ^ (σ - 1) ≤ 1 := by
          have hz : (0 : ℝ) ≤ σ - 1 := by linarith
          calc x ^ (σ - 1) ≤ 1 ^ (σ - 1) := Real.rpow_le_rpow hx0.le h1 hz
            _ = 1 := Real.one_rpow _
        have h3 : 0 ≤ x ^ (b - 1) := Real.rpow_nonneg hx0.le _
        linarith
      · have h2 : x ^ (σ - 1) ≤ x ^ (b - 1) :=
          Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
        linarith
    exact mul_le_mul_of_nonneg_right hkey hexp.le

/-- Three recurrence steps give quadratic decay of the Gaussian Mellin transform, with a
constant uniform in the real part of the exponent on `[1/2, 5/2]`. -/
private theorem pcsB_mellin_decay_strip (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 2 → ∀ t : ℝ,
      ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨B, hB, hBunif⟩ := pcsB_line_constant_uniform δ 7 (by norm_num)
  have hB2' : ∀ (σ : ℝ), 1 / 2 ≤ σ → σ ≤ 5 / 2 → ∀ t : ℝ,
      ‖gaussianMellin δ (((σ + 2 : ℝ)) + t * Complex.I)‖ ≤ B :=
    fun σ h1 h2 t => hBunif (σ + 2) (by linarith) (by linarith) t
  have hB3' : ∀ (σ : ℝ), 1 / 2 ≤ σ → σ ≤ 5 / 2 → ∀ t : ℝ,
      ‖gaussianMellin δ (((σ + 3 : ℝ)) + t * Complex.I)‖ ≤ B :=
    fun σ h1 h2 t => hBunif (σ + 3) (by linarith) (by linarith) t
  have hB4' : ∀ (σ : ℝ), 1 / 2 ≤ σ → σ ≤ 5 / 2 → ∀ t : ℝ,
      ‖gaussianMellin δ (((σ + 4 : ℝ)) + t * Complex.I)‖ ≤ B :=
    fun σ h1 h2 t => hBunif (σ + 4) (by linarith) (by linarith) t
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hP : 0 ≤ B + c * B + c * (B + c * B) := by
    have h1 : 0 ≤ c * B := mul_nonneg hc0 hB.le
    have h2 : 0 ≤ c * (B + c * B) :=
      mul_nonneg hc0 (by have := mul_nonneg hc0 hB.le; linarith)
    linarith
  refine ⟨4 * (B + c * B + c * (B + c * B)) + 1, by linarith,
    fun σ hσ1 hσ2 t => ?_⟩
  set a : ℂ := (σ : ℂ) + t * Complex.I with ha
  have hare : a.re = σ := by rw [ha]; simp
  have ha2 : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : a.re = σ := hare
    have h2 : a.im = t := by rw [ha]; simp
    rw [h1, h2]
    nlinarith
  have hb2 : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : (a + 1).re = σ + 1 := by rw [ha]; simp
    have h2 : (a + 1).im = t := by rw [ha]; simp
    rw [h1, h2]
    nlinarith
  have hquarter : (0 : ℝ) < (1 / 4 : ℝ) + t ^ 2 := by positivity
  have hapos : 0 < ‖a‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : a.re = 0 := by rw [h]; simp
    rw [hare] at h1
    linarith
  have hbpos : 0 < ‖a + 1‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (a + 1).re = 0 := by rw [h]; simp
    have h2 : (a + 1).re = σ + 1 := by rw [ha]; simp
    rw [h2] at h1
    linarith
  have ha1 : 0 < (a + 1).re := by rw [ha]; simp; linarith
  have ha2' : 0 < (a + 2).re := by rw [ha]; simp; linarith
  have hstep1 := pcst_mellin_step δ a (by rw [hare]; linarith)
  have hstep2 := pcst_mellin_step δ (a + 1) ha1
  have hstep3 := pcst_mellin_step δ (a + 2) ha2'
  have e2 : a + 2 = ((σ + 2 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have e3 : a + 3 = ((σ + 3 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have e4 : a + 4 = ((σ + 4 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have h3 : ‖gaussianMellin δ (a + 2)‖ * ‖a + 2‖ ≤ B + c * B := by
    have hb : ‖gaussianMellin δ ((a + 2) + 2)‖ ≤ B := by
      rw [show (a + 2) + 2 = a + 4 by ring, e4]; exact hB4' σ hσ1 hσ2 t
    have hc1 : ‖gaussianMellin δ ((a + 2) + 1)‖ ≤ B := by
      rw [show (a + 2) + 1 = a + 3 by ring, e3]; exact hB3' σ hσ1 hσ2 t
    calc ‖gaussianMellin δ (a + 2)‖ * ‖a + 2‖
        ≤ ‖gaussianMellin δ ((a + 2) + 2)‖ + c * ‖gaussianMellin δ ((a + 2) + 1)‖ := hstep3
      _ ≤ B + c * B := by
          refine add_le_add hb (mul_le_mul_of_nonneg_left hc1 hc0)
  have h2 : ‖gaussianMellin δ (a + 1)‖ * ‖a + 1‖ ≤ B + c * B := by
    have hb : ‖gaussianMellin δ ((a + 1) + 2)‖ ≤ B := by
      rw [show (a + 1) + 2 = a + 3 by ring, e3]; exact hB3' σ hσ1 hσ2 t
    have hc1 : ‖gaussianMellin δ ((a + 1) + 1)‖ ≤ B := by
      rw [show (a + 1) + 1 = a + 2 by ring, e2]; exact hB2' σ hσ1 hσ2 t
    calc ‖gaussianMellin δ (a + 1)‖ * ‖a + 1‖
        ≤ ‖gaussianMellin δ ((a + 1) + 2)‖ + c * ‖gaussianMellin δ ((a + 1) + 1)‖ := hstep2
      _ ≤ B + c * B := by
          refine add_le_add hb (mul_le_mul_of_nonneg_left hc1 hc0)
  have h2pos : 0 < ‖a + 2‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (a + 2).re = 0 := by rw [h]; simp
    linarith
  have hquot2 : ‖gaussianMellin δ (a + 2)‖ ≤ (B + c * B) / ‖a + 2‖ := by
    rw [le_div_iff₀ h2pos]
    linarith [h3]
  have hquot1 : ‖gaussianMellin δ (a + 1)‖ ≤ (B + c * B) / ‖a + 1‖ := by
    rw [le_div_iff₀ hbpos]
    linarith [h2]
  have hle : ‖a + 1‖ ≤ ‖a + 2‖ := by
    have hn1 : Complex.normSq (a + 1) = (σ + 1) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply]
      have h1 : (a + 1).re = σ + 1 := by rw [ha]; simp
      have h2 : (a + 1).im = t := by rw [ha]; simp
      rw [h1, h2]; ring
    have hn2 : Complex.normSq (a + 2) = (σ + 2) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply]
      have h1 : (a + 2).re = σ + 2 := by rw [ha]; simp
      have h2 : (a + 2).im = t := by rw [ha]; simp
      rw [h1, h2]; ring
    rw [show ‖a + 1‖ = Real.sqrt (Complex.normSq (a + 1)) by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
      show ‖a + 2‖ = Real.sqrt (Complex.normSq (a + 2)) by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
    apply Real.sqrt_le_sqrt
    rw [hn1, hn2]
    nlinarith
  have hsum : ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖ ≤
      B + c * B + c * (B + c * B) := by
    have hb1 : (B + c * B) / ‖a + 2‖ ≤ (B + c * B) / ‖a + 1‖ := by
      have hnum : (0 : ℝ) ≤ B + c * B := by
        have := mul_nonneg hc0 hB.le; linarith [hB.le]
      exact div_le_div_of_nonneg_left hnum hbpos hle
    have hmid : ‖gaussianMellin δ a‖ * ‖a‖ ≤
        (B + c * B + c * (B + c * B)) / ‖a + 1‖ := by
      have hb2' : c * ((B + c * B) / ‖a + 1‖) = c * (B + c * B) / ‖a + 1‖ := by ring
      calc ‖gaussianMellin δ a‖ * ‖a‖
          ≤ ‖gaussianMellin δ (a + 2)‖ + c * ‖gaussianMellin δ (a + 1)‖ := hstep1
        _ ≤ (B + c * B) / ‖a + 2‖ + c * ((B + c * B) / ‖a + 1‖) := by
            refine add_le_add hquot2 (mul_le_mul_of_nonneg_left hquot1 hc0)
        _ ≤ (B + c * B) / ‖a + 1‖ + c * (B + c * B) / ‖a + 1‖ := by
            rw [hb2']
            exact add_le_add hb1 le_rfl
        _ = (B + c * B + c * (B + c * B)) / ‖a + 1‖ := by ring
    calc ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖
        ≤ ((B + c * B + c * (B + c * B)) / ‖a + 1‖) * ‖a + 1‖ :=
          mul_le_mul_of_nonneg_right hmid hbpos.le
      _ = B + c * B + c * (B + c * B) := by field_simp
  have hmain : ‖gaussianMellin δ a‖ ≤
      (B + c * B + c * (B + c * B)) / (‖a‖ * ‖a + 1‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖a‖ * ‖a + 1‖)]
    calc ‖gaussianMellin δ a‖ * (‖a‖ * ‖a + 1‖) =
        ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖ := by ring
      _ ≤ _ := hsum
  have hden : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a‖ * ‖a + 1‖ := by
    have h1 : 0 ≤ ‖a‖ := norm_nonneg _
    have h2 : 0 ≤ ‖a + 1‖ := norm_nonneg _
    nlinarith [ha2, hb2]
  have hfin : ‖gaussianMellin δ a‖ ≤
      (B + c * B + c * (B + c * B)) / ((1 / 4 : ℝ) + t ^ 2) :=
    hmain.trans (div_le_div_of_nonneg_left hP hquarter hden)
  have hfour : (B + c * B + c * (B + c * B)) / ((1 / 4 : ℝ) + t ^ 2) ≤
      (4 * (B + c * B + c * (B + c * B)) + 1) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hquarter (by positivity : (0 : ℝ) < 1 + t ^ 2)]
    nlinarith [hP]
  simpa [ha] using hfin.trans hfour


/-- Quadratic decay of the continued Gaussian kernel on the rectangle `[-1/2, 2] × ℝ`, away
from the origin. -/
private theorem pcsB_cont_decay_strip (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, -(1 / 2) ≤ σ → σ ≤ 2 → ∀ t : ℝ, 1 ≤ |t| →
      ‖continuedGaussian δ ((σ : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨K1, hK1, hK1'⟩ := pcsB_mellin_decay_strip δ
  obtain ⟨K0, hK0, hK0'⟩ := pcst_mellin_decay_half δ (1 / 2) le_rfl
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  refine ⟨(K1 + c * K1) + K0 + 1, by positivity, fun σ h1 h2 t ht => ?_⟩
  rcases le_or_gt (1 / 2) σ with hs | hs
  · rw [Continuation457.continuedGaussian_eq δ _ (by simp; linarith)]
    have h1 : ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ K1 / (1 + t ^ 2) :=
      hK1' σ hs (by linarith) t
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    refine h1.trans ?_
    apply div_le_div_of_nonneg_right _ hden.le
    have hc1 : 0 ≤ c * K1 := mul_nonneg hc0 hK1.le
    linarith
  · -- `-1/2 ≤ σ < 1/2`: divide the recurrence by `s`, with `‖s‖ ≥ |t| ≥ 1`
    have hre1 : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have hnum := pcsB_cont_mul δ (s := (σ : ℂ) + t * Complex.I) (by
      intro h
      have him := congrArg Complex.im h
      simp at him
      have hz : |t| = 0 := by rw [him]; simp
      linarith)
    set s : ℂ := (σ : ℂ) + t * Complex.I with hsd
    have hsre : s.re = σ := by rw [hsd]; simp
    have hsim : s.im = t := by rw [hsd]; simp
    have hsnorm : 1 ≤ ‖s‖ := by
      have h1 : |t| ≤ ‖s‖ := by
        rw [← hsim]
        exact Complex.abs_im_le_norm s
      linarith
    have e1 : s + 1 = ((σ + 1 : ℝ) : ℂ) + t * Complex.I := by rw [hsd]; push_cast; ring
    have e2 : s + 2 = ((σ + 2 : ℝ) : ℂ) + t * Complex.I := by rw [hsd]; push_cast; ring
    have hb1 : ‖gaussianMellin δ (s + 1)‖ ≤ K1 / (1 + t ^ 2) := by
      rw [e1]
      exact hK1' (σ + 1) (by linarith) (by linarith) t
    have hb2 : ‖gaussianMellin δ (s + 2)‖ ≤ K1 / (1 + t ^ 2) := by
      rw [e2]
      exact hK1' (σ + 2) (by linarith) (by linarith) t
    have hnumle : ‖gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ ≤ (K1 + c * K1) / (1 + t ^ 2) := by
      calc ‖gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖
          ≤ ‖gaussianMellin δ (s + 2)‖ +
              ‖(2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
        _ = ‖gaussianMellin δ (s + 2)‖ + c * ‖gaussianMellin δ (s + 1)‖ := by
            rw [norm_mul, hc]
        _ ≤ K1 / (1 + t ^ 2) + c * (K1 / (1 + t ^ 2)) := by
            exact add_le_add hb2 (mul_le_mul_of_nonneg_left hb1 hc0)
        _ = (K1 + c * K1) / (1 + t ^ 2) := by ring
    have hun : continuedGaussian δ s =
        (gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) / s :=
      rfl
    have hspos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hsnorm
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hmul : ‖continuedGaussian δ s‖ ≤ ((K1 + c * K1) / (1 + t ^ 2)) / ‖s‖ := by
      rw [hun, norm_div]
      exact div_le_div_of_nonneg_right hnumle (norm_nonneg _)
    have hfin : ((K1 + c * K1) / (1 + t ^ 2)) / ‖s‖ ≤
        ((K1 + c * K1) + K0 + 1) / (1 + t ^ 2) := by
      have h1 : ((K1 + c * K1) / (1 + t ^ 2)) / ‖s‖ ≤
          ((K1 + c * K1) / (1 + t ^ 2)) / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hsnorm
      have h2 : (K1 + c * K1) / (1 + t ^ 2) ≤ ((K1 + c * K1) + K0 + 1) / (1 + t ^ 2) := by
        apply div_le_div_of_nonneg_right _ hden.le
        linarith
      calc ((K1 + c * K1) / (1 + t ^ 2)) / ‖s‖ ≤ ((K1 + c * K1) / (1 + t ^ 2)) / 1 := h1
        _ = (K1 + c * K1) / (1 + t ^ 2) := by ring
        _ ≤ ((K1 + c * K1) + K0 + 1) / (1 + t ^ 2) := h2
    simpa [hsd] using hmul.trans hfin


/-! #### F6. The two horizontal pieces are small at a good height -/

/-- A uniform bound on the two horizontal pieces: on the segment the logarithmic derivative is
at most `B` and the kernel decays like `(1 + |y| ^ 2)⁻¹`, while the scale factor is at most
`x ^ 2`. -/
private theorem pcsB_horiz_bound {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (y B : ℝ), 1 ≤ |y| → 0 ≤ B →
      (∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
        ‖logDeriv riemannZeta ((σ : ℂ) + y * Complex.I)‖ ≤ B) →
      ‖∫ σ in (-1 / 2 : ℝ)..2,
        -(deriv riemannZeta ((σ : ℂ) + y * Complex.I) /
            riemannZeta ((σ : ℂ) + y * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + y * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + y * Complex.I))‖ ≤
        5 / 2 * (K * B * x ^ 2 / (1 + y ^ 2)) := by
  obtain ⟨K, hK, hKdec⟩ := pcsB_cont_decay_strip δ
  refine ⟨K, hK, fun y B hy hB0 hB => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hden : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hb : ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
      ‖-(deriv riemannZeta ((σ : ℂ) + y * Complex.I) /
            riemannZeta ((σ : ℂ) + y * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + y * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + y * Complex.I))‖ ≤
        B * (K / (1 + y ^ 2)) * x ^ 2 := by
    intro σ hσ
    have hσ1 : -(1 / 2 : ℝ) ≤ σ := hσ.1
    have hσ2 : σ ≤ 2 := hσ.2
    have hlogd := hB σ hσ
    have hkern := hKdec σ hσ1 hσ2 y hy
    have hpow : ‖(x : ℂ) ^ ((σ : ℂ) + y * Complex.I)‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    have hpowle : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ2
    rw [show x ^ (2 : ℝ) = x ^ 2 by rw [Real.rpow_two]] at hpowle
    have hkern0 : 0 ≤ K / (1 + y ^ 2) := by positivity
    rw [norm_mul, norm_mul, norm_neg, hpow]
    have hGG : ‖continuedGaussian δ ((σ : ℂ) + y * Complex.I)‖ * x ^ σ ≤
        (K / (1 + y ^ 2)) * x ^ 2 :=
      mul_le_mul hkern hpowle (Real.rpow_nonneg hx0.le _) hkern0
    have hstep : ‖logDeriv riemannZeta ((σ : ℂ) + y * Complex.I)‖ *
        (‖continuedGaussian δ ((σ : ℂ) + y * Complex.I)‖ * x ^ σ) ≤
        B * ((K / (1 + y ^ 2)) * x ^ 2) :=
      mul_le_mul hlogd hGG (by positivity) hB0
    calc ‖deriv riemannZeta ((σ : ℂ) + y * Complex.I) /
          riemannZeta ((σ : ℂ) + y * Complex.I)‖ *
        (‖continuedGaussian δ ((σ : ℂ) + y * Complex.I)‖ * x ^ σ)
        ≤ B * ((K / (1 + y ^ 2)) * x ^ 2) := hstep
      _ = B * (K / (1 + y ^ 2)) * x ^ 2 := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => -(deriv riemannZeta ((σ : ℂ) + y * Complex.I) /
            riemannZeta ((σ : ℂ) + y * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + y * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + y * Complex.I)))
    (C := B * (K / (1 + y ^ 2)) * x ^ 2) (fun σ hσ => by
      rw [uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 2)] at hσ
      exact hb σ ⟨hσ.1.le, hσ.2⟩)
  have hlen : |(2 : ℝ) - -(1 / 2)| = 5 / 2 := by
    rw [show (2 : ℝ) - -(1 / 2) = 5 / 2 by norm_num, abs_of_pos (by norm_num)]
  rw [hlen] at hint
  have heq : B * (K / (1 + y ^ 2)) * x ^ 2 * (5 / 2) =
      5 / 2 * (K * B * x ^ 2 / (1 + y ^ 2)) := by
    rw [div_eq_mul_inv]
    ring
  rw [heq] at hint
  simpa only [neg_div] using hint

/-! #### F7. The horizontal pieces vanish at the good heights -/

/-- `log ^ 2 T / T ^ 2` tends to zero. -/
private theorem pcsB_log_sq_div_tendsto :
    Tendsto (fun T : ℝ => Real.log T ^ 2 / T ^ 2) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    have h := isLittleO_log_rpow_atTop (r := 1) (by norm_num : (0 : ℝ) < 1)
    have h2 := h.tendsto_div_nhds_zero
    simpa [Real.rpow_one] using h2
  have h2 := hlogdiv.pow 2
  simpa [div_pow] using h2

/-- At a good height the horizontal pieces vanish: there the logarithmic derivative is
`C log² T` and the kernel contributes only `(1 + y ^ 2)⁻¹` with `y ≥ T`. -/
private theorem pcsB_horiz_tendsto {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {C : ℝ} (hC : 0 ≤ C)
    {y : ℝ → ℝ} (hy : ∀ T : ℝ, 5 ≤ T → y T ∈ Set.Icc T (T + 1))
    (hBy : ∀ T : ℝ, 5 ≤ T → ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
      ‖logDeriv riemannZeta ((σ : ℂ) + y T * Complex.I)‖ ≤ C * Real.log T ^ 2) :
    Tendsto (fun T : ℝ => ∫ σ in (-1 / 2 : ℝ)..2,
        -(deriv riemannZeta ((σ : ℂ) + y T * Complex.I) /
            riemannZeta ((σ : ℂ) + y T * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + y T * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + y T * Complex.I)))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := pcsB_horiz_bound hx δ
  have hx0 : (0 : ℝ) < x := by linarith
  have hA0 : 0 ≤ 5 / 2 * K * C * x ^ 2 := by positivity
  have hev : ∀ᶠ T in atTop, ‖∫ σ in (-1 / 2 : ℝ)..2,
        -(deriv riemannZeta ((σ : ℂ) + y T * Complex.I) /
            riemannZeta ((σ : ℂ) + y T * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + y T * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + y T * Complex.I))‖ ≤
      (5 / 2 * K * C * x ^ 2) * (Real.log T ^ 2 / T ^ 2) := by
    filter_upwards [eventually_ge_atTop (5 : ℝ)] with T hT
    have hyI := hy T hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hy1 : 1 ≤ |y T| := by
      have h1 : T ≤ |y T| := le_trans hyI.1 (le_abs_self _)
      linarith
    have hlog2 : 0 ≤ Real.log T ^ 2 := sq_nonneg _
    have hB0 : 0 ≤ C * Real.log T ^ 2 := mul_nonneg hC hlog2
    have hb := hbound (y T) (C * Real.log T ^ 2) hy1 hB0 (hBy T hT)
    refine hb.trans ?_
    have hyl : T ^ 2 ≤ (y T) ^ 2 := by nlinarith [hyI.1, hyI.2, hT0.le]
    have hden : (0 : ℝ) < 1 + (y T) ^ 2 := by positivity
    have hT2 : (0 : ℝ) < T ^ 2 := by positivity
    have key : 5 / 2 * (K * (C * Real.log T ^ 2) * x ^ 2 / (1 + (y T) ^ 2)) =
        (5 / 2 * K * C * x ^ 2) * (Real.log T ^ 2 / (1 + (y T) ^ 2)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [key]
    refine mul_le_mul_of_nonneg_left ?_ hA0
    exact div_le_div_of_nonneg_left hlog2 hT2 (by linarith)
  have hlim : Tendsto (fun T : ℝ =>
      (5 / 2 * K * C * x ^ 2) * (Real.log T ^ 2 / T ^ 2)) atTop (𝓝 0) := by
    have h := pcsB_log_sq_div_tendsto.const_mul (5 / 2 * K * C * x ^ 2)
    simpa using h
  exact squeeze_zero_norm' hev hlim

/-! #### F8. The rectangle integral splits into the two vertical and the two horizontal pieces -/

/-- The normalized rectangle integral of a function over `[-1/2, 2] × [-T, T]` is the
difference of the two vertical pieces plus the two horizontal ones.  The integrand arguments
are written with real casts, so that they are the ones `RectangleIntegral'` unfolds to. -/
private theorem pcsB_rect_decomp (F : ℂ → ℂ) (T : ℝ) :
    RectangleIntegral' F (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ =
      (1 / (2 * π) : ℂ) *
        ((∫ t in (-T)..T, F (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
         ∫ t in (-T)..T, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
      (1 / (2 * π * Complex.I) : ℂ) *
        ((∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
         ∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) := by
  rw [RectangleIntegral', RectangleIntegral]
  simp only [HIntegral, VIntegral, smul_eq_mul]
  set A : ℂ := ∫ x in (-1 / 2 : ℝ)..2, F ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) with hA
  set B : ℂ := ∫ x in (-1 / 2 : ℝ)..2, F ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) with hB
  set P : ℂ := ∫ y in (-T)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) with hP
  set Q : ℂ := ∫ y in (-T)..T, F (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) with hQ
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  have hπ : (2 * ((π : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hpi : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have key : (1 / (2 * ((π : ℝ) : ℂ) * Complex.I)) * (A - B + Complex.I * P - Complex.I * Q) =
      (1 / (2 * ((π : ℝ) : ℂ))) * (P - Q) +
        (1 / (2 * ((π : ℝ) : ℂ) * Complex.I)) * (A - B) := by
    field_simp
    ring
  exact key

/-! #### F9. Quadratic decay of the Mellin transform inside the strip -/

/-- On the open critical strip, away from the real axis, the Gaussian Mellin transform decays
quadratically: above `Re s = 1/2` this is `pcsB_mellin_decay_strip`, and below it a single
recurrence step divides by `|s| ≥ |Im s| ≥ 1`. -/
private theorem pcsB_mellin_decay_strip_full (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → 1 ≤ |ρ.im| →
      ‖gaussianMellin δ ρ‖ ≤ K / (1 + ρ.im ^ 2) := by
  obtain ⟨K1, hK1, hK1'⟩ := pcsB_mellin_decay_strip δ
  refine ⟨K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1 + 1, by positivity, ?_⟩
  intro ρ hρ0 hρ1 him
  have hden : (0 : ℝ) < 1 + ρ.im ^ 2 := by positivity
  have hc0 : 0 ≤ ‖(2 * π * Complex.I * δ : ℂ)‖ := norm_nonneg _
  have htarget : K1 / (1 + ρ.im ^ 2) ≤
      (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1 + 1) / (1 + ρ.im ^ 2) := by
    apply div_le_div_of_nonneg_right _ hden.le
    have h2 : 0 ≤ ‖(2 * π * Complex.I * δ : ℂ)‖ * K1 := mul_nonneg hc0 hK1.le
    linarith
  rcases le_or_gt (1 / 2) ρ.re with hs | hs
  · have h1 : ‖gaussianMellin δ (((ρ.re : ℝ) : ℂ) + ρ.im * Complex.I)‖ ≤
        K1 / (1 + ρ.im ^ 2) := hK1' ρ.re hs (by linarith) ρ.im
    have heq : ((ρ.re : ℝ) : ℂ) + ρ.im * Complex.I = ρ := by
      apply Complex.ext <;> simp
    rw [heq] at h1
    exact h1.trans htarget
  · have hρnorm : 1 ≤ ‖ρ‖ := by
      have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
      linarith
    have hstep := pcst_mellin_step δ ρ hρ0
    have e1 : ρ + 1 = (((ρ.re + 1) : ℝ) : ℂ) + ρ.im * Complex.I := by
      apply Complex.ext <;> simp
    have e2 : ρ + 2 = (((ρ.re + 2) : ℝ) : ℂ) + ρ.im * Complex.I := by
      apply Complex.ext <;> simp
    have hb1 : ‖gaussianMellin δ (ρ + 1)‖ ≤ K1 / (1 + ρ.im ^ 2) := by
      rw [e1]
      exact hK1' (ρ.re + 1) (by linarith) (by linarith) ρ.im
    have hb2 : ‖gaussianMellin δ (ρ + 2)‖ ≤ K1 / (1 + ρ.im ^ 2) := by
      rw [e2]
      exact hK1' (ρ.re + 2) (by linarith) (by linarith) ρ.im
    have hnum : ‖gaussianMellin δ ρ‖ * ‖ρ‖ ≤
        (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2) := by
      have h1 : ‖gaussianMellin δ (ρ + 2)‖ + ‖(2 * π * Complex.I * δ : ℂ)‖ *
          ‖gaussianMellin δ (ρ + 1)‖ ≤
          K1 / (1 + ρ.im ^ 2) + ‖(2 * π * Complex.I * δ : ℂ)‖ * (K1 / (1 + ρ.im ^ 2)) :=
        add_le_add hb2 (mul_le_mul_of_nonneg_left hb1 hc0)
      have h2 : K1 / (1 + ρ.im ^ 2) + ‖(2 * π * Complex.I * δ : ℂ)‖ *
          (K1 / (1 + ρ.im ^ 2)) =
          (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2) := by
        rw [← mul_div_assoc, ← add_div]
      exact hstep.trans (h1.trans (le_of_eq h2))
    have hmul : ‖gaussianMellin δ ρ‖ ≤
        ((K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2)) / ‖ρ‖ := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖ρ‖)]
      exact hnum
    have hfin : ((K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2)) / ‖ρ‖ ≤
        (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1 + 1) / (1 + ρ.im ^ 2) := by
      have h1 : ((K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2)) / ‖ρ‖ ≤
          (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2) := by
        calc ((K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2)) / ‖ρ‖
            ≤ ((K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2)) / 1 := by
              exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hρnorm
          _ = (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2) := by ring
      have h2 : (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1) / (1 + ρ.im ^ 2) ≤
          (K1 + ‖(2 * π * Complex.I * δ : ℂ)‖ * K1 + 1) / (1 + ρ.im ^ 2) := by
        apply div_le_div_of_nonneg_right _ hden.le
        linarith
      exact h1.trans h2
    exact hmul.trans hfin


end

/-! #### F10. The line of real part minus one half: truncation limit and value -/

/-- The integrand of the shift on the line of real part minus one half is integrable once the
`L`-function is that of zeta. -/
private theorem pcsB_half_line_integrable_zeta {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Integrable (fun t : ℝ =>
      logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        (continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I))) := by
  have hD := principal_half_line_integrable x hx 1 (1 : DirichletCharacter ℂ 1) δ
  refine hD.congr ?_
  filter_upwards with t
  simp only [DirichletCharacter.LFunction_modOne_eq]
  ring

/-- The truncated integrals of the shift integrand on the line of real part minus one half
converge to the full-line integral. -/
private theorem pcsB_half_line_tendsto {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
      logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        (continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)))
      atTop (𝓝 (∫ t : ℝ,
      logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        (continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)))) :=
  intervalIntegral_tendsto_integral (pcsB_half_line_integrable_zeta hx δ)
    tendsto_neg_atTop_atBot tendsto_id

/-- **The value of the line of real part minus one half.** The normalized truncated integrals of
the shift integrand on that line converge to the principal contour. -/
private theorem pcsB_half_line_value {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Tendsto (fun T : ℝ => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
      logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        (continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)))
      atTop (𝓝 (principalContour δ x)) := by
  have hC := principal_half_line_conductor_one x hx 1 (1 : DirichletCharacter ℂ 1) δ rfl
  have hfun : (fun t : ℝ => logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        (continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)))
      = fun t : ℝ => logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
          ((-1 / 2 : ℂ) + t * Complex.I) * continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
            (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := by
    funext t
    simp only [DirichletCharacter.LFunction_modOne_eq]
    ring
  have hval : (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        (continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) = principalContour δ x := by
    rw [hfun]
    exact hC
  have hT := (pcsB_half_line_tendsto hx δ).const_mul (1 / (2 * π) : ℂ)
  rw [hval] at hT
  exact hT

/-! #### F11. The zeros of zeta in the strip: summability, and the split at a height -/

/-- One zero term is dominated by the convergent zero weight `m(ρ)/‖ρ (ρ + 1)‖`. -/
private theorem pcsB_zeroTerm_norm_le {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → 1 ≤ |ρ.im| →
      ‖gaussianMellin δ ρ‖ ≤ K / (1 + ρ.im ^ 2))
    {ρ : ℂ} (h1 : 0 < ρ.re) (h2 : ρ.re < 1) (him : 1 ≤ |ρ.im|) :
    ‖zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ‖ ≤
      2 * K * x * LeanLab.PNTPort.ExplicitPsi1.hw ρ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hden : (0 : ℝ) < 1 + ρ.im ^ 2 := by positivity
  have hG : ‖gaussianMellin δ ρ‖ ≤ K / (1 + ρ.im ^ 2) := hK ρ h1 h2 him
  have hpow : ‖(x : ℂ) ^ ρ‖ ≤ x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    calc x ^ ρ.re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h2.le
      _ = x := Real.rpow_one x
  have hnormz : ‖gaussianMellin δ ρ * (x : ℂ) ^ ρ‖ ≤ K * x / (1 + ρ.im ^ 2) := by
    rw [norm_mul]
    calc ‖gaussianMellin δ ρ‖ * ‖(x : ℂ) ^ ρ‖ ≤ (K / (1 + ρ.im ^ 2)) * x :=
          mul_le_mul hG hpow (norm_nonneg _) (div_nonneg hK0 hden.le)
      _ = K * x / (1 + ρ.im ^ 2) := by ring
  -- the scale comparison `‖ρ (ρ + 1)‖ ≤ 2 (1 + im ^ 2)`
  have hquad : ‖ρ * (ρ + 1)‖ ≤ 2 * (1 + ρ.im ^ 2) := by
    have hsq1 : ‖ρ‖ ^ 2 ≤ 1 + ρ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [mul_pos h1 h1]
    have hsq2 : ‖ρ + 1‖ ^ 2 ≤ 4 + ρ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre1 : (ρ + 1).re = ρ.re + 1 := by simp
      have him1 : (ρ + 1).im = ρ.im := by simp
      rw [hre1, him1]
      nlinarith [mul_pos h1 h1]
    have hpos1 : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
    have hpos2 : (0 : ℝ) ≤ ‖ρ + 1‖ := norm_nonneg _
    have hfac : (1 + ρ.im ^ 2) * (4 + ρ.im ^ 2) ≤ (2 * (1 + ρ.im ^ 2)) ^ 2 := by
      nlinarith [sq_nonneg ρ.im]
    have hsq : ‖ρ * (ρ + 1)‖ ^ 2 ≤ (2 * (1 + ρ.im ^ 2)) ^ 2 := by
      rw [norm_mul, mul_pow]
      nlinarith [hsq1, hsq2, hpos1, hpos2, mul_nonneg hpos1 hpos2]
    nlinarith [norm_nonneg (ρ * (ρ + 1)), hsq]
  have hrp : ρ ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  have hrp1 : ρ + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hnormpos : (0 : ℝ) < ‖ρ * (ρ + 1)‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero hrp hrp1
  have hm0 : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
  have hinv : 1 / (1 + ρ.im ^ 2) ≤ 2 / ‖ρ * (ρ + 1)‖ := by
    rw [div_le_div_iff₀ hden hnormpos]
    nlinarith [hquad]
  calc ‖zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ‖
      = (analyticOrderNatAt riemannZeta ρ : ℝ) *
          ‖gaussianMellin δ ρ * (x : ℂ) ^ ρ‖ := by
        rw [zeroTerm, DirichletCharacter.LFunction_modOne_eq, nsmul_eq_mul, norm_mul,
          Complex.norm_natCast]
    _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (K * x / (1 + ρ.im ^ 2)) :=
        mul_le_mul_of_nonneg_left hnormz hm0
    _ = ((analyticOrderNatAt riemannZeta ρ : ℝ) * (K * x)) * (1 / (1 + ρ.im ^ 2)) := by
        ring
    _ ≤ ((analyticOrderNatAt riemannZeta ρ : ℝ) * (K * x)) * (2 / ‖ρ * (ρ + 1)‖) := by
        exact mul_le_mul_of_nonneg_left hinv (mul_nonneg hm0 (mul_nonneg hK0 (le_of_lt hx0)))
    _ = 2 * K * x * LeanLab.PNTPort.ExplicitPsi1.hw ρ := by
        rw [LeanLab.PNTPort.ExplicitPsi1.hw]
        field_simp

set_option maxHeartbeats 20000000 in
/-- The zero terms of the strip zeros of zeta are summable. -/
private theorem pcsB_zeroTerm_summable {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
      zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val) := by
  obtain ⟨K, hK0, hK⟩ := pcsB_mellin_decay_strip_full δ
  have hhw : Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
      LeanLab.PNTPort.ExplicitPsi1.hw ρ.val) := by
    have hinj : Function.Injective
        (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
          (⟨ρ.val, ρ.2.1, by linarith [ρ.2.2.1]⟩ : LeanLab.PNTPort.ExplicitPsi1.Zall)) := by
      intro a b h
      exact Subtype.ext (congrArg (fun z : LeanLab.PNTPort.ExplicitPsi1.Zall => (z : ℂ)) h)
    have hcomp := LeanLab.PNTPort.ExplicitPsi1.summable_hw.comp_injective
      (f := fun ρ : LeanLab.PNTPort.ExplicitPsi1.Zall => LeanLab.PNTPort.ExplicitPsi1.hw ρ)
      (i := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
        (⟨ρ.val, ρ.2.1, by linarith [ρ.2.2.1]⟩ : LeanLab.PNTPort.ExplicitPsi1.Zall)) hinj
    exact hcomp
  have hfin : ({ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} |
      |ρ.val.im| ≤ 1} : Set {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}).Finite := by
    refine Set.Finite.of_finite_image
      (f := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} => (ρ.val : ℂ)) ?_
      (fun a _ b _ h => Subtype.ext h)
    refine Set.Finite.subset (pcsB_zeros_rect_finite 1) ?_
    rintro z ⟨ρ, hρ, rfl⟩
    simp only [Set.mem_setOf_eq] at hρ
    refine ⟨?_, ρ.2.1⟩
    rw [pcsB_mem_rect (T := 1) (by norm_num)]
    have hab := abs_le.mp hρ
    exact ⟨⟨by linarith [ρ.2.2.1], by linarith [ρ.2.2.2]⟩, hab⟩
  have h1 : Summable (fun ρ : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} |
      |ρ.val.im| ≤ 1} => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val.val) := by
    haveI := hfin.to_subtype
    exact Summable.of_finite
  have h2 : Summable (fun ρ : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} |
      ¬ |ρ.val.im| ≤ 1} => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val.val) := by
    refine Summable.of_norm_bounded (g := fun ρ : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1} | ¬ |ρ.val.im| ≤ 1} =>
        (2 * K * x) * LeanLab.PNTPort.ExplicitPsi1.hw ρ.val.val) ?_ ?_
    · exact (hhw.mul_left (2 * K * x)).subtype _
    · intro ρ
      exact pcsB_zeroTerm_norm_le hx δ hK0.le hK ρ.val.2.2.1 ρ.val.2.2.2
        (by have := not_le.mp ρ.2; linarith)
  exact Summable.add_compl h1 h2


/-- The `L`-function of the trivial character vanishes exactly where zeta does. -/
private theorem pcsB_LFunction_one_eq_zero {ρ : ℂ} :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ↔ riemannZeta ρ = 0 := by
  rw [DirichletCharacter.LFunction_modOne_eq]

/-- A zero of zeta inside the rectangle `[-1/2, 2] × [-T, T]` is a strip zero of height at most
`T`, and conversely. -/
private lemma pcsB_rect_zero_iff {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ} :
    (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ↔
      ρ ∈ (pcsB_zeros_rect_finite T).toFinset := by
  have hmem := fun z => pcsB_mem_rect (T := T) hT (z := z)
  constructor
  · rintro ⟨hz, h1, h2, hi⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨(hmem ρ).mpr ⟨⟨by linarith, by linarith⟩, abs_le.mp hi⟩, hz⟩
  · intro hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨hR, hz⟩ := hρ
    obtain ⟨hre, him⟩ := (hmem ρ).mp hR
    refine ⟨hz, ?_, ?_, ?_⟩
    · rcases eq_or_ne ρ.im 0 with h0 | h0
      · have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := by
          apply Complex.ext
          · simp
          · simpa using h0
        rcases lt_or_ge ρ.re 0 with hlt | hge
        · exact absurd (by rw [← hρeq]; exact hz)
            (pcsB_zeta_ne_zero_of_real_nonpos (by linarith) hlt)
        · -- `0 ≤ ρ.re`; only the value zero itself is a real zero of zeta there
          have hne : ρ.re ≠ 0 := by
            intro h0re
            have hρ0 : ρ = 0 := by rw [hρeq, h0re]; norm_num
            have hzρ : riemannZeta ρ = 0 := mem_riemannZetaZeros.mp hz
            have hz0 : riemannZeta (0 : ℂ) = 0 := by rwa [hρ0] at hzρ
            rw [riemannZeta_zero] at hz0
            norm_num at hz0
          exact lt_of_le_of_ne hge hne.symm
      · by_contra hpos
        push_neg at hpos
        exact LeanLab.PNTPort.ZetaZeros.zeta_ne_zero_of_re_nonpos hpos h0 hz
    · by_contra h
      push_neg at h
      exact riemannZeta_ne_zero_of_one_le_re h hz
    · exact abs_le.mpr ⟨by linarith [him.1], him.2⟩

/-- The sum over the zeros of zeta in the rectangle is the low zero sum. -/
private theorem pcsB_rect_finset_sum {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∑ ρ ∈ (pcsB_zeros_rect_finite T).toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (gaussianMellin δ ρ * (x : ℂ) ^ ρ) =
      lowZeros (1 : DirichletCharacter ℂ 1) δ x T := by
  have h1 : lowZeros (1 : DirichletCharacter ℂ 1) δ x T =
      ∑' ρ : {ρ : ℂ // ρ ∈ (pcsB_zeros_rect_finite T).toFinset},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val := by
    rw [lowZeros]
    refine (tsum_congr_subtype (f := fun ρ : ℂ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ)
      (P := fun ρ : ℂ => DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (Q := fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (fun ρ => by simp only [pcsB_LFunction_one_eq_zero])).trans ?_
    exact tsum_congr_subtype _ (fun ρ => pcsB_rect_zero_iff hT)
  rw [h1, Finset.tsum_subtype]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  simp only [zeroTerm, DirichletCharacter.LFunction_modOne_eq]
  rw [nsmul_eq_mul]

/-- The strip zeros of zeta of height at most `T`, `T ≥ 0`, are finitely many. -/
private theorem pcsB_stripZeros_finite_nonneg (T : ℝ) (hT : 0 ≤ T) :
    ({ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} | |ρ.val.im| ≤ T} :
      Set {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}).Finite := by
  refine Set.Finite.of_finite_image
    (s := {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} | |ρ.val.im| ≤ T})
    (f := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} => (ρ.val : ℂ)) ?_ ?_
  · refine Set.Finite.subset (pcsB_zeros_rect_finite T) ?_
    rintro z ⟨ρ, hρ, rfl⟩
    simp only [Set.mem_setOf_eq] at hρ
    refine ⟨?_, ρ.2.1⟩
    rw [pcsB_mem_rect (T := T) hT]
    have hab := abs_le.mp hρ
    exact ⟨⟨by linarith [ρ.2.2.1], by linarith [ρ.2.2.2]⟩, hab⟩
  · intro a _ b _ h
    exact Subtype.ext h

/-- The strip zeros of zeta of height at most `T` are finitely many, for any `T`. -/
private theorem pcsB_stripZeros_finite (T : ℝ) :
    ({ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} | |ρ.val.im| ≤ T} :
      Set {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}).Finite :=
  Set.Finite.subset (pcsB_stripZeros_finite_nonneg (max T 0) (le_max_right _ _)) fun ρ hρ =>
    show |ρ.val.im| ≤ max T 0 from le_trans hρ (le_max_left _ _)

/-- The strip zeros of zeta below a growing height exhaust all strip zeros. -/
private theorem pcsB_stripZeros_finset_tendsto :
    Tendsto (fun T : ℝ => (pcsB_stripZeros_finite T).toFinset) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun s =>
    ⟨max (s.sum fun ρ => |ρ.val.im|) 0, fun T hT ρ hρ => ?_⟩
  rw [Set.Finite.mem_toFinset]
  refine le_trans (Finset.single_le_sum (f := fun ρ =>
    |ρ.val.im|) (fun i _ => abs_nonneg _) hρ) ?_
  exact le_trans (le_max_left _ _) hT

/-- The high zero sum is the sum over the complement of the finitely many low zeros. -/
private theorem pcsB_high_eq_compl {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) (T : ℝ) :
    highZeros (1 : DirichletCharacter ℂ 1) δ x T =
      ∑' ρ : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} |
          ¬ |ρ.val.im| ≤ T},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val.val := by
  rw [highZeros]
  refine (tsum_congr_subtype (f := fun ρ : ℂ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ)
    (P := fun ρ : ℂ => DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|)
    (Q := fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|)
    (fun ρ => by simp only [pcsB_LFunction_one_eq_zero])).trans ?_
  refine (tsum_congr_subtype (f := fun ρ : ℂ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ)
    (P := fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|)
    (Q := fun ρ : ℂ => (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ∧ T < |ρ.im|)
    (fun ρ => by tauto)).trans ?_
  refine (tsum_congr_subtype (f := fun ρ : ℂ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ)
    (P := fun ρ : ℂ => (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ∧ T < |ρ.im|)
    (Q := fun ρ : ℂ => (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ∧ ¬ |ρ.im| ≤ T)
    (fun ρ => by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, not_le.mpr h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, not_le.mp h2⟩)).trans ?_
  exact ((Equiv.subtypeSubtypeEquivSubtypeInter
    (fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    (fun ρ : ℂ => ¬ |ρ.im| ≤ T)).tsum_eq
      (fun ρ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val)).symm

/-- The low and the high zero sum add up to the total zero sum. -/
private theorem pcsB_zero_split {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) (T : ℝ) :
    lowZeros (1 : DirichletCharacter ℂ 1) δ x T +
        highZeros (1 : DirichletCharacter ℂ 1) δ x T =
      ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val := by
  have hf := pcsB_zeroTerm_summable hx δ
  have hlow : lowZeros (1 : DirichletCharacter ℂ 1) δ x T =
      ∑' ρ : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} | |ρ.val.im| ≤ T},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val.val := by
    rw [lowZeros]
    refine (tsum_congr_subtype (f := fun ρ : ℂ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ)
      (P := fun ρ : ℂ => DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (Q := fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (fun ρ => by simp only [pcsB_LFunction_one_eq_zero])).trans ?_
    refine (tsum_congr_subtype (f := fun ρ : ℂ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ)
      (P := fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (Q := fun ρ : ℂ => (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ∧ |ρ.im| ≤ T)
      (fun ρ => by tauto)).trans ?_
    exact ((Equiv.subtypeSubtypeEquivSubtypeInter
      (fun ρ : ℂ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
      (fun ρ : ℂ => |ρ.im| ≤ T)).tsum_eq
        (fun ρ => zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val)).symm
  have hhigh :
      highZeros (1 : DirichletCharacter ℂ 1) δ x T =
      ∑' ρ : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} |
          ¬ |ρ.val.im| ≤ T},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val.val :=
    pcsB_high_eq_compl hx δ T
  rw [hlow, hhigh]
  exact hf.tsum_subtype_add_tsum_subtype_compl
    {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} | |ρ.val.im| ≤ T}

/-- The high zero sum of zeta tends to zero as the height grows. -/
private theorem pcsB_high_tendsto {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Tendsto (fun T : ℝ => highZeros (1 : DirichletCharacter ℂ 1) δ x T) atTop (𝓝 0) := by
  have h := (tendsto_tsum_compl_atTop_zero
    (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
      zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val)).comp
    pcsB_stripZeros_finset_tendsto
  refine h.congr' ?_
  filter_upwards with T
  have h1 : (∑' a : {x : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} //
        x ∉ (pcsB_stripZeros_finite T).toFinset},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x a.val.val) =
      ∑' a : {ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} |
          ¬ |ρ.val.im| ≤ T},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x a.val.val :=
    tsum_congr_subtype (f := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val)
      (P := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
        ρ ∉ (pcsB_stripZeros_finite T).toFinset)
      (Q := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
        ¬ |ρ.val.im| ≤ T)
      (fun a => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq])
  exact h1.trans (pcsB_high_eq_compl hx δ T).symm

/-- The low zero sum of zeta tends to the total zero sum as the height grows. -/
private theorem pcsB_low_tendsto_total {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Tendsto (fun T : ℝ => lowZeros (1 : DirichletCharacter ℂ 1) δ x T) atTop
      (𝓝 (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val)) := by
  have h2 : Tendsto (fun T : ℝ =>
      (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val) -
        highZeros (1 : DirichletCharacter ℂ 1) δ x T) atTop
      (𝓝 ((∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val) - 0)) :=
    tendsto_const_nhds.sub (pcsB_high_tendsto hx δ)
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards with T
  have hs := pcsB_zero_split hx δ T
  rw [← hs]
  ring


/-! #### F12. Conjugation, and the lower horizontal piece at a good height -/

private theorem pcsB_zeta_conj (z : ℂ) :
    riemannZeta (starRingEnd ℂ z) = starRingEnd ℂ (riemannZeta z) := by
  simpa using riemannZeta_conj z

private theorem pcsB_zeta_conj_ne {z : ℂ} (h : riemannZeta (starRingEnd ℂ z) ≠ 0) :
    riemannZeta z ≠ 0 := by
  intro hz
  exact h (by rw [pcsB_zeta_conj, hz, map_zero])

private theorem pcsB_logDeriv_conj (z : ℂ) :
    logDeriv riemannZeta (starRingEnd ℂ z) = starRingEnd ℂ (logDeriv riemannZeta z) := by
  simpa using logDerivZeta_conj' z

private theorem pcsB_logDeriv_conj_norm (z : ℂ) :
    ‖logDeriv riemannZeta (starRingEnd ℂ z)‖ = ‖logDeriv riemannZeta z‖ := by
  rw [pcsB_logDeriv_conj]
  exact norm_star _

/-- At a good height the horizontal piece at the lower edge also vanishes. -/
private theorem pcsB_horiz_tendsto_neg {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {C : ℝ} (hC : 0 ≤ C)
    {y : ℝ → ℝ} (hy : ∀ t : ℝ, 5 ≤ t → y t ∈ Set.Icc t (t + 1))
    (hBy : ∀ t : ℝ, 5 ≤ t → ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
      ‖logDeriv riemannZeta ((σ : ℂ) + y t * Complex.I)‖ ≤ C * Real.log t ^ 2) :
    Tendsto (fun t : ℝ => ∫ σ in (-1 / 2 : ℝ)..2,
        -(deriv riemannZeta ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I) /
            riemannZeta ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I)))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := pcsB_horiz_bound hx δ
  have hx0 : (0 : ℝ) < x := by linarith
  have hA0 : 0 ≤ 5 / 2 * K * C * x ^ 2 := by positivity
  have hev : ∀ᶠ t : ℝ in atTop,
      ‖∫ σ in (-1 / 2 : ℝ)..2,
        -(deriv riemannZeta ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I) /
            riemannZeta ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I)) *
          (continuedGaussian δ ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I))‖ ≤
      (5 / 2 * K * C * x ^ 2) * (Real.log t ^ 2 / t ^ 2) := by
    filter_upwards [eventually_ge_atTop (5 : ℝ)] with t ht
    have hyI := hy t ht
    have hT0 : (0 : ℝ) < t := by linarith
    have hy1 : 1 ≤ |(-y t : ℝ)| := by
      rw [abs_neg]
      exact le_trans (by linarith [hyI.1] : (1 : ℝ) ≤ y t) (le_abs_self _)
    have hlog2 : 0 ≤ Real.log t ^ 2 := sq_nonneg _
    have hB0 : 0 ≤ C * Real.log t ^ 2 := mul_nonneg hC hlog2
    have hb := hbound (-y t) (C * Real.log t ^ 2) hy1 hB0 ?_
    · refine hb.trans ?_
      have hyl : t ^ 2 ≤ (-y t) ^ 2 := by nlinarith [hyI.1, hyI.2, hT0.le]
      have hden : (0 : ℝ) < 1 + (-y t) ^ 2 := by positivity
      have hT2 : (0 : ℝ) < t ^ 2 := by positivity
      have key : 5 / 2 * (K * (C * Real.log t ^ 2) * x ^ 2 / (1 + (-y t) ^ 2)) =
          (5 / 2 * K * C * x ^ 2) * (Real.log t ^ 2 / (1 + (-y t) ^ 2)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [key]
      refine mul_le_mul_of_nonneg_left ?_ hA0
      exact div_le_div_of_nonneg_left hlog2 hT2 (by linarith)
    · intro σ hσ
      have heqc : ((σ : ℂ) + (((-y t : ℝ) : ℂ)) * Complex.I) =
          starRingEnd ℂ ((σ : ℂ) + ((y t : ℝ) : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [heqc, pcsB_logDeriv_conj_norm]
      exact hBy t ht σ hσ
  have hlim : Tendsto (fun t : ℝ =>
      (5 / 2 * K * C * x ^ 2) * (Real.log t ^ 2 / t ^ 2)) atTop (𝓝 0) := by
    have h := pcsB_log_sq_div_tendsto.const_mul (5 / 2 * K * C * x ^ 2)
    simpa using h
  exact squeeze_zero_norm' hev hlim


/-! #### F13. The contour shift in the total form -/

/-- **The contour shift, summed over all strip zeros.** This is the identity that leaf B
states, with the two zero sums replaced by their total. -/
private theorem pcsB_shift_total {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) :
    Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x + principalContour δ x =
      -(((Real.log (2 * π) : ℝ)) : ℂ) + fhat etaHeart (-δ) * (x : ℂ) -
        ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val := by
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨C, hC0, hgood⟩ := LeanLab.PNTPort.ZetaZeros.good_height_full
  set Y : ℝ → ℝ := fun t => if h : 5 ≤ t then (hgood t h).choose else 5 with hY
  have hYspec : ∀ t : ℝ, 5 ≤ t → Y t ∈ Set.Icc t (t + 1) ∧
      ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2, riemannZeta ((σ : ℂ) + Y t * Complex.I) ≠ 0 ∧
        ‖logDeriv riemannZeta ((σ : ℂ) + Y t * Complex.I)‖ ≤ C * Real.log t ^ 2 := by
    intro t ht
    have hyv : Y t = (hgood t ht).choose := by rw [hY]; exact dif_pos ht
    have h0 := (hgood t ht).choose_spec
    rw [hyv]
    refine ⟨h0.1, fun σ hσ => ?_⟩
    have hσ1 : (-1 / 2 : ℝ) ≤ σ ∧ σ ≤ 2 := by
      rw [Set.mem_Icc] at hσ
      exact ⟨by linarith [hσ.1], hσ.2⟩
    refine ⟨?_, ?_⟩
    · simpa only [mul_comm Complex.I] using (h0.2 σ hσ1).1
    · rw [logDeriv_apply]
      simpa only [mul_comm Complex.I] using (h0.2 σ hσ1).2
  have hYtop : Tendsto Y atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun a => ⟨max a 5, fun t ht => ?_⟩
    have h5 : (5 : ℝ) ≤ t := le_trans (le_max_right a 5) ht
    exact le_trans (le_trans (le_max_left a 5) ht) (hYspec t h5).1.1
  set F : ℂ → ℂ := fun s => -(deriv riemannZeta s / riemannZeta s) *
    (continuedGaussian δ s * (x : ℂ) ^ s) with hF
  have hbd : ∀ t : ℝ, 5 ≤ t → ∀ z ∈ RectangleBorder (⟨-1 / 2, -(Y t)⟩ : ℂ) ⟨2, Y t⟩,
      riemannZeta z ≠ 0 := by
    intro t ht z hz hzero
    have hT0 : 0 < Y t := by linarith [(hYspec t ht).1.1]
    have hbdd := (pcsB_mem_rect (T := Y t) (z := z) hT0.le).mp
      (rectangleBorder_subset_rectangle (⟨-1 / 2, -(Y t)⟩ : ℂ) ⟨2, Y t⟩ hz)
    obtain ⟨hre, him⟩ := hbdd
    rcases pcsB_border_cases hz with h | h | h | h
    · have hconj : riemannZeta (starRingEnd ℂ z) = 0 := by
        rw [pcsB_zeta_conj, hzero, map_zero]
      have hz' : starRingEnd ℂ z = ((z.re : ℝ) : ℂ) + Y t * Complex.I := by
        apply Complex.ext
        · simp
        · simp [h]
      rw [hz'] at hconj
      exact ((hYspec t ht).2 z.re ⟨by linarith [hre.1], hre.2⟩).1 hconj
    · rcases eq_or_ne z.im 0 with him0 | him0
      · have hzeq : z = (((-1 / 2 : ℝ)) : ℂ) := by
          apply Complex.ext
          · simpa using h
          · simpa using him0
        rw [hzeq] at hzero
        exact pcsB_zeta_ne_zero_of_real_nonpos (by norm_num) (by norm_num) hzero
      · exact LeanLab.PNTPort.ZetaZeros.zeta_ne_zero_of_re_nonpos (by rw [h]; norm_num) him0 hzero
    · have hz' : z = ((z.re : ℝ) : ℂ) + Y t * Complex.I := by
        apply Complex.ext <;> simp [h]
      rw [hz'] at hzero
      exact ((hYspec t ht).2 z.re ⟨by linarith [hre.1], hre.2⟩).1 hzero
    · exact riemannZeta_ne_zero_of_one_lt_re (by rw [h]; norm_num) hzero
  have hV2 : Tendsto (fun t : ℝ => (1 / (2 * π) : ℂ) * ∫ s in (-(Y t))..(Y t),
      F (((2 : ℝ) : ℂ) + (s : ℂ) * Complex.I)) atTop
      (𝓝 (Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x)) := by
    have hI : Tendsto (fun t : ℝ => (1 / (2 * π) : ℂ) * ∫ s in (-(Y t))..(Y t),
        logDeriv riemannZeta ((2 : ℂ) + s * Complex.I) *
          (gaussianMellin δ ((2 : ℂ) + s * Complex.I) *
            (x : ℂ) ^ ((2 : ℂ) + s * Complex.I)))
        atTop (𝓝 (- Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x)) :=
      (pcsB_two_line_value hx δ).comp hYtop
    have hI' : Tendsto (fun t : ℝ => -((1 / (2 * π) : ℂ) * ∫ s in (-(Y t))..(Y t),
        logDeriv riemannZeta ((2 : ℂ) + s * Complex.I) *
          (gaussianMellin δ ((2 : ℂ) + s * Complex.I) *
            (x : ℂ) ^ ((2 : ℂ) + s * Complex.I))))
        atTop (𝓝 (Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x)) := by
      simpa using hI.neg
    refine hI'.congr' ?_
    filter_upwards with t
    have hpt : (∫ s in (-(Y t))..(Y t), F (((2 : ℝ) : ℂ) + (s : ℂ) * Complex.I)) =
        -(∫ s in (-(Y t))..(Y t), logDeriv riemannZeta ((2 : ℂ) + s * Complex.I) *
          (gaussianMellin δ ((2 : ℂ) + s * Complex.I) *
            (x : ℂ) ^ ((2 : ℂ) + s * Complex.I))) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hF]
      rw [logDeriv_apply,
        LeanLab.HelfgottMajor.Continuation457.continuedGaussian_eq δ _ (by push_cast; norm_num)]
      push_cast
      ring
    rw [hpt]
    ring
  have hVm : Tendsto (fun t : ℝ => (1 / (2 * π) : ℂ) * ∫ s in (-(Y t))..(Y t),
      F (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I)) atTop
      (𝓝 (- principalContour δ x)) := by
    have hI : Tendsto (fun t : ℝ => (1 / (2 * π) : ℂ) * ∫ s in (-(Y t))..(Y t),
        logDeriv riemannZeta ((-1 / 2 : ℂ) + s * Complex.I) *
          (continuedGaussian δ ((-1 / 2 : ℂ) + s * Complex.I) *
            (x : ℂ) ^ ((-1 / 2 : ℂ) + s * Complex.I)))
        atTop (𝓝 (principalContour δ x)) :=
      (pcsB_half_line_value hx δ).comp hYtop
    have hI' : Tendsto (fun t : ℝ => -((1 / (2 * π) : ℂ) * ∫ s in (-(Y t))..(Y t),
        logDeriv riemannZeta ((-1 / 2 : ℂ) + s * Complex.I) *
          (continuedGaussian δ ((-1 / 2 : ℂ) + s * Complex.I) *
            (x : ℂ) ^ ((-1 / 2 : ℂ) + s * Complex.I))))
        atTop (𝓝 (- principalContour δ x)) := by
      simpa using hI.neg
    refine hI'.congr' ?_
    filter_upwards with t
    have hpt : (∫ s in (-(Y t))..(Y t), F (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I)) =
        -(∫ s in (-(Y t))..(Y t), logDeriv riemannZeta ((-1 / 2 : ℂ) + s * Complex.I) *
          (continuedGaussian δ ((-1 / 2 : ℂ) + s * Complex.I) *
            (x : ℂ) ^ ((-1 / 2 : ℂ) + s * Complex.I))) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hF]
      rw [logDeriv_apply]
      push_cast
      ring
    rw [hpt]
    ring
  have hH : Tendsto (fun t : ℝ => (1 / (2 * π * Complex.I) : ℂ) *
      ((∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + (((-Y t : ℝ) : ℂ)) * Complex.I)) -
       ∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + ((Y t : ℝ) : ℂ) * Complex.I)))
      atTop (𝓝 0) := by
    have hneg := pcsB_horiz_tendsto_neg (x := x) hx δ hC0.le
      (fun t ht => (hYspec t ht).1) (fun t ht σ hσ => ((hYspec t ht).2 σ hσ).2)
    have hpos := pcsB_horiz_tendsto (x := x) hx δ hC0.le
      (fun t ht => (hYspec t ht).1) (fun t ht σ hσ => ((hYspec t ht).2 σ hσ).2)
    have h := (hneg.sub hpos).const_mul (1 / (2 * π * Complex.I) : ℂ)
    simpa [hF, mul_zero] using h
  have hdec : ∀ t : ℝ, RectangleIntegral' F (⟨-1 / 2, -(Y t)⟩ : ℂ) ⟨2, Y t⟩ =
      (1 / (2 * π) : ℂ) * ((∫ s in (-(Y t))..(Y t), F (((2 : ℝ) : ℂ) + (s : ℂ) * Complex.I)) -
        ∫ s in (-(Y t))..(Y t), F (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I)) +
      (1 / (2 * π * Complex.I) : ℂ) *
        ((∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + (((-Y t : ℝ) : ℂ)) * Complex.I)) -
         ∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + ((Y t : ℝ) : ℂ) * Complex.I)) := by
    intro t
    exact pcsB_rect_decomp F (Y t)
  have hres : ∀ t : ℝ, 5 ≤ t →
      RectangleIntegral' F (⟨-1 / 2, -(Y t)⟩ : ℂ) ⟨2, Y t⟩ =
        -(((Real.log (2 * π) : ℝ)) : ℂ) + fhat etaHeart (-δ) * (x : ℂ) -
          lowZeros (1 : DirichletCharacter ℂ 1) δ x (Y t) := by
    intro t ht
    have hT0 : 0 < Y t := by linarith [(hYspec t ht).1.1]
    rw [hF]
    rw [pcsB_rect_residue hx0 δ hT0 (hbd t ht)]
    rw [pcsB_rect_finset_sum hx δ hT0.le]
  have hA : Tendsto (fun t : ℝ =>
      (1 / (2 * π) : ℂ) * (∫ s in (-(Y t))..(Y t), F (((2 : ℝ) : ℂ) + (s : ℂ) * Complex.I))
      - (1 / (2 * π) : ℂ) * (∫ s in (-(Y t))..(Y t),
          F (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I))
      + (1 / (2 * π * Complex.I) : ℂ) *
        ((∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + (((-Y t : ℝ) : ℂ)) * Complex.I)) -
         ∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + ((Y t : ℝ) : ℂ) * Complex.I)))
      atTop (𝓝 (Schi etaHeart (1 : DirichletCharacter ℂ 1) δ x + principalContour δ x)) := by
    have h := (hV2.sub hVm).add hH
    simpa using h
  have hreslim : Tendsto (fun t : ℝ =>
      -(((Real.log (2 * π) : ℝ)) : ℂ) + fhat etaHeart (-δ) * (x : ℂ) -
        lowZeros (1 : DirichletCharacter ℂ 1) δ x (Y t)) atTop
      (𝓝 (-(((Real.log (2 * π) : ℝ)) : ℂ) + fhat etaHeart (-δ) * (x : ℂ) -
        ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          zeroTerm (1 : DirichletCharacter ℂ 1) δ x ρ.val)) := by
    have h1 : Tendsto (fun _ : ℝ => -(((Real.log (2 * π) : ℝ)) : ℂ)) atTop
        (𝓝 (-(((Real.log (2 * π) : ℝ)) : ℂ))) := tendsto_const_nhds
    have h2 : Tendsto (fun _ : ℝ => fhat etaHeart (-δ) * (x : ℂ)) atTop
        (𝓝 (fhat etaHeart (-δ) * (x : ℂ))) := tendsto_const_nhds
    have h3 := (pcsB_low_tendsto_total hx δ).comp hYtop
    have h := (h1.add h2).sub h3
    simpa using h
  have heqfun : ∀ᶠ t : ℝ in atTop,
      ((1 / (2 * π) : ℂ) * (∫ s in (-(Y t))..(Y t), F (((2 : ℝ) : ℂ) + (s : ℂ) * Complex.I))
        - (1 / (2 * π) : ℂ) * (∫ s in (-(Y t))..(Y t),
            F (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I))
        + (1 / (2 * π * Complex.I) : ℂ) *
          ((∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + (((-Y t : ℝ) : ℂ)) * Complex.I)) -
           ∫ σ in (-1 / 2 : ℝ)..2, F ((σ : ℂ) + ((Y t : ℝ) : ℂ) * Complex.I))) =
      (-(((Real.log (2 * π) : ℝ)) : ℂ) + fhat etaHeart (-δ) * (x : ℂ) -
        lowZeros (1 : DirichletCharacter ℂ 1) δ x (Y t)) := by
    filter_upwards [eventually_ge_atTop (5 : ℝ)] with t ht
    rw [← hres t ht]
    rw [hdec t]
    ring
  exact tendsto_nhds_unique hA (hreslim.congr' (heqfun.mono fun t h => h.symm))

/-! ### B. The move from real part two to real part minus one half -/

/-- LEAF. Step two, the contour shift at conductor one, Lemma 4.1 at page 33 display 4.7.
The weighted von Mangoldt sum equals minus the principal contour minus log of two pi, plus
the guarded conductor one main term, minus the two zero sums split at the height `T`. It is
one leg: the line of real part one half is no contour, since the logarithmic derivative is
not integrable across the zeros of that line. It asserts no size estimate for the contour
and no bound for either zero sum, and it needs no hypothesis on the location of the zeros. -/
theorem principal_explicit_formula_shift (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    Schi etaHeart χ δ x =
      -((log (2 * π) : ℂ)) - principalContour δ x +
        (if q = 1 then fhat etaHeart (-δ) * x else 0) -
        lowZeros χ δ x T - highZeros χ δ x T := by
  subst hq
  have hchi : χ = 1 := Subsingleton.elim χ 1
  rw [hchi, if_pos rfl]
  have hmain := pcsB_shift_total hx δ
  have hsplit := pcsB_zero_split hx δ T
  rw [← hsplit] at hmain
  linear_combination hmain

/-! ### E. The assembly -/

/-- The contour shift identity of the target, assembled from the three identities above by
rewriting and `ring` only.  The statement is the target's, unchanged; the assembly has no
unproved step of its own and does not use the target theorem. -/
theorem principal_contour_shift_two_to_minus_half_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) +
        (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
        (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
  have h1 := principal_two_line_prime_sum x hx q χ δ
  have h2 := principal_half_line_conductor_one x hx q χ δ hq
  have h3 := principal_explicit_formula_shift x hx q χ δ T hq
  rw [h1, h3, h2]
  ring


/-- LEAF. Step two, the whole contour shift, P0014 Lemma 4.1, page 33 display 4.7, at
conductor one.  Moving the vertical line from real part two down to real part minus one
half crosses the pole at one, whose residue is minus the main term, which is the guarded
term; every nontrivial zero with its analytic multiplicity, which gives the two zero sums
split at the height `T` with the plus sign they carry in the target; and the pole at zero,
where the logarithmic derivative of zeta is log of two pi and the continued transform has
residue one.  No zero hypothesis is needed: the two zero sums together run over every zero
in the strip.  U-1648 replaced the former leaves `principal_contour_line_shift_pole_at_one`
and `principal_contour_zero_band_crossing` by this one; both were false, since their line
at real part one half meets zeros of zeta, the integrand is not integrable there and the
Lean integral on that line is zero.

The shift itself is carried out below by the development of
`SPLIT_principal_contour_shift_two_to_minus_half.lean` copied into this file, since that
module imports this one and so cannot be imported back; the only import added is
`LeanLab.PNTPort.ExplicitPsi1.ZeroSum`. -/
theorem principal_contour_shift_two_to_minus_half (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) +
        (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
        (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
  exact principal_contour_shift_two_to_minus_half_split x hx q χ δ T hq

/-- The conductor one contour identity, assembled from the four steps above by rewriting
and ring only.  The target statement is unchanged; the assembly has no unproved step of its own
and does not use the target theorem.  Since U-1648 it chains three leaves, and its binders
`hχ`, `hT` and `hzeros` are kept only so that its type stays the target's. -/
theorem principal_contour_identity_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q = 1)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T =
        -(log (2 * π) : ℂ) - principalContour δ x := by
  let A : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
      gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)
  let C : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
      continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)
  have hA : A = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
        gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) := rfl
  have hC : C = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := rfl
  have h1 := principal_prime_sum_mellin_contour x hx q χ δ
  have h2 := principal_contour_shift_two_to_minus_half x hx q χ δ T hq
  have h4 := principal_contour_conductor_one x hx q χ hq δ
  have e1 : Schi etaHeart χ δ x = -A := by
    rw [hA]; exact h1
  have e2 : A = C + (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
      (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
    rw [hA, hC]; exact h2
  have e4 : C = principalContour δ x := by
    rw [hC]; exact h4
  rw [e1, e2, e4]
  ring

end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
