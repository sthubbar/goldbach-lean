module

public import LeanLab.HelfgottMajor.Decomp123

/-!
Absolute convergence of the Gaussian twisted sum in P0014 Theorem 1.1 on page 3.
This is an elementary prerequisite for the explicit formula of Lemma 4.1 on page 31.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Gaussian123
open Real
open LeanLab.HelfgottArcs
open scoped ArithmeticFunction

/-- A summable geometric majorant for the Gaussian summand on page 3. -/
theorem gaussian_term_norm_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ)
    (hx : 0 < x) (n : ℕ) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * e (δ * n / x) * (etaHeart (n / x) : ℂ)‖ ≤
      (n : ℝ) * exp (-(1 / (2 * x ^ 2)) * (n : ℝ)) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hΛ : Λ n ≤ (n : ℝ) := by
    have hl := log_le_sub_one_of_pos hn
    exact ArithmeticFunction.vonMangoldt_le_log.trans (by linarith)
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (show n ≤ n ^ 2 by simpa [pow_two] using Nat.le_mul_self n)
  have hphase : ‖e (δ * n / x)‖ = 1 := by
    simp [e, Complex.norm_exp, Complex.mul_re]
  have hweight : ‖(etaHeart (n / x) : ℂ)‖ = exp (-((n : ℝ) / x) ^ 2 / 2) := by
    rw [etaHeart, ite_eq_left (div_pos hn hx), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exp_pos _)]
  have hexp : exp (-((n : ℝ) / x) ^ 2 / 2) ≤
      exp (-(1 / (2 * x ^ 2)) * (n : ℝ)) := by
    apply exp_le_exp.mpr
    have he : -((n : ℝ) / x) ^ 2 / 2 = -(n : ℝ) ^ 2 / (2 * x ^ 2) := by
      field_simp
    rw [he]
    have := div_le_div_of_nonneg_right hnsq (by positivity : 0 ≤ 2 * x ^ 2)
    have he2 : -(1 / (2 * x ^ 2)) * (n : ℝ) = -((n : ℝ) / (2 * x ^ 2)) := by ring
    rw [he2]
    simpa only [neg_div] using neg_le_neg this
  rw [norm_mul, norm_mul, norm_mul, hphase, hweight, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_one]
  apply mul_le_mul _ hexp (by positivity) (by positivity)
  calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
      mul_le_mul_of_nonneg_left (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ (n : ℝ) := by simpa using hΛ

/-- The Gaussian twisted von Mangoldt series converges absolutely for every x > 0.
P0014 page 3 and Lemma 4.1 on page 31. No GRH input is used.
-/
theorem gaussian_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) *
      e (δ * n / x) * (etaHeart (n / x) : ℂ)) := by
  have hc : 0 < 1 / (2 * x ^ 2) := by positivity
  apply (Real.summable_pow_mul_exp_neg_nat_mul 1 hc).of_norm_bounded
  intro n
  simpa only [pow_one] using gaussian_term_norm_bound χ δ x hx n

/-- The Gaussian twisted sum is continuous in the real shift.
P0014 page 3, the sum to which Lemma 4.1 applies on page 31.
-/
theorem continuous_gaussian_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : 0 < x) :
    Continuous (fun δ : ℝ => Schi etaHeart χ δ x) := by
  have hs : Summable (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) *
      (etaHeart (n / x) : ℂ)) := by
    simpa [e] using gaussian_summable χ 0 x hx
  unfold Schi
  apply continuous_tsum (u := fun n : ℕ =>
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * (etaHeart (n / x) : ℂ)‖) ?_ hs.norm ?_
  · intro n
    unfold e
    fun_prop
  · intro n δ
    have hphase : ‖e (δ * n / x)‖ = 1 := by
      simp [e, Complex.norm_exp, Complex.mul_re]
    simp only [norm_mul, hphase, mul_one, le_refl]

/-- The weight extended by zero in the lab has finite integral.
P0014 Lemma 4.1 on page 31, applied to the Gaussian.
-/
theorem etaHeart_integrable : MeasureTheory.Integrable etaHeart := by
  have h : MeasureTheory.Integrable (fun t : ℝ => exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hi := h.indicator (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  convert hi using 1
  funext t
  simp only [etaHeart, Set.indicator, Set.mem_Ioi]
  split_ifs
  · congr 1
    ring
  · rfl

/-- The Fourier main term for the Gaussian is continuous in the real frequency.
P0014 Theorem 1.1 on page 3 and Lemma 4.1 on page 31.
-/
theorem continuous_gaussian_fourier : Continuous (fun δ : ℝ => fhat etaHeart δ) := by
  unfold fhat
  apply MeasureTheory.continuous_of_dominated (bound := etaHeart)
  · intro δ
    exact (by unfold e; fun_prop : Continuous (fun y : ℝ => e (-(y * δ)))).aestronglyMeasurable.mul
      etaHeart_integrable.ofReal.aestronglyMeasurable
  · intro δ
    apply Filter.Eventually.of_forall
    intro y
    have hphase : ‖e (-(y * δ))‖ = 1 := by
      simp [e, Complex.norm_exp, Complex.mul_re]
    have hη : 0 ≤ etaHeart y := by
      unfold etaHeart
      split_ifs <;> positivity
    simp only [norm_mul, hphase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hη, le_refl]
  · exact etaHeart_integrable
  · apply Filter.Eventually.of_forall
    intro y
    unfold e
    fun_prop

/-- The lab norm formulation is equivalent to the paper's error variable formulation.
P0014 Theorem 1.1 on page 3. This is an algebraic equivalence, not a major arc estimate.
-/
theorem major_shape_error_iff {q : ℕ} (η : ℝ → ℝ) (χ : DirichletCharacter ℂ q)
    (δ x B : ℝ) (hx : 0 < x) :
    MajorShape η χ δ x B ↔ ∃ E : ℂ,
      Schi η χ δ x = (if q = 1 then fhat η (-δ) * x else 0) + E * x ∧ ‖E‖ ≤ B := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  constructor
  · intro h
    refine ⟨(Schi η χ δ x - (if q = 1 then fhat η (-δ) * x else 0)) / (x : ℂ), ?_, ?_⟩
    · field_simp
      ring
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, div_le_iff₀ hx]
      exact h
  · rintro ⟨E, he, hE⟩
    unfold MajorShape
    rw [he, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    exact mul_le_mul_of_nonneg_right hE hx.le

/-- At zero frequency the lab half-line Gaussian transform is half the full-line value.
This checks the normalization of the notation on P0014 page 3.
-/
theorem gaussian_fourier_zero :
    fhat etaHeart 0 = ((sqrt (2 * π) / 2 : ℝ) : ℂ) := by
  have hreal : (∫ y : ℝ, etaHeart y) = sqrt (2 * π) / 2 := by
    calc (∫ y : ℝ, etaHeart y) =
        ∫ y in Set.Ioi (0 : ℝ), exp (-(1 / 2 : ℝ) * y ^ 2) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
          congr 1
          funext y
          simp only [etaHeart, Set.indicator, Set.mem_Ioi]
          split_ifs
          · congr 1
            ring
          · rfl
      _ = sqrt (2 * π) / 2 := by rw [integral_gaussian_Ioi]; norm_num; ring
  unfold fhat
  simp only [mul_zero, neg_zero, e, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal, hreal]

/-- The lab half-line value differs from the full-line Gaussian value in the page 3 aside. -/
theorem half_line_ne_full_line : fhat etaHeart 0 ≠ ((sqrt (2 * π) : ℝ) : ℂ) := by
  rw [gaussian_fourier_zero]
  intro h
  have hr := Complex.ofReal_injective h
  have hp : 0 < sqrt (2 * π) := by positivity
  linarith

/-- The norm of the Gaussian main-term error is continuous in the shift.
This is a limit prerequisite for Theorem 1.1 on page 3.
-/
theorem continuous_gaussian_error {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : 0 < x) :
    Continuous (fun δ : ℝ =>
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖) := by
  have hmain : Continuous (fun δ : ℝ => if q = 1 then fhat etaHeart (-δ) * x else 0) := by
    by_cases hq : q = 1
    · simp only [hq, reduceIte]
      exact (continuous_gaussian_fourier.comp continuous_neg).mul continuous_const
    · simp only [hq, reduceIte]
      exact continuous_const
  exact ((continuous_gaussian_sum χ x hx).sub hmain).norm

/-- A bound on a punctured positive shift interval extends to zero when its error budget is continuous.
P0014 page 3. CONDITIONAL ON hBound. This supplies no analytic major arc bound by itself.
-/
theorem major_shape_zero_of_punctured {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hx : 0 < x) (D : ℝ) (hD : 0 < D) (B : ℝ → ℝ) (hB : ContinuousAt B 0)
    (hBound : ∀ δ : ℝ, 0 < δ → δ ≤ D → MajorShape etaHeart χ δ x (B δ)) :
    MajorShape etaHeart χ 0 x (B 0) := by
  have hf : Filter.Tendsto (fun δ : ℝ =>
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ‖Schi etaHeart χ 0 x - (if q = 1 then fhat etaHeart (-0) * x else 0)‖) :=
    (continuous_gaussian_error χ x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg : Filter.Tendsto (fun δ : ℝ => B δ * x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (B 0 * x)) := (hB.mul_const x).tendsto.mono_left nhdsWithin_le_nhds
  unfold MajorShape
  apply le_of_tendsto_of_tendsto hf hg
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hD)] with δ hpos hlt
  exact hBound δ hpos hlt.le

/-- Polynomial moments of the Gaussian twisted series converge absolutely.
P0014 Theorem 1.2 on page 3 and the shifted Gaussian in display 4.44 on page 44.
-/
theorem gaussian_polynomial_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (hx : 0 < x) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℂ) ^ k *
      (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * e (δ * n / x) * (etaHeart (n / x) : ℂ))) := by
  have hc : 0 < 1 / (2 * x ^ 2) := by positivity
  apply (Real.summable_pow_mul_exp_neg_nat_mul (k + 1) hc).of_norm_bounded
  intro n
  have hnc : ‖(n : ℂ) ^ k‖ = (n : ℝ) ^ k := by simp
  rw [norm_mul, hnc]
  have h := mul_le_mul_of_nonneg_left (gaussian_term_norm_bound χ δ x hx n)
    (pow_nonneg (Nat.cast_nonneg n) k)
  simpa only [pow_succ, mul_assoc] using h

/-- Absolute convergence for the weight t squared times the Gaussian in Theorem 1.2, page 3. -/
theorem t2_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) *
      e (δ * n / x) * (etaT2 (n / x) : ℂ)) := by
  have hs := (gaussian_polynomial_summable χ δ x hx 2).mul_left (((x : ℂ) ^ 2)⁻¹)
  apply hs.congr
  intro n
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [etaHeart, etaT2, ite_eq_left (div_pos hn hx)]
  push_cast
  field_simp

end LeanLab.HelfgottMajor.Gaussian123
