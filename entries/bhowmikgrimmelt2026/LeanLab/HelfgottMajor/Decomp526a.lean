module

public import LeanLab.HelfgottMajor.Decomp526Energy
public import LeanLab.HelfgottMajor.BookP1617
public import LeanLab.HelfgottMajor.ZeroCount1623
public import LeanLab.HelfgottMajor.HalfMoment389

/-!
A signed continuous sampling route for P0014 Lemma 4.4, pages 39 and 40.
The Gaussian energies are the proved supplies of Decomp389b, now cycle free.
The scalar norms are display 4.42 on page 43.
The upper cutoff endpoint is retained in finite partial summation.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real MeasureTheory LeanLab.HelfgottArcs

/-- The multiplicity weighted Mellin norm of one zero, P0014 Lemma 4.4 pages 38 and 39 and
Lemma 4.5 page 40. The same definition as Decomp269b.mellinMassTerm. -/
noncomputable def mellinMassTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) (ρ : ℂ) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * ‖gaussianMellin δ ρ‖

/-- The part of the low Mellin mass with absolute imaginary part above 1, P0014 pages 39, 40. -/
noncomputable def middleMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- PROVED. P0014 display 4.30, page 39: the trivial bound of the Gaussian Mellin transform by
the absolute integral. Copy of Gaussian269.mellin_norm_le. -/
theorem mellin_norm_le (δ : ℝ) (s : ℂ) :
    ‖gaussianMellin δ s‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), t ^ (s.re - 1) * exp (-t ^ 2 / 2) := by
  unfold gaussianMellin mellin
  calc
    _ ≤ ∫ t in Set.Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
      rw [norm_smul, norm_mul, he, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      simp

/-- PROVED. P0014 display 4.30 on page 39 with the norm 2.15581 of display 4.42 on page 43:
on the critical line the Gaussian Mellin transform has norm at most 2.15581. -/
theorem mellin_critical_norm_le (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖gaussianMellin δ s‖ ≤ 2.15581 := by
  have h := mellin_norm_le δ s
  rw [hs] at h
  exact h.trans HalfMoment389.gaussian_half_moment_bound

end LeanLab.HelfgottMajor.SplitGaussian123

namespace LeanLab.HelfgottMajor.Decomp526a
open Real MeasureTheory LeanLab.HelfgottArcs SplitGaussian123
open Decomp389b Set
open scoped Topology

/-- The contribution of one sign of the middle heights in display 4.32, page 39.
Only the signs one and minus one are used. -/
noncomputable def signedMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) : ℝ :=
  ∑' ρ : ZeroCount1623.ZeroIdx χ T,
    Set.indicator {ρ | 1 < ε * ρ.val.im} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- The critical line turns a zero into its ordinate sample in display 4.32, page 39.
This uses no reflection of the twisted Gaussian. -/
theorem signed_mass_on_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    signedMass χ δ T ε = ∑' ρ : ZeroCount1623.ZeroIdx χ T,
      Set.indicator {ρ | 1 < ε * ρ.val.im}
        (fun ρ => (ZeroCount1623.mult χ ρ.val : ℝ) *
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ := by
  classical
  apply tsum_congr
  intro ρ
  have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
  have he : ρ.val = (1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  by_cases h : 1 < ε * ρ.val.im
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, h, if_true, mellinMassTerm]
    congr 1
    exact congrArg (fun z => ‖gaussianMellin δ z‖) he
  · simp [Set.indicator, h]

/-- The two signs partition the middle heights, pages 39 and 40.
Finiteness of the strip zeros supplies summability without a critical line input. -/
theorem middle_mass_signed_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : middleMass χ δ T = signedMass χ δ T 1 + signedMass χ δ T (-1) := by
  classical
  haveI := ZeroCount1623.zeroIdx_finite χ T
  unfold middleMass signedMass
  rw [← (Summable.of_finite.tsum_add Summable.of_finite)]
  apply tsum_congr
  intro ρ
  by_cases hp : 1 < ρ.val.im
  · have hn : ¬1 < -ρ.val.im := by linarith
    have ha : ¬|ρ.val.im| ≤ 1 := by intro h; have := (abs_le.mp h).2; linarith
    simp [Set.indicator, hp, hn, ha]
  · by_cases hn : 1 < -ρ.val.im
    · have ha : ¬|ρ.val.im| ≤ 1 := by intro h; have := (abs_le.mp h).1; linarith
      simp [Set.indicator, hp, hn, ha]
    · have ha : |ρ.val.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [Set.indicator, hp, hn, ha]

/-- Each signed contribution is nonnegative, as in display 4.32 on page 39. -/
theorem signed_mass_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) : 0 ≤ signedMass χ δ T ε := by
  apply tsum_nonneg
  intro ρ
  apply Set.indicator_nonneg
  intro _ _
  exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- At height one the middle interval is empty, page 39. -/
theorem middle_mass_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) : middleMass χ δ 1 = 0 := by
  unfold middleMass
  convert tsum_zero (β := ZeroCount1623.ZeroIdx χ 1) (α := ℝ) using 1
  congr 1
  funext ρ
  exact Set.indicator_of_notMem (by simpa using ρ.property.2.2.2) _

/-- Unit interval Cauchy Schwarz from the integral of a square.
Derived scalar support for the finite integrals in display 4.32, page 39. -/
theorem unit_interval_integral_le_sqrt (f : ℝ → ℝ) (a : ℝ)
    (hf : ContinuousOn f (Icc a (a + 1))) :
    (∫ t in a..a + 1, f t) ≤ sqrt (∫ t in a..a + 1, f t ^ 2) := by
  let m := ∫ t in a..a + 1, f t
  have hfc : ContinuousOn f (uIcc a (a + 1)) := by simpa [uIcc_of_le (show a ≤ a + 1 by linarith)] using hf
  have hi : IntervalIntegrable f volume a (a + 1) := hfc.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => f t ^ 2) volume a (a + 1) := (hfc.pow 2).intervalIntegrable
  have hp : 0 ≤ ∫ t in a..a + 1, (f t - m) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact sq_nonneg _
  have he : (∫ t in a..a + 1, (f t - m) ^ 2) =
      (∫ t in a..a + 1, f t ^ 2) - m ^ 2 := by
    calc
      _ = ∫ t in a..a + 1, (f t ^ 2 - (2 * m) * f t + m ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hi2.sub (hi.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hi2 (hi.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        dsimp [m]
        ring
  rw [he] at hp
  by_cases hm : m ≤ 0
  · exact hm.trans (sqrt_nonneg _)
  · have hm0 : 0 ≤ m := le_of_not_ge hm
    exact (le_sqrt hm0 (by linarith [sq_nonneg m])).mpr (by linarith)

/-- A unit interval trace estimate from the fundamental theorem of calculus.
Derived support for the finite upper endpoint in display 4.32, page 39. -/
theorem unit_interval_trace (f f' : ℝ → ℂ) (T : ℝ)
    (hf : ContinuousOn f (Icc (T - 1) T))
    (hf' : ContinuousOn f' (Icc (T - 1) T))
    (hd : ∀ t ∈ Icc (T - 1) T, HasDerivAt f (f' t) t) :
    ‖f T‖ ≤ sqrt (∫ t in (T - 1)..T, ‖f t‖ ^ 2) +
      sqrt (∫ t in (T - 1)..T, ‖f' t‖ ^ 2) := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (T - 1) T).Nonempty from ⟨T, by constructor <;> linarith⟩)
    (hf.norm.pow 2)
  have hfu : ‖f u‖ ^ 2 ≤ ∫ t in (T - 1)..T, ‖f t‖ ^ 2 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : T - 1 ≤ T)
      (f := fun _ => ‖f u‖ ^ 2) (g := fun t => ‖f t‖ ^ 2)
      intervalIntegrable_const (by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (show T - 1 ≤ T by linarith)]
        exact hf.norm.pow 2)
      (fun t ht => hmin ht)
    simpa using h
  have hfu' : ‖f u‖ ≤ sqrt (∫ t in (T - 1)..T, ‖f t‖ ^ 2) :=
    (le_sqrt (norm_nonneg _) (hfu.trans' (sq_nonneg _))).mpr hfu
  have hfui : IntervalIntegrable f' volume u T :=
    (hf'.mono (by intro x hx; rw [uIcc_of_le hu.2] at hx; exact ⟨hu.1.trans hx.1, hx.2⟩)).intervalIntegrable
  have he : ∫ t in u..T, f' t = f T - f u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hfui
    intro t ht
    rw [uIcc_of_le hu.2] at ht
    exact hd t ⟨hu.1.trans ht.1, ht.2⟩
  have hdiff : ‖f T - f u‖ ≤ ∫ t in (T - 1)..T, ‖f' t‖ := by
    rw [← he]
    apply (intervalIntegral.norm_integral_le_integral_norm hu.2).trans
    apply intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (by simpa [uIcc_of_le (show T - 1 ≤ T by linarith)] using hf'.norm : ContinuousOn (fun t => ‖f' t‖) (uIcc (T - 1) T)).intervalIntegrable
  have hc := unit_interval_integral_le_sqrt (fun t => ‖f' t‖) (T - 1)
    (by simpa using hf'.norm)
  have hlast : (∫ t in (T - 1)..T, ‖f' t‖) ≤ sqrt (∫ t in (T - 1)..T, ‖f' t‖ ^ 2) := by
    simpa using hc
  calc
    _ ≤ ‖f u‖ + ‖f T - f u‖ := by simpa only [add_sub_cancel] using norm_add_le (f u) (f T - f u)
    _ ≤ _ := add_le_add hfu' (hdiff.trans hlast)

/-- The upper endpoint is bounded by the two one sign energies.
Derived finite cutoff support for display 4.32 on page 39 and page 40.
The unit interval ending at T lies above height one when T is at least two. -/
theorem gaussian_endpoint_trace (δ T ε : ℝ) (hT : 2 ≤ T) (hε : ε = 1 ∨ ε = -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * T : ℝ) * Complex.I)‖ ≤
      sqrt (lineEnergy δ ε) + sqrt (derivativeEnergy δ ε) := by
  let F : ℝ → ℂ := fun t => gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)
  let D : ℝ → ℂ := fun t => deriv (gaussianMellin δ)
    ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) * ((ε : ℂ) * Complex.I)
  have hnorm : ‖(ε : ℂ) * Complex.I‖ = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have han (t : ℝ) : AnalyticAt ℂ (gaussianMellin δ)
      ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) :=
    Decomp389b.gaussian_mellin_analyticAt δ _ (by norm_num) (by norm_num)
  have hpath : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) := by fun_prop
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun u : ℝ => (1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I)
      (g := gaussianMellin δ) (han t).continuousAt hpath.continuousAt
  have hD : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc := ContinuousAt.comp (f := fun u : ℝ => (1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I)
      (g := deriv (gaussianMellin δ)) (han t).deriv.continuousAt hpath.continuousAt
    exact hc.mul continuousAt_const
  have hd (t : ℝ) : HasDerivAt F (D t) t := by
    have hg : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + (ε : ℂ) * z * Complex.I)
        ((ε : ℂ) * Complex.I) (t : ℂ) := by
      convert (((hasDerivAt_id (t : ℂ)).const_mul (ε : ℂ)).mul_const Complex.I).const_add
        (1 / 2 : ℂ) using 1 <;> simp
    have hh := (han t).differentiableAt.hasDerivAt
    have hh' : HasDerivAt (gaussianMellin δ)
        (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε : ℂ) * (t : ℂ) * Complex.I))
        ((1 / 2 : ℂ) + (ε : ℂ) * (t : ℂ) * Complex.I) := by
      simpa only [Complex.ofReal_mul] using hh
    simpa only [F, D, Function.comp_apply, Complex.ofReal_mul] using
      (hh'.comp (t : ℂ) hg).comp_ofReal
  have hFi : Integrable (fun t : ℝ => ‖F t‖ ^ 2) := by
    rcases hε with rfl | rfl
    · simpa [F, gaussianMellin, Decomp269a.gaussianMellin] using Decomp389b.integrable_mellin_sq δ
    · simpa [F, gaussianMellin, Decomp269a.gaussianMellin] using (Decomp389b.integrable_mellin_sq δ).comp_neg
  have hDi : Integrable (fun t : ℝ => ‖D t‖ ^ 2) := by
    have he : (fun t : ℝ => ‖D t‖ ^ 2) =
        fun t => ‖deriv (gaussianMellin δ)
          ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2 := by
      funext t
      simp only [D, norm_mul, hnorm, mul_one]
    rw [he]
    have hdint : Integrable (fun t : ℝ => ‖deriv (gaussianMellin δ)
        ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
      Decomp389b.gaussian_derivative_sq_integrable δ
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hdint
    · simpa only [neg_one_mul] using hdint.comp_neg
  have ha : (∫ t in (T - 1)..T, ‖F t‖ ^ 2) ≤ lineEnergy δ ε := by
    rw [intervalIntegral.integral_of_le (by linarith : T - 1 ≤ T)]
    apply setIntegral_mono_set hFi.integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    filter_upwards with t ht
    exact lt_of_lt_of_le (by linarith : 0 < T - 1) ht.1.le
  have hb : (∫ t in (T - 1)..T, ‖D t‖ ^ 2) ≤ derivativeEnergy δ ε := by
    rw [intervalIntegral.integral_of_le (by linarith : T - 1 ≤ T)]
    have he : (fun t : ℝ => ‖D t‖ ^ 2) =
        fun t => ‖deriv (gaussianMellin δ)
          ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2 := by
      funext t
      simp only [D, norm_mul, hnorm, mul_one]
    rw [he] at hDi ⊢
    apply setIntegral_mono_set hDi.integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    filter_upwards with t ht
    exact lt_of_le_of_lt (by linarith : 1 ≤ T - 1) ht.1
  exact (unit_interval_trace F D T hF.continuousOn hD.continuousOn (fun t _ => hd t)).trans
    (add_le_add (sqrt_le_sqrt ha) (sqrt_le_sqrt hb))

/-- Continuity of the signed Gaussian line profile used in display 4.32, page 39. -/
theorem signed_profile_continuous (δ ε : ℝ) :
    Continuous (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ha : AnalyticAt ℂ (gaussianMellin δ)
      ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) :=
    Decomp389b.gaussian_mellin_analyticAt δ _ (by norm_num) (by norm_num)
  exact ContinuousAt.comp (f := fun u : ℝ => (1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I)
    (g := gaussianMellin δ) ha.continuousAt (by fun_prop)

/-- Continuity of the signed Mellin derivative profile used on page 40. -/
theorem signed_derivative_profile_continuous (δ ε : ℝ) :
    Continuous (fun t : ℝ => deriv (gaussianMellin δ)
      ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ha : AnalyticAt ℂ (gaussianMellin δ)
      ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) :=
    Decomp389b.gaussian_mellin_analyticAt δ _ (by norm_num) (by norm_num)
  exact ContinuousAt.comp (f := fun u : ℝ => (1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I)
    (g := deriv (gaussianMellin δ)) ha.deriv.continuousAt (by fun_prop)

/-- Square integrability of either Gaussian line profile.
This transports the proved Plancherel supply to display 4.32 on page 39. -/
theorem signed_profile_sq_integrable (δ ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Integrable (fun t : ℝ =>
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2) := by
  have h : Integrable (fun t : ℝ =>
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
    Decomp389b.integrable_mellin_sq δ
  rcases hε with rfl | rfl
  · simpa only [one_mul] using h
  · simpa only [neg_one_mul] using h.comp_neg

/-- Square integrability of either Gaussian derivative profile.
This transports the proved differentiated Plancherel supply to page 40. -/
theorem signed_derivative_profile_sq_integrable (δ ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2) := by
  have h : Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
    Decomp389b.gaussian_derivative_sq_integrable δ
  rcases hε with rfl | rfl
  · simpa only [one_mul] using h
  · simpa only [neg_one_mul] using h.comp_neg

/-- Cauchy Schwarz on a finite height interval.
Derived support for display 4.32 on page 39 and the derivative integral on page 40. -/
theorem interval_cauchy_schwarz (f g : ℝ → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hf : ContinuousOn f (Icc 1 T)) (hg : ContinuousOn g (Icc 1 T))
    (hf0 : ∀ t ∈ Icc 1 T, 0 ≤ f t) (hg0 : ∀ t ∈ Icc 1 T, 0 ≤ g t) :
    (∫ t in (1 : ℝ)..T, f t * g t) ≤
      sqrt (∫ t in (1 : ℝ)..T, f t ^ 2) * sqrt (∫ t in (1 : ℝ)..T, g t ^ 2) := by
  have hfc : ContinuousOn f (uIcc 1 T) := by rwa [uIcc_of_le hT]
  have hgc : ContinuousOn g (uIcc 1 T) := by rwa [uIcc_of_le hT]
  have hfi : IntegrableOn f (Ioc 1 T) := hfc.intervalIntegrable.1
  have hgi : IntegrableOn g (Ioc 1 T) := hgc.intervalIntegrable.1
  have hfs : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume 1 T := (hfc.pow 2).intervalIntegrable
  have hgs : IntervalIntegrable (fun t : ℝ => g t ^ 2) volume 1 T := (hgc.pow 2).intervalIntegrable
  have hfm : MemLp f 2 (volume.restrict (Ioc 1 T)) := by
    apply (memLp_two_iff_integrable_sq_norm hfi.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs, Pi.pow_apply, IntegrableOn] using hfs.1
  have hgm : MemLp g 2 (volume.restrict (Ioc 1 T)) := by
    apply (memLp_two_iff_integrable_sq_norm hgi.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs, Pi.pow_apply, IntegrableOn] using hgs.1
  have hf0a : 0 ≤ᵐ[volume.restrict (Ioc 1 T)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hf0 t ⟨ht.1.le, ht.2⟩
  have hg0a : 0 ≤ᵐ[volume.restrict (Ioc 1 T)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hg0 t ⟨ht.1.le, ht.2⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc 1 T)) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) hf0a hg0a (by simpa using hfm) (by simpa using hgm)
  simpa only [intervalIntegral.integral_of_le hT, Real.rpow_two, sqrt_eq_rpow] using h

/-- A tail indicator restricts an interval integral to that tail.
Derived finite atom support for P0014 display 4.32 on page 39. -/
theorem integral_tail_indicator (f : ℝ → ℝ) (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (∫ t in a..b, (Set.Ioi c).indicator f t) = ∫ t in c..b, f t := by
  rw [intervalIntegral.integral_of_le (hac.trans hcb), integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, intervalIntegral.integral_of_le hcb]
  congr 1
  congr 1
  ext t
  simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
  constructor
  · rintro ⟨hc, ha, hb⟩
    exact ⟨hc, hb⟩
  · rintro ⟨hc, hb⟩
    exact ⟨hc, hac.trans_lt hc, hb⟩

/-- Finite partial summation for arbitrary real atoms and a continuously differentiable test.
Derived elementary support for Lemma 4.3 and display 4.32 on page 39.
The open inequality in the integrand keeps all Lebesgue endpoint atoms irrelevant. -/
theorem finite_atom_partial_summation {ι : Type*} (s : Finset ι)
    (γ w : ι → ℝ) (f f' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ i ∈ s, γ i ∈ Icc a b)
    (hf' : ContinuousOn f' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) :
    (∑ i ∈ s, w i * f (γ i)) = f b * (∑ i ∈ s, w i) -
      ∫ t in a..b, f' t * (∑ i ∈ s, if γ i < t then w i else 0) := by
  classical
  have hfi : IntervalIntegrable f' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hi (i : ι) : IntervalIntegrable ((Ioi (γ i)).indicator (fun t => w i * f' t)) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    exact (hfi.1.const_mul (w i)).indicator measurableSet_Ioi
  have heq : (fun t => f' t * (∑ i ∈ s, if γ i < t then w i else 0)) =
      fun t => ∑ i ∈ s, (Ioi (γ i)).indicator (fun t => w i * f' t) t := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ht : γ i < t <;> simp [Set.indicator, ht, mul_comm]
  rw [heq, intervalIntegral.integral_finsetSum (fun i (_ : i ∈ s) => hi i)]
  have hone (i : ι) (his : i ∈ s) :
      (∫ t in a..b, (Ioi (γ i)).indicator (fun t => w i * f' t) t) = w i * (f b - f (γ i)) := by
    rw [integral_tail_indicator _ _ _ _ (hγ i his).1 (hγ i his).2,
      intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le (hγ i his).2] at ht
      exact hd t ⟨(hγ i his).1.trans ht.1, ht.2⟩
    · apply hfi.mono_set
      rw [uIcc_of_le (hγ i his).2, uIcc_of_le hab]
      exact Icc_subset_Icc (hγ i his).1 le_rfl
  rw [Finset.sum_congr rfl hone]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

open ZeroCount1623

/-- The right closed positive count, with half weight at height zero.
Derived endpoint convention for book page 431 and P0014 display 4.32 on page 39. -/
noncomputable def closedPositiveCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) : ℝ :=
  ∑ ρ ∈ (stripZeros_finite χ T).toFinset,
    if ρ.im = 0 then (mult χ ρ : ℝ) / 2 else if 0 < ρ.im then (mult χ ρ : ℝ) else 0

/-- Just above T the book half endpoint count equals the right closed positive count.
Derived endpoint support for the finite sampling interval in display 4.32, page 39. -/
theorem book_count_right_eventually {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 0 < T) :
    ∀ᶠ t in 𝓝[>] T, bookCount χ t = closedPositiveCount χ T := by
  classical
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  filter_upwards [Ioo_mem_nhdsGT (show T < T + ε by linarith)] with t ht
  have he := hgap t ht.1 ht.2
  unfold bookCount closedPositiveCount
  rw [Finset.sum_filter]
  have hsets : (stripZeros_finite χ t).toFinset = (stripZeros_finite χ T).toFinset := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, he]
  rw [hsets]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρs : ρ ∈ stripZeros χ T := by simpa using hρ
  have hρT : |ρ.im| ≤ T := hρs.2.2.2
  have hne : ρ.im ≠ t := by
    intro heq
    rw [heq, abs_of_pos (hT.trans ht.1)] at hρT
    linarith [ht.1]
  by_cases h0 : ρ.im = 0
  · simp [halfWeight, h0]
    ring
  · by_cases hp : 0 < ρ.im
    · simp [halfWeight, h0, hne, hp, hp.le]
    · have hn : ¬0 ≤ ρ.im := by intro h; exact hp (lt_of_le_of_ne h (Ne.symm h0))
      simp [halfWeight, h0, hp, hn]

/-- A continuous numerical half count envelope also bounds the right closed count.
CONDITIONAL ON the explicit count family, as required by display 4.32 on page 39. -/
theorem closed_positive_count_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T)
    (hcount : ∀ t : ℝ, 1 ≤ t → |bookCount χ t - bookMain q t| ≤ bookError q t) :
    |closedPositiveCount χ T - bookMain q T| ≤ bookError q T := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hT0 : 0 < T := by linarith
  have hmain : ContinuousAt (fun t => bookMain q t) T := by
    unfold bookMain
    have hne : (q : ℝ) * T / (2 * π * exp 1) ≠ 0 := by positivity
    exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)
  have herr : ContinuousAt (fun t => bookError q t) T := by
    unfold bookError
    exact ContinuousAt.add (ContinuousAt.mul (by fun_prop)
      (ContinuousAt.log (by fun_prop) (mul_ne_zero hq hT0.ne'))) (by fun_prop)
  have hev : ∀ᶠ t in 𝓝[>] T,
      |closedPositiveCount χ T - bookMain q t| ≤ bookError q t := by
    filter_upwards [book_count_right_eventually χ T hT0, self_mem_nhdsWithin] with t he ht
    rw [← he]
    exact hcount t (hT.trans ht.le)
  exact le_of_tendsto_of_tendsto
    ((continuousAt_const.sub hmain).abs.tendsto.mono_left nhdsWithin_le_nhds)
    (herr.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- At the bottom cutoff either signed mass vanishes.
P0014 page 39, the middle height range starts strictly above one. -/
theorem signed_mass_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ ε : ℝ) (hε : ε = 1 ∨ ε = -1) : signedMass χ δ 1 ε = 0 := by
  have hs := middle_mass_signed_split χ δ 1
  rw [middle_mass_at_one] at hs
  have hp := signed_mass_nonneg χ δ 1 1
  have hn := signed_mass_nonneg χ δ 1 (-1)
  rcases hε with rfl | rfl <;> linarith

/-- Finite partial summation with all atoms below the upper endpoint.
Atoms at or below the lower endpoint are subtracted explicitly.
Derived elementary support for Lemma 4.3 and display 4.32 on page 39. -/
theorem finite_atom_interval_partial_summation {ι : Type*} (s : Finset ι)
    (γ w : ι → ℝ) (f f' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ i ∈ s, γ i ≤ b)
    (hf' : ContinuousOn f' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) :
    (∑ i ∈ s, if a < γ i then w i * f (γ i) else 0) =
      f b * (∑ i ∈ s, w i) - f a * (∑ i ∈ s, if γ i ≤ a then w i else 0) -
      ∫ t in a..b, f' t * (∑ i ∈ s, if γ i < t then w i else 0) := by
  classical
  have hclamp : ∀ i ∈ s, max a (γ i) ∈ Icc a b := by
    intro i hi
    exact ⟨le_max_left _ _, max_le hab (hγ i hi)⟩
  have hbase := finite_atom_partial_summation s (fun i => max a (γ i)) w f f' a b hab hclamp hf' hd
  have hsum : (∑ i ∈ s, w i * f (max a (γ i))) =
      (∑ i ∈ s, if a < γ i then w i * f (γ i) else 0) +
        f a * (∑ i ∈ s, if γ i ≤ a then w i else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : a < γ i
    · simp [max_eq_right h.le, h, not_le.mpr h]
    · simp [max_eq_left (le_of_not_gt h), h, le_of_not_gt h, mul_comm]
  have hint : (∫ t in a..b, f' t * (∑ i ∈ s, if max a (γ i) < t then w i else 0)) =
      ∫ t in a..b, f' t * (∑ i ∈ s, if γ i < t then w i else 0) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hab] at ht
    simp [max_lt_iff, ht.1]
  rw [hsum, hint] at hbase
  linarith

/-- The derivative of a complex profile norm is bounded by the norm of its derivative.
At a zero the total real derivative of the norm is zero by its local minimum.
Derived support for the inequality used in P0014 page 40. -/
theorem norm_deriv_norm_le {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    ‖deriv (fun u => ‖f u‖) t‖ ≤ ‖f'‖ := by
  by_cases h0 : f t = 0
  · have hm : IsLocalMin (fun u => ‖f u‖) t := by
      apply Filter.Eventually.of_forall
      intro u
      simp only [h0, norm_zero]
      exact norm_nonneg _
    rw [hm.deriv_eq_zero, norm_zero]
    exact norm_nonneg _
  · have hn : DifferentiableAt ℝ (fun u => ‖f u‖) t := hf.differentiableAt.norm ℝ h0
    have he := (hn.hasDerivAt.pow 2).unique hf.norm_sq
    norm_num only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at he
    have hi := abs_le.mp (abs_real_inner_le_norm (f t) f')
    have hp : 0 < ‖f t‖ := norm_pos_iff.mpr h0
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith [hi.1]
    · apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith [hi.2]

/-- The signed Gaussian norm profile is absolutely continuous on every finite interval.
Mathlib composition with the Lipschitz norm supplies the regularity required by
P0014 display 4.32 on page 39 and the derivative integral on page 40. -/
theorem gaussian_norm_absolutelyContinuous (δ ε a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖) a b := by
  have hc : ContDiffOn ℝ 1
      (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)) (uIcc a b) := by
    intro t ht
    have ha : AnalyticAt ℂ (gaussianMellin δ)
        ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) :=
      LeanLab.HelfgottMajor.Decomp389b.gaussian_mellin_analyticAt δ _ (by norm_num) (by norm_num)
    have ho : ContDiffAt ℝ 1 (gaussianMellin δ)
        ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) := ha.contDiffAt.restrict_scalars ℝ
    have hco : ContDiffAt ℝ 1 ((↑) : ℝ → ℂ) (ε * t) :=
      Complex.ofRealCLM.contDiff.contDiffAt
    have hx : ContDiffAt ℝ 1 (fun u : ℝ => ε * u) t := contDiffAt_const.mul contDiffAt_id
    have hi : ContDiffAt ℝ 1 (fun u : ℝ => (ε * u : ℝ) * Complex.I) t :=
      (hco.comp t hx).mul contDiffAt_const
    have hp : ContDiffAt ℝ 1 (fun u : ℝ => (1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I) t :=
      contDiffAt_const.add hi
    exact (ho.comp t hp).contDiffWithinAt
  exact lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hc.absolutelyContinuousOnInterval

/-- Chain differentiation of the signed critical line Gaussian profile.
Derived support for display 4.31 on page 39. -/
theorem gaussian_profile_hasDerivAt (δ ε t : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I))
      (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) *
        ((ε : ℂ) * Complex.I)) t := by
  have hg : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + (ε : ℂ) * z * Complex.I)
      ((ε : ℂ) * Complex.I) (t : ℂ) := by
    convert (((hasDerivAt_id (t : ℂ)).const_mul (ε : ℂ)).mul_const Complex.I).const_add
      (1 / 2 : ℂ) using 1 <;> simp
  have ha : AnalyticAt ℂ (gaussianMellin δ)
      ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I) :=
    LeanLab.HelfgottMajor.Decomp389b.gaussian_mellin_analyticAt δ _ (by norm_num) (by norm_num)
  have hh' : HasDerivAt (gaussianMellin δ)
      (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε : ℂ) * (t : ℂ) * Complex.I))
      ((1 / 2 : ℂ) + (ε : ℂ) * (t : ℂ) * Complex.I) := by
    simpa only [Complex.ofReal_mul] using ha.differentiableAt.hasDerivAt
  simpa only [Function.comp_apply, Complex.ofReal_mul] using
    (hh'.comp (t : ℂ) hg).comp_ofReal

/-- The real derivative of the signed Gaussian norm is bounded by the complex Mellin derivative.
This uses the actual chain rule, with no reflection at fixed twist.
Derived support for the derivative integral on page 40. -/
theorem gaussian_norm_derivative_bound (δ ε t : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ‖deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I)‖) t‖ ≤
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ := by
  have h := norm_deriv_norm_le (gaussian_profile_hasDerivAt δ ε t)
  have hc : ‖(ε : ℂ) * Complex.I‖ = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  simpa only [norm_mul, hc, mul_one] using h

/-- Finite atom partial summation for an absolutely continuous real test.
The derivative is the almost everywhere real derivative.
Derived support for Lemma 4.3 and display 4.32 on page 39. -/
theorem finite_atom_partial_summation_ac {ι : Type*} (s : Finset ι)
    (γ w : ι → ℝ) (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ i ∈ s, γ i ∈ Icc a b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∑ i ∈ s, w i * f (γ i)) = f b * (∑ i ∈ s, w i) -
      ∫ t in a..b, (deriv f) t * (∑ i ∈ s, if γ i < t then w i else 0) := by
  classical
  have hfi : IntervalIntegrable (deriv f) volume a b := hf.intervalIntegrable_deriv
  have hi (i : ι) : IntervalIntegrable ((Ioi (γ i)).indicator (fun t => w i * (deriv f) t)) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    exact (hfi.1.const_mul (w i)).indicator measurableSet_Ioi
  have heq : (fun t => (deriv f) t * (∑ i ∈ s, if γ i < t then w i else 0)) =
      fun t => ∑ i ∈ s, (Ioi (γ i)).indicator (fun t => w i * (deriv f) t) t := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ht : γ i < t <;> simp [Set.indicator, ht, mul_comm]
  rw [heq, intervalIntegral.integral_finsetSum (fun i (_ : i ∈ s) => hi i)]
  have hone (i : ι) (his : i ∈ s) :
      (∫ t in a..b, (Ioi (γ i)).indicator (fun t => w i * (deriv f) t) t) = w i * (f b - f (γ i)) := by
    rw [integral_tail_indicator _ _ _ _ (hγ i his).1 (hγ i his).2,
      intervalIntegral.integral_const_mul]
    congr 1
    apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    apply hf.mono
    rw [uIcc_of_le (hγ i his).2, uIcc_of_le hab]
    exact Icc_subset_Icc (hγ i his).1 le_rfl
  rw [Finset.sum_congr rfl hone]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- The finite interval atom identity for an absolutely continuous real test.
The lower endpoint count is subtracted explicitly.
Derived support for Lemma 4.3 and display 4.32 on page 39. -/
theorem finite_atom_interval_partial_summation_ac {ι : Type*} (s : Finset ι)
    (γ w : ι → ℝ) (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ i ∈ s, γ i ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∑ i ∈ s, if a < γ i then w i * f (γ i) else 0) =
      f b * (∑ i ∈ s, w i) - f a * (∑ i ∈ s, if γ i ≤ a then w i else 0) -
      ∫ t in a..b, (deriv f) t * (∑ i ∈ s, if γ i < t then w i else 0) := by
  classical
  have hclamp : ∀ i ∈ s, max a (γ i) ∈ Icc a b := by
    intro i hi
    exact ⟨le_max_left _ _, max_le hab (hγ i hi)⟩
  have hbase := finite_atom_partial_summation_ac s (fun i => max a (γ i)) w f a b hab hclamp hf
  have hsum : (∑ i ∈ s, w i * f (max a (γ i))) =
      (∑ i ∈ s, if a < γ i then w i * f (γ i) else 0) +
        f a * (∑ i ∈ s, if γ i ≤ a then w i else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : a < γ i
    · simp [max_eq_right h.le, h, not_le.mpr h]
    · simp [max_eq_left (le_of_not_gt h), h, le_of_not_gt h, mul_comm]
  have hint : (∫ t in a..b, (deriv f) t * (∑ i ∈ s, if max a (γ i) < t then w i else 0)) =
      ∫ t in a..b, (deriv f) t * (∑ i ∈ s, if γ i < t then w i else 0) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hab] at ht
    simp [max_lt_iff, ht.1]
  rw [hsum, hint] at hbase
  linarith

/-- Quantitative finite atom partial summation from an explicit cumulative count envelope.
The envelope is needed almost everywhere inside the interval and at both endpoints.
CONDITIONAL ON the three supplied count bounds.
Derived support for Lemma 4.3 and display 4.32 on page 39. -/
theorem finite_atom_count_error_bound {ι : Type*} (s : Finset ι)
    (γ w : ι → ℝ) (f M g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ i ∈ s, γ i ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hM : AbsolutelyContinuousOnInterval M a b)
    (hg : ContinuousOn g (uIcc a b))
    (hcount : ∀ᵐ t ∂volume.restrict (Icc a b),
      |(∑ i ∈ s, if γ i < t then w i else 0) - M t| ≤ g t)
    (hupper : |(∑ i ∈ s, w i) - M b| ≤ g b)
    (hlower : |(∑ i ∈ s, if γ i ≤ a then w i else 0) - M a| ≤ g a) :
    (∑ i ∈ s, if a < γ i then w i * f (γ i) else 0) ≤
      (∫ t in a..b, f t * deriv M t) + |f b| * g b + |f a| * g a +
      ∫ t in a..b, |deriv f t| * g t := by
  classical
  let C : ℝ → ℝ := fun t => ∑ i ∈ s, if γ i < t then w i else 0
  have hfi := hf.intervalIntegrable_deriv
  have hi (i : ι) : IntervalIntegrable ((Ioi (γ i)).indicator (fun t => w i * deriv f t)) volume a b := by
    exact ⟨(hfi.1.const_mul (w i)).indicator measurableSet_Ioi,
      (hfi.2.const_mul (w i)).indicator measurableSet_Ioi⟩
  have hC : IntervalIntegrable (fun t => deriv f t * C t) volume a b := by
    have heq : (fun t => deriv f t * C t) =
        fun t => ∑ i ∈ s, (Ioi (γ i)).indicator (fun t => w i * deriv f t) t := by
      funext t
      dsimp [C]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases ht : γ i < t <;> simp [Set.indicator, ht, mul_comm]
    rw [heq]
    have heFun : (∑ i ∈ s, (Ioi (γ i)).indicator (fun t => w i * deriv f t)) =
        (fun t => ∑ i ∈ s, (Ioi (γ i)).indicator (fun t => w i * deriv f t) t) := by
      ext t
      simp only [Finset.sum_apply]
    rw [← heFun]
    exact IntervalIntegrable.sum s (fun i _ => hi i)
  have hmi := hfi.mul_continuousOn hM.continuousOn
  have hri : IntervalIntegrable (fun t => -(deriv f t) * (C t - M t)) volume a b := by
    convert (hC.sub hmi).neg using 1
    funext t
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  have hgi : IntervalIntegrable (fun t => |deriv f t| * g t) volume a b := by
    simpa only [Real.norm_eq_abs] using hfi.norm.mul_continuousOn hg
  have hpoint : (fun t => -(deriv f t) * (C t - M t)) ≤ᵐ[volume.restrict (Icc a b)]
      (fun t => |deriv f t| * g t) := by
    filter_upwards [hcount] with t ht
    calc
      _ ≤ |-(deriv f t) * (C t - M t)| := le_abs_self _
      _ = |deriv f t| * |C t - M t| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hInt := intervalIntegral.integral_mono_ae_restrict hab hri hgi hpoint
  have hri_eq : (∫ t in a..b, -(deriv f t) * (C t - M t)) =
      (∫ t in a..b, deriv f t * M t) - (∫ t in a..b, deriv f t * C t) := by
    rw [← intervalIntegral.integral_sub hmi hC]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hup : f b * ((∑ i ∈ s, w i) - M b) ≤ |f b| * g b := by
    calc
      _ ≤ |f b * ((∑ i ∈ s, w i) - M b)| := le_abs_self _
      _ = |f b| * |(∑ i ∈ s, w i) - M b| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hupper (abs_nonneg _)
  have hlo : -f a * ((∑ i ∈ s, if γ i ≤ a then w i else 0) - M a) ≤ |f a| * g a := by
    calc
      _ ≤ |-f a * ((∑ i ∈ s, if γ i ≤ a then w i else 0) - M a)| := le_abs_self _
      _ = |f a| * |(∑ i ∈ s, if γ i ≤ a then w i else 0) - M a| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (abs_nonneg _)
  have hAbel := finite_atom_interval_partial_summation_ac s γ w f a b hab hγ hf
  have hparts := hf.integral_mul_deriv_eq_deriv_mul hM
  change (∑ i ∈ s, if a < γ i then w i * f (γ i) else 0) =
    f b * (∑ i ∈ s, w i) - f a * (∑ i ∈ s, if γ i ≤ a then w i else 0) -
      ∫ t in a..b, deriv f t * C t at hAbel
  nlinarith

/-- The signed half endpoint count uses chi for positive heights and its inverse for negative heights.
This is the count convention of book page 431, used for P0014 display 4.32 on page 39. -/
theorem half_count_signed_formula {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    bookCount (if ε = 1 then χ else χ⁻¹) T =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        halfWeight T (ε * ρ.im) * (mult χ ρ : ℝ) := by
  classical
  rcases hε with rfl | rfl
  · simp only [if_pos rfl, one_mul]
    rfl
  · rw [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    simpa only [neg_one_mul, neg_nonneg] using bookCount_inv χ T

/-- The signed book count just to the right gives full weight at the upper endpoint.
It preserves half weight at height zero. Derived endpoint support for display 4.32 on page 39. -/
theorem signed_book_count_right_eventually {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T ε : ℝ) (hT : 0 < T) (hε : ε = 1 ∨ ε = -1) :
    ∀ᶠ t in 𝓝[>] T, bookCount (if ε = 1 then χ else χ⁻¹) t =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ) := by
  classical
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨r, hr, hgap⟩ := exists_gap χ T
  filter_upwards [Ioo_mem_nhdsGT (show T < T + r by linarith)] with t ht
  rw [half_count_signed_formula χ t ε hε]
  have hsets : (stripZeros_finite χ t).toFinset = (stripZeros_finite χ T).toFinset := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, hgap t ht.1 ht.2]
  rw [hsets]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρs : ρ ∈ stripZeros χ T := by simpa using (Finset.mem_filter.mp hρ).1
  have hb : ε * ρ.im ≤ T := by
    calc
      _ ≤ |ε * ρ.im| := le_abs_self _
      _ = |ρ.im| := by rw [abs_mul, habs, one_mul]
      _ ≤ T := hρs.2.2.2
  have hne : ε * ρ.im ≠ t := by intro he; rw [he] at hb; linarith [ht.1]
  by_cases h0 : ε * ρ.im = 0
  · simp [halfWeight, h0]
    ring
  · simp [halfWeight, h0, hne]

/-- The signed finite atom count inherits the continuous numerical half count envelope.
CONDITIONAL ON the explicit signed count family.
Derived quantitative count support for display 4.32 on page 39. -/
theorem signed_finite_count_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T ε : ℝ) (hT : 1 ≤ T) (hε : ε = 1 ∨ ε = -1)
    (hcount : ∀ t : ℝ, 1 ≤ t →
      |bookCount (if ε = 1 then χ else χ⁻¹) t - bookMain q t| ≤ bookError q t) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
      if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)) - bookMain q T| ≤
      bookError q T := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hT0 : 0 < T := by linarith
  have hmain : ContinuousAt (fun t => bookMain q t) T := by
    unfold bookMain
    have hne : (q : ℝ) * T / (2 * π * exp 1) ≠ 0 := by positivity
    exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)
  have herr : ContinuousAt (fun t => bookError q t) T := by
    unfold bookError
    exact ContinuousAt.add (ContinuousAt.mul (by fun_prop)
      (ContinuousAt.log (by fun_prop) (mul_ne_zero hq hT0.ne'))) (by fun_prop)
  have hev : ∀ᶠ t in 𝓝[>] T,
      |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)) - bookMain q t| ≤
          bookError q t := by
    filter_upwards [signed_book_count_right_eventually χ T ε hT0 hε, self_mem_nhdsWithin]
      with t he ht
    rw [← he]
    exact hcount t (hT.trans ht.le)
  exact le_of_tendsto_of_tendsto
    ((continuousAt_const.sub hmain).abs.tendsto.mono_left nhdsWithin_le_nhds)
    (herr.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- Restriction of the signed finite strip sum to a smaller height is exact.
Derived finite count transport for display 4.32 on page 39. -/
theorem signed_strip_cutoff_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (F : ℂ → ℝ) (T U ε : ℝ) (hUT : U ≤ T) (hε : ε = 1 ∨ ε = -1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
      if ε * ρ.im ≤ U then F ρ else 0) =
      ∑ ρ ∈ (stripZeros_finite χ U).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im), F ρ := by
  classical
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have he (ρ : ℂ) (hp : 0 ≤ ε * ρ.im) : |ρ.im| = ε * ρ.im := by
    calc
      _ = |ε * ρ.im| := by rw [abs_mul, habs, one_mul]
      _ = _ := abs_of_nonneg hp
  rw [← Finset.sum_filter]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨hρ, hp⟩, hu⟩
    exact ⟨⟨hρ.1, hρ.2.1, hρ.2.2.1, (he ρ hp).trans_le hu⟩, hp⟩
  · rintro ⟨hρ, hp⟩
    exact ⟨⟨⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans hUT⟩, hp⟩,
      (he ρ hp).symm.trans_le hρ.2.2.2⟩

/-- Strict and closed finite cumulative weights agree almost everywhere.
Finite real atom heights have Lebesgue measure zero.
Derived endpoint support for display 4.32 on page 39. -/
theorem finite_cumulative_lt_eq_le_ae {ι : Type*} (s : Finset ι) (γ w : ι → ℝ) :
    (fun t : ℝ => ∑ i ∈ s, if γ i < t then w i else 0) =ᵐ[volume]
      (fun t : ℝ => ∑ i ∈ s, if γ i ≤ t then w i else 0) := by
  classical
  have hev := (s.finite_toSet.image γ).countable.ae_notMem (volume : Measure ℝ)
  filter_upwards [hev] with t ht
  apply Finset.sum_congr rfl
  intro i hi
  have hne : γ i ≠ t := by
    intro he
    exact ht ⟨i, hi, he⟩
  by_cases h : γ i < t
  · simp [h, h.le]
  · have hle : ¬γ i ≤ t := by
      intro hle
      rcases lt_or_eq_of_le hle with hl | he
      · exact h hl
      · exact hne he
    simp [h, hle]

/-- The book count main term has derivative log of qt over two pi, divided by two pi.
Derived calculus for book page 431 and display 4.32 on page 39. -/
theorem bookMain_hasDerivAt (q : ℕ) [NeZero q] (t : ℝ) (ht : 0 < t) :
    HasDerivAt (bookMain q) (log ((q : ℝ) * t / (2 * π)) / (2 * π)) t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hratio := (((hasDerivAt_id t).const_mul (q : ℝ)).div_const (2 * π * exp 1))
  have hlog := hratio.log (show (q : ℝ) * t / (2 * π * exp 1) ≠ 0 by positivity)
  have hmain := ((hasDerivAt_id t).div_const (2 * π)).mul hlog
  have he : log ((q : ℝ) * t / (2 * π * exp 1)) = log ((q : ℝ) * t / (2 * π)) - 1 := by
    rw [log_div (mul_ne_zero hq.ne' ht.ne') (show 2 * π * exp 1 ≠ 0 by positivity),
      log_div (mul_ne_zero hq.ne' ht.ne') (show 2 * π ≠ 0 by positivity),
      log_mul (show 2 * π ≠ 0 by positivity) (exp_ne_zero 1), log_exp]
    ring
  convert hmain using 1
  · rfl
  · simp only [id_eq, mul_one]
    rw [he]
    field_simp [hq.ne', ht.ne', Real.pi_ne_zero, exp_ne_zero]
    ring

/-- The book main term is absolutely continuous on each finite interval above height one.
Derived calculus for book page 431 and display 4.32 on page 39. -/
theorem bookMain_absolutelyContinuous (q : ℕ) [NeZero q] (T : ℝ) (hT : 1 ≤ T) :
    AbsolutelyContinuousOnInterval (bookMain q) 1 T := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply ContDiffOn.absolutelyContinuousOnInterval
  intro t ht
  rw [uIcc_of_le hT] at ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  apply ContDiffAt.contDiffWithinAt
  unfold bookMain
  fun_prop (disch := positivity)

/-- The critical line writes the signed middle mass as the finite atom test sum.
The sign is kept in the profile. No fixed twist reflection is used.
P0014 display 4.32 on page 39. -/
theorem signed_mass_as_atoms {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    signedMass χ δ T ε =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        if 1 < ε * ρ.im then
          (if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * (ε * ρ.im) : ℝ) * Complex.I)‖ else 0 := by
  classical
  rw [signed_mass_on_line χ δ T ε hzeros]
  let F : ℂ → ℝ := fun ρ => if 1 < ε * ρ.im then
    (mult χ ρ : ℝ) * ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.im : ℝ) * Complex.I)‖ else 0
  have heq : (∑' ρ : ZeroIdx χ T,
      {ρ | 1 < ε * ρ.val.im}.indicator
        (fun ρ => (mult χ ρ.val : ℝ) *
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) =
      ∑' ρ : ZeroIdx χ T, F ρ.val := by
    apply tsum_congr
    intro ρ
    rfl
  rw [heq, tsum_zeroIdx χ T F, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases h : 1 < ε * ρ.im
  · have hp : 0 ≤ ε * ρ.im := by linarith
    have hne : ε * ρ.im ≠ 0 := by linarith
    have he : ε * (ε * ρ.im) = ρ.im := by rcases hε with rfl | rfl <;> ring
    simp [F, h, hp, hne, he]
  · simp [F, h]

/-- Finite signed partial summation from Lemma 4.3 and display 4.32 on page 39.
The error envelope is the sharper signed count on book pages 431 to 434.
Only the conversion of zero samples to continuous integrals is asserted here.
Both finite endpoints are explicit. Cauchy Schwarz and all Gaussian energies are separate.
For the negative sign the quantitative count belongs to the inverse character.
CONDITIONAL ON the explicit numerical count family. The sampling proof has no admission. -/
theorem one_sign_partial_summation (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) (hT : 1 ≤ T) (hε : ε = 1 ∨ ε = -1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : ∀ t : ℝ, 1 ≤ t →
      |ZeroCount1623.bookCount (if ε = 1 then χ else χ⁻¹) t -
        ZeroCount1623.bookMain q t| ≤ ZeroCount1623.bookError q t) :
    signedMass χ δ T ε ≤
      (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ *
          |log ((q : ℝ) * t / (2 * π))|) / (2 * π) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε : ℂ) * Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * T : ℝ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  classical
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  let s := (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im)
  let γ : ℂ → ℝ := fun ρ => ε * ρ.im
  let w : ℂ → ℝ := fun ρ => if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)
  let f : ℝ → ℝ := fun t => ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖
  have hAll : ∀ ρ ∈ s, γ ρ ≤ T := by
    intro ρ hρ
    have hρs : ρ ∈ stripZeros χ T := by simpa [s] using (Finset.mem_filter.mp hρ).1
    calc
      γ ρ ≤ |ε * ρ.im| := le_abs_self _
      _ = |ρ.im| := by rw [abs_mul, habs, one_mul]
      _ ≤ _ := hρs.2.2.2
  have hclosed (t : ℝ) (ht : t ∈ Icc 1 T) :
      |(∑ ρ ∈ s, if γ ρ ≤ t then w ρ else 0) - bookMain q t| ≤ bookError q t := by
    change |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
      if ε * ρ.im ≤ t then w ρ else 0) - bookMain q t| ≤ bookError q t
    rw [signed_strip_cutoff_sum χ w T t ε ht.2 hε]
    exact signed_finite_count_bound χ t ε ht.1 hε hcount
  have hupper : |(∑ ρ ∈ s, w ρ) - bookMain q T| ≤ bookError q T :=
    signed_finite_count_bound χ T ε hT hε hcount
  have hlower := hclosed 1 ⟨le_rfl, hT⟩
  have hAE : ∀ᵐ t ∂volume.restrict (Icc 1 T),
      |(∑ ρ ∈ s, if γ ρ < t then w ρ else 0) - bookMain q t| ≤ bookError q t := by
    filter_upwards [ae_restrict_of_ae (finite_cumulative_lt_eq_le_ae s γ w),
      ae_restrict_mem measurableSet_Icc] with t he ht
    rw [he]
    exact hclosed t ht
  have hfac : AbsolutelyContinuousOnInterval f 1 T := gaussian_norm_absolutelyContinuous δ ε 1 T
  have hg : ContinuousOn (bookError q) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    unfold bookError
    fun_prop (disch := positivity)
  have hAbel := finite_atom_count_error_bound s γ w f (bookMain q) (bookError q) 1 T hT
    hAll hfac (bookMain_absolutelyContinuous q T hT) hg hAE hupper hlower
  have hmass : signedMass χ δ T ε =
      ∑ ρ ∈ s, if 1 < γ ρ then w ρ * f (γ ρ) else 0 := by
    exact signed_mass_as_atoms χ δ T ε hε hzeros
  rw [← hmass] at hAbel
  have hfc : ContinuousOn f (uIcc 1 T) := (signed_profile_continuous δ ε).norm.continuousOn
  have hlogc : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t / (2 * π))) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hmainEq : (∫ t in (1 : ℝ)..T, f t * deriv (bookMain q) t) =
      (∫ t in (1 : ℝ)..T, f t * log ((q : ℝ) * t / (2 * π))) / (2 * π) := by
    calc
      _ = ∫ t in (1 : ℝ)..T, (1 / (2 * π)) * (f t * log ((q : ℝ) * t / (2 * π))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        dsimp only
        rw [(bookMain_hasDerivAt q t (lt_of_lt_of_le zero_lt_one ht.1)).deriv]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]; ring
  have hmainLe : (∫ t in (1 : ℝ)..T, f t * deriv (bookMain q) t) ≤
      (∫ t in (1 : ℝ)..T, f t * |log ((q : ℝ) * t / (2 * π))|) / (2 * π) := by
    rw [hmainEq]
    apply div_le_div_of_nonneg_right _ (show 0 ≤ 2 * π by positivity)
    apply intervalIntegral.integral_mono_on hT
      (hfc.mul hlogc).intervalIntegrable (hfc.mul hlogc.abs).intervalIntegrable
    intro t ht
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
  have hdi : IntervalIntegrable (fun t => |deriv f t| * bookError q t) volume 1 T := by
    simpa only [Real.norm_eq_abs] using hfac.intervalIntegrable_deriv.norm.mul_continuousOn hg
  have hdc : ContinuousOn (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖) (uIcc 1 T) :=
    (signed_derivative_profile_continuous δ ε).norm.continuousOn
  have herrLe : (∫ t in (1 : ℝ)..T, |deriv f t| * bookError q t) ≤
      ∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ * bookError q t := by
    apply intervalIntegral.integral_mono_on hT hdi (hdc.mul hg).intervalIntegrable
    intro t ht
    have ht1 : 1 ≤ (q : ℝ) * t := by nlinarith [ht.1]
    have hg0 : 0 ≤ bookError q t := by
      unfold bookError
      have := log_nonneg ht1
      linarith
    have hn : |deriv f t| ≤
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ := by
      simpa only [f, Real.norm_eq_abs] using gaussian_norm_derivative_bound δ ε t hε
    exact mul_le_mul_of_nonneg_right hn hg0
  dsimp only [f, bookError] at hAbel hmainLe herrLe
  simp only [abs_norm, mul_one] at hAbel
  nlinarith

/-- Finite one sign form of Lemma 4.3 and display 4.32, page 39.
The two Cauchy Schwarz factors are left as finite weight integrals.
The quantitative count is an explicit independent input.
The finite upper endpoint is retained, as required by integration by parts.
For the negative sign the count is taken for the inverse character.
No fixed twist reflection or discrete full mass bound is used. -/
theorem one_sign_finite_sampling (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) (hT : 1 ≤ T) (hε : ε = 1 ∨ ε = -1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : ∀ t : ℝ, 1 ≤ t →
      |ZeroCount1623.bookCount (if ε = 1 then χ else χ⁻¹) t -
        ZeroCount1623.bookMain q t| ≤ ZeroCount1623.bookError q t) :
    signedMass χ δ T ε ≤
      sqrt (lineEnergy δ ε) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ ε) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε : ℂ) * Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * T : ℝ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hfc : ContinuousOn (fun t : ℝ =>
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖) (Icc 1 T) :=
    (signed_profile_continuous δ ε).norm.continuousOn
  have hdc : ContinuousOn (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖) (Icc 1 T) :=
    (signed_derivative_profile_continuous δ ε).norm.continuousOn
  have hmc : ContinuousOn (fun t : ℝ => |log ((q : ℝ) * t / (2 * π))|) (Icc 1 T) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hec : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389) (Icc 1 T) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hM := interval_cauchy_schwarz _ _ T hT hfc hmc
    (fun _ _ => norm_nonneg _) (fun _ _ => abs_nonneg _)
  simp_rw [sq_abs] at hM
  have hD := interval_cauchy_schwarz _ _ T hT hdc hec
    (fun _ _ => norm_nonneg _) (by
      intro t ht
      have ht1 : (1 : ℝ) ≤ (q : ℝ) * t := by nlinarith [ht.1]
      have := log_nonneg ht1
      linarith)
  have hFE : (∫ t in (1 : ℝ)..T,
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2) ≤ lineEnergy δ ε := by
    rw [intervalIntegral.integral_of_le hT]
    apply setIntegral_mono_set (signed_profile_sq_integrable δ ε hε).integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    filter_upwards with t ht
    exact lt_trans zero_lt_one ht.1
  have hDE : (∫ t in (1 : ℝ)..T,
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2) ≤
      derivativeEnergy δ ε := by
    rw [intervalIntegral.integral_of_le hT]
    apply setIntegral_mono_set (signed_derivative_profile_sq_integrable δ ε hε).integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    filter_upwards with t ht
    exact ht.1
  have hM' := hM.trans (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hFE) (sqrt_nonneg _))
  have hD' := hD.trans (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hDE) (sqrt_nonneg _))
  have hm := div_le_div_of_nonneg_right hM' (show 0 ≤ 2 * π by positivity)
  have hraw := one_sign_partial_summation q χ δ T ε hT hε hzeros hcount
  apply hraw.trans
  convert add_le_add (add_le_add (add_le_add hm hD') le_rfl) le_rfl using 1 <;> ring

/-- A coarse lower bound for the log weighted Gaussian norm of display 4.42, page 43. -/
theorem sqrt_nLog_lower : (1.1 : ℝ) ≤ sqrt Sec45.nLog := by
  have hg : 0 ≤ eulerMascheroniConstant := by
    linarith [LeanLab.Helfgott2013.GammaFine.gamma_gt_fine]
  have hl : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hb : 12 ≤ π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
      8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 := by
    nlinarith [pi_gt_three, log_two_gt_d9, mul_nonneg hg hl,
      sq_nonneg eulerMascheroniConstant]
  have hn : (1.3 : ℝ) ≤ Sec45.nLog := by
    unfold Sec45.nLog
    have hm := mul_le_mul (show (1.77 : ℝ) / 16 ≤ sqrt π / 16 by
      linarith [Sec45.sqrt_pi_gt]) hb (by norm_num : (0 : ℝ) ≤ 12) (by positivity)
    linarith
  exact (le_sqrt (by norm_num) Sec45.nLog_nonneg).mpr (by nlinarith)

/-- The coefficient of sqrt T on page 40 is at least fifteen.
This is a coarse scalar comparison with the norms of display 4.42 on page 43. -/
theorem middle_constant_lower :
    (15 : ℝ) ≤ 17.21 * sqrt Sec45.nLog -
      log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have hN := Sec45.sqrt_nTwo_lt
  have hL := sqrt_nLog_lower
  have hC := BookP1617.K_bds
  have hp := mul_le_mul hC.2.le hN.le (sqrt_nonneg _) (by norm_num)
  nlinarith

/-- Scalar absorption of the finite upper endpoint into the printed page 40 budget.
The energy coefficients come from the one sign Plancherel bounds.
This is derived arithmetic, not a replacement sampling hypothesis. -/
theorem finite_endpoint_absorption (s L lq : ℝ) (hs : 1.4 ≤ s) (hL : 0 ≤ L)
    (hlq : 0 ≤ lq) :
    (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) * s * L +
      11.497 * sqrt Sec45.nLog * s + 2.15581 * (0.3 * lq + 6.778) +
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * (0.15 * L + 3.389) ≤
    (sqrt Sec45.nTwo + sqrt Sec45.nLog) * s * L +
      (17.21 * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * s +
      2.15581 * (0.5 * lq + 17.7) := by
  have hN0 := sqrt_nonneg Sec45.nTwo
  have hL0 := sqrt_nonneg Sec45.nLog
  have hNlo := Sec45.sqrt_nTwo_gt
  have hNhi := Sec45.sqrt_nTwo_lt
  have hLlo := sqrt_nLog_lower
  have hLhi := Sec45.sqrt_nLog_lt
  have hC := BookP1617.K_bds
  have hprod := mul_le_mul hC.2.le hNhi.le hN0 (by norm_num)
  have hA : (0.9 : ℝ) ≤ sqrt Sec45.nTwo + sqrt Sec45.nLog -
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) := by linarith
  have hB : (4 : ℝ) ≤ 17.21 * sqrt Sec45.nLog -
      log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo - 11.497 * sqrt Sec45.nLog := by
    nlinarith
  have hEL : 3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 0.15 ≤ (1.25 : ℝ) := by
    linarith
  have hEC : 3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 3.389 ≤ (28.1 : ℝ) := by
    linarith
  have hAs := mul_le_mul_of_nonneg_right hA (show 0 ≤ s by linarith)
  have hBs := mul_le_mul_of_nonneg_right hB (show 0 ≤ s by linarith)
  have hAL : 0 ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog -
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog)) * s -
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 0.15 := by linarith
  have hp := mul_nonneg hAL hL
  nlinarith

/-- The trivial Mellin bound charges the middle mass to the strip multiplicity count.
P0014 page 39, display 4.30. The finite sum comparison has no quantitative count input. -/
theorem middle_mass_le_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤ 2.15581 * ∑' ρ : ZeroCount1623.ZeroIdx χ T,
      (ZeroCount1623.mult χ ρ.val : ℝ) := by
  classical
  haveI := ZeroCount1623.zeroIdx_finite χ T
  unfold middleMass
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
  intro ρ
  by_cases h : |ρ.val.im| ≤ 1
  · simp [Set.indicator, h]
    positivity
  · simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, h, not_false_eq_true,
      ite_true, mellinMassTerm]
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hn := mellin_critical_norm_le δ ρ.val hz
    simpa only [ZeroCount1623.mult, mul_comm] using
      mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (ZeroCount1623.mult χ ρ.val))

end LeanLab.HelfgottMajor.Decomp526a
