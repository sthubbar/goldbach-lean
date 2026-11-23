module

public import LeanLab.ExceptionalSet.WindowParseval264

/-!
Finite weighted Gallagher inequality with arbitrary real frequencies.
Source: Coppola and Laporta, arXiv 1411.1739, page 2 display triple star
and page 5 Plancherel proof. The weight is assumed to be in L1 and L2.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


open MeasureTheory FourierTransform
open scoped ENNReal

namespace LeanLab.ExceptionalSet.WeightedGallagher264

/-- Finite scalar weighted translates preserve Lp membership. -/
theorem memLp_sum_translates {ι : Type*} (s : Finset ι) (ν : ι → ℝ) (a : ι → ℂ)
    (f : ℝ → ℂ) {p : ℝ≥0∞} (hf : MemLp f p) :
    MemLp (fun x => ∑ n ∈ s, a n * f (x - ν n)) p := by
  apply memLp_finsetSum
  intro n hn
  have ht := hf.comp_measurePreserving (measurePreserving_add_right volume (-ν n))
  convert ht.const_smul (a n) using 1
  ext x
  simp [sub_eq_add_neg]

/-- The Fourier integral of finite weighted translates factors into the weight transform
and the exponential sum. -/
theorem fourier_sum_translates {ι : Type*} (s : Finset ι) (ν : ι → ℝ) (a : ι → ℂ)
    (f : ℝ → ℂ) (hf : Integrable f) (t : ℝ) :
    𝓕 (fun x => ∑ n ∈ s, a n * f (x - ν n)) t =
      (∑ n ∈ s, a n * Complex.exp ((-2 * Real.pi * t * Complex.I) * ν n)) * 𝓕 f t := by
  have hi (n : ι) : Integrable (fun x => a n * f (x - ν n)) := by
    simpa only [sub_eq_add_neg] using (hf.comp_add_right (-ν n)).const_mul (a n)
  rw [Real.fourier_eq]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum]
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (innerₗ ℝ) f (-ν n)) t
    have ht' : 𝓕 (fun x => f (x - ν n)) t =
        Complex.exp ((-2 * Real.pi * t * Complex.I) * ν n) * 𝓕 f t := by
      have he : (2 : ℂ) * Real.pi * (-((ν n : ℝ) : ℂ) * t) * Complex.I =
          (-2 * Real.pi * t * Complex.I) * ν n := by ring
      simpa only [Real.fourier_eq, VectorFourier.fourierIntegral,
        Function.comp_apply, sub_eq_add_neg, innerₗ_apply_apply,
        Real.inner_apply, Circle.smul_def, Real.fourierChar_apply,
        Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul, he] using ht
    calc
      _ = a n * 𝓕 (fun x => f (x - ν n)) t := by
        rw [Real.fourier_eq, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [Circle.smul_def, smul_eq_mul]
        ring
      _ = _ := by rw [ht']; ring
  · intro n hn
    exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ ℝ) (by fun_prop) t).2 (hi n)

/-- The finite weighted Gallagher inequality for real frequencies. -/
theorem weighted_gallagher {ι : Type*} (s : Finset ι) (ν : ι → ℝ) (a : ι → ℂ)
    (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) {T m : ℝ}
    (hT : 0 < T) (_hm : 0 ≤ m)
    (hmin : ∀ t ∈ Set.Icc (-T) T, m ≤ ‖𝓕 f t‖ ^ 2) :
    m * (∫ t in (-T)..T, ‖∑ n ∈ s, a n *
      Complex.exp ((-2 * Real.pi * t * Complex.I) * ν n)‖ ^ 2) ≤
      ∫ x : ℝ, ‖∑ n ∈ s, a n * f (x - ν n)‖ ^ 2 := by
  let C : ℝ → ℂ := fun x => ∑ n ∈ s, a n * f (x - ν n)
  let P : ℝ → ℂ := fun t => ∑ n ∈ s, a n *
    Complex.exp ((-2 * Real.pi * t * Complex.I) * ν n)
  have hC₁ : Integrable C := memLp_one_iff_integrable.mp
    (memLp_sum_translates s ν a f (memLp_one_iff_integrable.mpr h₁))
  have hC₂ : MemLp C 2 := memLp_sum_translates s ν a f h₂
  have hF := WindowParseval264.fourierIntegral_memLp C hC₁ hC₂
  have hFs : Integrable (fun t => ‖𝓕 C t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hFc : Continuous (𝓕 C) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hC₁
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -T ≤ T)
    (((hPc.norm.pow 2).const_mul m).intervalIntegrable (-T) T)
    ((hFc.norm.pow 2).intervalIntegrable (-T) T) (fun t ht => ?_)
  · change m * (∫ t in (-T)..T, ‖P t‖ ^ 2) ≤ _
    calc
      _ = ∫ t in (-T)..T, m * ‖P t‖ ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ t in (-T)..T, ‖𝓕 C t‖ ^ 2 := hi
      _ ≤ ∫ t : ℝ, ‖𝓕 C t‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
        exact integral_mono_measure Measure.restrict_le_self
          (by filter_upwards with t; positivity) hFs
      _ = _ := WindowParseval264.integral_norm_sq_fourier C hC₁ hC₂
  · have hw := congrArg norm (fourier_sum_translates s ν a f h₁ t)
    change ‖𝓕 C t‖ = ‖P t * 𝓕 f t‖ at hw
    rw [norm_mul] at hw
    calc m * ‖P t‖ ^ 2 ≤ ‖𝓕 f t‖ ^ 2 * ‖P t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hmin t ht) (sq_nonneg _)
         _ = ‖𝓕 C t‖ ^ 2 := by rw [hw]; ring

/-- A nonzero interval weight supplies a strictly positive Fourier lower bound. -/
theorem interval_weight_lower (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (1 / Real.pi) ^ 2 ≤
      ‖𝓕 (WindowParseval264.window {0} (fun _ => 1) (1 / 2)) t‖ ^ 2 := by
  have hlo : 1 / Real.pi ≤
      ‖𝓕 (WindowParseval264.window {0} (fun _ => 1) (1 / 2)) t‖ := by
    by_cases ht0 : t = 0
    · subst t
      have hw := WindowParseval264.fourier_interval (-1 / 2) 0 (by norm_num) 1 0
      have he : WindowParseval264.window {0} (fun _ => 1) (1 / 2) =
          (Set.Ico (-1 / 2 : ℝ) 0).indicator (fun _ => (1 : ℂ)) := by
        funext x
        simp only [WindowParseval264.window, Finset.sum_singleton]
        norm_num
      rw [he, hw]
      norm_num
      have hpi : 1 / Real.pi ≤ (1 : ℝ) / 2 :=
        (div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 2)).mpr
          (by nlinarith [Real.two_le_pi])
      simpa only [one_div] using hpi
    · rw [WindowParseval264.fourier_window {0} (fun _ => 1) (by norm_num) ht0]
      simp only [Finset.sum_singleton, Int.cast_zero, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, mul_one, one_mul]
      have hk := WindowParseval264.kernel_lower (T := 1) (t := t) (by norm_num) ht0
        (abs_le.mpr ht)
      simpa using hk
  exact pow_le_pow_left₀ (by positivity) hlo 2

/-- The interval weight lower bound at every positive frequency scale. -/
theorem interval_weight_lower_scaled {T : ℝ} (hT : 0 < T) (t : ℝ)
    (ht : t ∈ Set.Icc (-T) T) :
    (1 / (Real.pi * T)) ^ 2 ≤
      ‖𝓕 (WindowParseval264.window {0} (fun _ => 1) (1 / (2 * T))) t‖ ^ 2 := by
  have hlo : 1 / (Real.pi * T) ≤
      ‖𝓕 (WindowParseval264.window {0} (fun _ => 1) (1 / (2 * T))) t‖ := by
    by_cases ht0 : t = 0
    · subst t
      have he : WindowParseval264.window {0} (fun _ => 1) (1 / (2 * T)) =
          (Set.Ico (-(1 / (2 * T))) 0).indicator (fun _ => (1 : ℂ)) := by
        funext x
        simp only [WindowParseval264.window, Finset.sum_singleton, Int.cast_zero, zero_sub]
      rw [he, WindowParseval264.fourier_interval _ _ (neg_nonpos.mpr (by positivity)) 1 0]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
        intervalIntegral.integral_const, sub_neg_eq_add, zero_add, smul_eq_mul, mul_one,
        norm_mul, norm_one]
      rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one,
        abs_of_pos (by positivity : 0 < 1 / (2 * T))]
      apply (div_le_div_iff₀ (mul_pos Real.pi_pos hT) (by positivity : 0 < 2 * T)).mpr
      nlinarith [Real.two_le_pi]
    · rw [WindowParseval264.fourier_window {0} (fun _ => 1) (by positivity) ht0]
      simp only [Finset.sum_singleton, Int.cast_zero, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, mul_one, one_mul]
      exact WindowParseval264.kernel_lower hT ht0 (abs_le.mpr ht)
  exact pow_le_pow_left₀ (by positivity) hlo 2

/-- A finite family of interval translates gives the usual moving window sum. -/
theorem translated_window_sum {ι : Type*} (s : Finset ι) (ν : ι → ℝ) (a : ι → ℂ)
    (h x : ℝ) :
    (∑ n ∈ s, a n * WindowParseval264.window {0} (fun _ => 1) h (x - ν n)) =
      ∑ n ∈ s.filter (fun n => x < ν n ∧ ν n ≤ x + h), a n := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [WindowParseval264.window, Finset.sum_singleton, Int.cast_zero, zero_sub]
  by_cases hx : x < ν n ∧ ν n ≤ x + h
  · have hi : -h ≤ x - ν n ∧ x - ν n < 0 := by constructor <;> linarith [hx.1, hx.2]
    simp only [Set.indicator, Set.mem_Ico, ite_eq_left hi, ite_eq_left hx, mul_one]
  · have hi : ¬ (-h ≤ x - ν n ∧ x - ν n < 0) := by
      intro hi
      exact hx ⟨by linarith [hi.2], by linarith [hi.1]⟩
    simp only [Set.indicator, Set.mem_Ico, ite_eq_right hi, ite_eq_right hx, mul_zero]

/-- Gallagher's finite real frequency lemma with the explicit constant at theta equal to one half. -/
theorem real_frequency_gallagher {ι : Type*} (s : Finset ι) (ν : ι → ℝ) (a : ι → ℂ)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ s, a n *
      Complex.exp ((2 * Real.pi * t * Complex.I) * ν n)‖ ^ 2) ≤
      Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ,
        ‖∑ n ∈ s.filter (fun n => x < ν n ∧ ν n ≤ x + 1 / (2 * T)), a n‖ ^ 2 := by
  let f := WindowParseval264.window {0} (fun _ => 1) (1 / (2 * T))
  have hb := weighted_gallagher s ν a f (WindowParseval264.window_integrable _ _ _)
    (WindowParseval264.window_memLp _ _ _ _) hT (sq_nonneg _)
    (interval_weight_lower_scaled hT)
  have hp : Real.pi * T ≠ 0 := (mul_pos Real.pi_pos hT).ne'
  have hc : (Real.pi * T) ^ 2 * (1 / (Real.pi * T)) ^ 2 = 1 := by field_simp
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.pi * T))
  rw [← mul_assoc, hc, one_mul] at hh
  have hreflect : (∫ t in (-T)..T, ‖∑ n ∈ s, a n *
      Complex.exp ((2 * Real.pi * t * Complex.I) * ν n)‖ ^ 2) =
      ∫ t in (-T)..T, ‖∑ n ∈ s, a n *
      Complex.exp ((-2 * Real.pi * t * Complex.I) * ν n)‖ ^ 2 := by
    have hneg := intervalIntegral.integral_comp_neg
      (fun t : ℝ => ‖∑ n ∈ s, a n * Complex.exp ((2 * Real.pi * t * Complex.I) * ν n)‖ ^ 2)
      (a := -T) (b := T)
    simpa only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg] using hneg.symm
  rw [hreflect]
  convert hh using 1
  congr 1
  · ring
  · apply integral_congr_ae
    filter_upwards with x
    congr 1
    exact congrArg norm (translated_window_sum s ν a _ x).symm

end LeanLab.ExceptionalSet.WeightedGallagher264
