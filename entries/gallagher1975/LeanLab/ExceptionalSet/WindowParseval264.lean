module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Fourier integral and L2 compatibility for Gallagher's finite windows.
Source: Gallagher 1970 Lemma 1 and Montgomery Topics Lemma 1.9.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap Topology ContDiff ENNReal

namespace LeanLab.ExceptionalSet.WindowParseval264

/-- An integrable function has the same Fourier pairing as its L2 class. -/
theorem fourier_pairing (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, g x * 𝓕 f x =
      ∫ x : ℝ, g x * (𝓕 (h₂.toLp f) : Lp ℂ 2) x := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
    (by fun_prop) g.integrable h₁
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    exact flip_innerₗ ℝ
  rw [hflip] at hswap
  have hd := congrArg (fun d : 𝓢'(ℝ, ℂ) => d g)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x : ℝ, (𝓕 g) x * f x := by
      simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
        VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul] using hswap.symm
    _ = ∫ x : ℝ, (𝓕 g) x * (h₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := by simpa only [smul_eq_mul] using hd

/-- The Fourier integral represents the Fourier transform of the L2 class. -/
theorem fourierIntegral_ae_eq (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  simpa using fourier_pairing f h₁ h₂ (hc'.toSchwartzMap hg')

/-- The square of the L2 norm is the integral of the squared pointwise norm. -/
theorem integral_norm_sq_coe (u : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖u x‖ ^ 2 = ‖u‖ ^ 2 := by
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) u u)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    using hi.symm

/-- Plancherel for the Fourier integral on L1 intersect L2. -/
theorem integral_norm_sq_fourier (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    ∫ t : ℝ, ‖𝓕 f t‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourierIntegral_ae_eq f h₁ h₂] with t ht
      rw [ht]
    _ = ‖𝓕 (h₂.toLp f)‖ ^ 2 := integral_norm_sq_coe _
    _ = ‖h₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      rw [← integral_norm_sq_coe]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

/-- The finite moving window with its left endpoint included. -/
noncomputable def window (s : Finset ℤ) (a : ℤ → ℂ) (h x : ℝ) : ℂ :=
  ∑ n ∈ s, (Set.Ico ((n : ℝ) - h) n).indicator (fun _ => a n) x

/-- Bounded interval windows belong to every Lp space. -/
theorem window_memLp (s : Finset ℤ) (a : ℤ → ℂ) (h : ℝ) (p : ℝ≥0∞) :
    MemLp (window s a h) p := by
  apply memLp_finsetSum
  intro n hn
  exact memLp_indicator_const p measurableSet_Ico (a n)
    (Or.inr (by simp))

/-- The finite moving window is integrable. -/
theorem window_integrable (s : Finset ℤ) (a : ℤ → ℂ) (h : ℝ) :
    Integrable (window s a h) := by
  exact memLp_one_iff_integrable.mp (window_memLp s a h 1)

/-- The interval indicator window equals the filtered coefficient sum. -/
theorem window_eq_sum_filter (s : Finset ℤ) (a : ℤ → ℂ) (h x : ℝ) :
    window s a h x = ∑ n ∈ s.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n := by
  classical
  rw [window, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hx : (n : ℝ) - h ≤ x ∧ x < n
  · have hx' : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h := by constructor <;> linarith [hx.1, hx.2]
    simp only [Set.indicator, Set.mem_Ico, if_pos hx, if_pos hx']
  · have hx' : ¬ (x < (n : ℝ) ∧ (n : ℝ) ≤ x + h) := by
      intro hh
      exact hx ⟨by linarith [hh.2], hh.1⟩
    simp only [Set.indicator, Set.mem_Ico, if_neg hx, if_neg hx']

/-- Parseval for the finite moving interval window. -/
theorem window_parseval (s : Finset ℤ) (a : ℤ → ℂ) (h : ℝ) :
    ∫ t : ℝ, ‖𝓕 (window s a h) t‖ ^ 2 = ∫ x : ℝ, ‖window s a h x‖ ^ 2 :=
  integral_norm_sq_fourier _ (window_integrable s a h) (window_memLp s a h 2)

/-- The Fourier integral of an interval indicator is an interval integral. -/
theorem fourier_interval (b c : ℝ) (hbc : b ≤ c) (z : ℂ) (t : ℝ) :
    𝓕 ((Set.Ico b c).indicator (fun _ : ℝ => z)) t =
      (∫ x in b..c, Complex.exp ((-2 * Real.pi * t * Complex.I) * x)) * z := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) =
      Complex.exp ((-2 * Real.pi * t * Complex.I) * x) := by
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hind : (fun x : ℝ => Complex.exp ((-2 * Real.pi * t * Complex.I) * x) *
      (Set.Ico b c).indicator (fun _ => z) x) =
      (Set.Ico b c).indicator (fun x => Complex.exp ((-2 * Real.pi * t * Complex.I) * x) * z) := by
    funext x
    by_cases hx : x ∈ Set.Ico b c <;> simp [Set.indicator, hx]
  rw [hind]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbc, intervalIntegral.integral_mul_const]

/-- The finite window Fourier integral factors as an exponential sum and a common kernel. -/
theorem fourier_window (s : Finset ℤ) (a : ℤ → ℂ) {h : ℝ} (hh : 0 ≤ h)
    {t : ℝ} (ht : t ≠ 0) :
    𝓕 (window s a h) t =
      ((1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
        (-2 * Real.pi * t * Complex.I)) *
      ∑ n ∈ s, a n * Complex.exp ((-2 * Real.pi * t * Complex.I) * (n : ℝ)) := by
  let c : ℂ := -2 * Real.pi * t * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast ht)) Complex.I_ne_zero
  have hi (n : ℤ) : Integrable ((Set.Ico ((n : ℝ) - h) n).indicator (fun _ => a n)) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_Ico
      (a n) (Or.inr (by simp)))
  have hsum : 𝓕 (window s a h) t =
      ∑ n ∈ s, 𝓕 ((Set.Ico ((n : ℝ) - h) n).indicator (fun _ => a n)) t := by
    rw [Real.fourier_eq]
    simp only [window, Finset.smul_sum]
    rw [integral_finsetSum]
    · rfl
    · intro n hn
      exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ ℝ) (by fun_prop) t).2 (hi n)
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fourier_interval _ _ (by linarith) (a n) t]
  change (∫ x in (n : ℝ) - h..n, Complex.exp (c * x)) * a n = _
  rw [integral_exp_mul_complex hc]
  have he : Complex.exp (c * ((n : ℝ) - h)) =
      Complex.exp (c * (n : ℝ)) * Complex.exp (-c * h) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he' : -c * h = ((2 * Real.pi * t * h : ℝ) : ℂ) * Complex.I := by
    dsimp [c]
    push_cast
    ring
  rw [Complex.ofReal_sub, he, he']
  dsimp [c]
  ring

/-- The absolute size of the common interval Fourier kernel. -/
theorem kernel_norm (h t : ℝ) :
    ‖(1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
      (-2 * Real.pi * t * Complex.I)‖ =
      |Real.sin (Real.pi * t * h)| / (Real.pi * |t|) := by
  rw [norm_div, norm_sub_rev]
  have he : ((2 * Real.pi * t * h : ℝ) : ℂ) * Complex.I =
      Complex.I * ((2 * Real.pi * t * h : ℝ) : ℂ) := mul_comm _ _
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have ha : 2 * Real.pi * t * h / 2 = Real.pi * t * h := by ring
  rw [ha]
  simp only [Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
  norm_num
  ring

/-- Jordan's sine bound gives the required lower bound for the window kernel. -/
theorem kernel_lower {T t : ℝ} (hT : 0 < T) (ht : t ≠ 0) (hbound : |t| ≤ T) :
    1 / (Real.pi * T) ≤
      ‖(1 - Complex.exp ((2 * Real.pi * t * (1 / (2 * T)) : ℝ) * Complex.I)) /
        (-2 * Real.pi * t * Complex.I)‖ := by
  rw [kernel_norm]
  have hp : 0 < Real.pi := Real.pi_pos
  have hta : 0 < |t| := abs_pos.mpr ht
  have harg : |Real.pi * t * (1 / (2 * T))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
    calc Real.pi * |t| * (1 / (2 * T)) ≤ Real.pi * T * (1 / (2 * T)) := by gcongr
         _ = Real.pi / 2 := by field_simp
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_mul, abs_of_pos hp,
    abs_of_pos (by positivity : 0 < 1 / (2 * T))] at hs
  apply (le_div_iff₀ (mul_pos hp hta)).mpr
  calc (1 / (Real.pi * T)) * (Real.pi * |t|) =
      2 / Real.pi * (Real.pi * |t| * (1 / (2 * T))) := by field_simp
       _ ≤ _ := hs

/-- The Fourier integral of an L1 intersect L2 function belongs to L2. -/
theorem fourierIntegral_memLp (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourierIntegral_ae_eq f h₁ h₂)).mpr (Lp.memLp _)

/-- Gallagher's bound for the finite exponential sum with negative Fourier sign. -/
theorem window_bound (s : Finset ℤ) (a : ℤ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ‖∑ n ∈ s, a n *
      Complex.exp ((-2 * Real.pi * t * Complex.I) * (n : ℝ))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ, ‖window s a (1 / (2 * T)) x‖ ^ 2 := by
  let C := window s a (1 / (2 * T))
  let P : ℝ → ℂ := fun t => ∑ n ∈ s, a n *
    Complex.exp ((-2 * Real.pi * t * Complex.I) * (n : ℝ))
  have hC₁ : Integrable C := window_integrable _ _ _
  have hC₂ : MemLp C 2 := window_memLp _ _ _ _
  have hF := fourierIntegral_memLp C hC₁ hC₂
  have hFs : Integrable (fun t => ‖𝓕 C t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hFc : Continuous (𝓕 C) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hC₁
  have hpoint : ∀ᵐ t : ℝ, t ∈ Set.Icc (-T) T →
      ‖P t‖ ^ 2 ≤ Real.pi ^ 2 * T ^ 2 * ‖𝓕 C t‖ ^ 2 := by
    filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 from by
      rw [ae_iff]
      simp] with t ht htI
    have hb : |t| ≤ T := abs_le.mpr ⟨htI.1, htI.2⟩
    have hk := kernel_lower hT ht hb
    have hw := fourier_window s a (by positivity : 0 ≤ 1 / (2 * T)) ht
    change 𝓕 C t = _ at hw
    have hnorm := congrArg norm hw
    rw [norm_mul] at hnorm
    have hq : ‖P t‖ ≤ (Real.pi * T) * ‖𝓕 C t‖ := by
      have hh := mul_le_mul_of_nonneg_right hk (norm_nonneg (P t))
      change 1 / (Real.pi * T) * ‖P t‖ ≤ _ at hh
      rw [← hnorm] at hh
      have hpT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
      have hh' : ‖P t‖ / (Real.pi * T) ≤ ‖𝓕 C t‖ := by
        simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hh
      simpa only [mul_comm] using (div_le_iff₀ hpT).mp hh'
    nlinarith [norm_nonneg (P t), norm_nonneg (𝓕 C t), Real.pi_pos]
  have hi := intervalIntegral.integral_mono_ae_restrict (by linarith : -T ≤ T)
    (hPc.norm.pow 2 |>.intervalIntegrable (-T) T)
    ((hFc.norm.pow 2).const_mul (Real.pi ^ 2 * T ^ 2) |>.intervalIntegrable (-T) T)
    ((ae_restrict_iff' measurableSet_Icc).mpr hpoint)
  change (∫ t in (-T)..T, ‖P t‖ ^ 2) ≤ _
  calc
    _ ≤ ∫ t in (-T)..T, Real.pi ^ 2 * T ^ 2 * ‖𝓕 C t‖ ^ 2 := hi
    _ = Real.pi ^ 2 * T ^ 2 * ∫ t in (-T)..T, ‖𝓕 C t‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ Real.pi ^ 2 * T ^ 2 * ∫ t : ℝ, ‖𝓕 C t‖ ^ 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact integral_mono_measure Measure.restrict_le_self
        (by filter_upwards with t; positivity) hFs
    _ = _ := by rw [integral_norm_sq_fourier C hC₁ hC₂]

end LeanLab.ExceptionalSet.WindowParseval264
