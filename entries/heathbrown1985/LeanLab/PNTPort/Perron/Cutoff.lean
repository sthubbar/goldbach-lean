module

public import LeanLab.PNTPort.Perron.Sinc

/-!
LeanLab.PNTPort.Perron.Cutoff

Truncated Perron type cutoff lemma, for separating the condition mn ≤ x in a
Bombieri-Vinogradov argument. AI wrote this file; the mathematics is classical and known:
the Dirichlet integral plus integration by parts on the sinc tail.

The lemma `norm_sinc_tail_le_of_pos` is a copy of `norm_intervalIntegral_sinc_tail_le`
from PrimeNumberTheoremAnd, commit c39a751132c88b6e8080b74c74023fd95b3d8be0, file
PrimeNumberTheoremAnd/LaplaceInversion.lean, Apache-2.0, with the hypothesis `1 ≤ a`
weakened to `0 < a`, which the original proof already allows.
-/

@[expose] public section

namespace LeanLab.PNTPort.Perron

open Real Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- Finite sinc tail bound for any positive left endpoint. -/
theorem norm_sinc_tail_le_of_pos {a b : ℝ} (ha_pos : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Real.sinc x‖ ≤ 3 * a⁻¹ := by
  have hb_pos : 0 < b := ha_pos.trans_le hab
  have hpos_uIcc : ∀ x ∈ Set.Icc a b, 0 < x := by
    intro x hx
    exact ha_pos.trans_le hx.1
  have hboundary : ‖-Real.cos b / b + Real.cos a / a‖ ≤ 2 * a⁻¹ := by
    calc
      ‖-Real.cos b / b + Real.cos a / a‖
          = |(-Real.cos b / b) + (Real.cos a / a)| := by rw [Real.norm_eq_abs]
      _ ≤ |-Real.cos b / b| + |Real.cos a / a| := abs_add_le _ _
      _ ≤ b⁻¹ + a⁻¹ := by
            refine add_le_add ?_ ?_
            · calc
                |-Real.cos b / b| = |Real.cos b| / b := by
                  rw [abs_div, abs_neg, abs_of_pos hb_pos]
                _ ≤ 1 / b := div_le_div_of_nonneg_right (Real.abs_cos_le_one b) hb_pos.le
                _ = b⁻¹ := by rw [one_div]
            · calc
                |Real.cos a / a| = |Real.cos a| / a := by
                  rw [abs_div, abs_of_pos ha_pos]
                _ ≤ 1 / a := div_le_div_of_nonneg_right (Real.abs_cos_le_one a) ha_pos.le
                _ = a⁻¹ := by rw [one_div]
      _ ≤ a⁻¹ + a⁻¹ := by
            exact add_le_add (by
              simpa [one_div] using one_div_le_one_div_of_le ha_pos hab) le_rfl
      _ = 2 * a⁻¹ := by ring
  have hnormInt : IntervalIntegrable (fun x : ℝ => ‖Real.cos x / x ^ 2‖) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((Real.continuous_cos.continuousOn).div (continuousOn_pow 2) fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne').norm
  have hinvInt : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne'
  have hJ : ‖∫ x in a..b, Real.cos x / x ^ 2‖ ≤ a⁻¹ := by
    calc
      ‖∫ x in a..b, Real.cos x / x ^ 2‖
          ≤ ∫ x in a..b, ‖Real.cos x / x ^ 2‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on hab hnormInt hinvInt ?_
            intro x hx
            have hx_pos : 0 < x := hpos_uIcc x hx
            calc
              ‖Real.cos x / x ^ 2‖ = |Real.cos x| / x ^ 2 := by
                rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx_pos 2)]
              _ ≤ 1 / x ^ 2 :=
                div_le_div_of_nonneg_right (Real.abs_cos_le_one x) (sq_nonneg x)
              _ = (x ^ 2)⁻¹ := by rw [one_div]
      _ = a⁻¹ - b⁻¹ := intervalIntegral_inv_sq_of_pos ha_pos hab
      _ ≤ a⁻¹ := sub_le_self _ (inv_nonneg.mpr hb_pos.le)
  rw [intervalIntegral_sinc_tail_eq_ibp ha_pos hab]
  calc
    ‖(-Real.cos b / b + Real.cos a / a) - ∫ x in a..b, Real.cos x / x ^ 2‖
        ≤ ‖-Real.cos b / b + Real.cos a / a‖ +
            ‖∫ x in a..b, Real.cos x / x ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 * a⁻¹ + a⁻¹ := add_le_add hboundary hJ
    _ = 3 * a⁻¹ := by ring

/-- The sine integral `Si z = ∫₀ᶻ sinc`. -/
def sineIntegral (z : ℝ) : ℝ := ∫ x in (0 : ℝ)..z, Real.sinc x

theorem abs_sineIntegral_sub_pi_div_two_le {z : ℝ} (hz : 0 < z) :
    |sineIntegral z - π / 2| ≤ 3 / z := by
  have hlim := tendsto_intervalIntegral_real_sinc_atTop
  have h1 : Tendsto (fun b => |sineIntegral b - sineIntegral z|) atTop
      (𝓝 (|π / 2 - sineIntegral z|)) :=
    (hlim.sub_const (sineIntegral z)).abs
  have h2 : ∀ᶠ b in atTop, |sineIntegral b - sineIntegral z| ≤ 3 / z := by
    filter_upwards [eventually_ge_atTop z] with b hb
    have h := norm_sinc_tail_le_of_pos hz hb
    rw [Real.norm_eq_abs] at h
    have heq : sineIntegral b - sineIntegral z = ∫ x in z..b, Real.sinc x := by
      unfold sineIntegral
      exact intervalIntegral.integral_interval_sub_left
        (Real.continuous_sinc.intervalIntegrable _ _)
        (Real.continuous_sinc.intervalIntegrable _ _)
    rw [heq, div_eq_mul_inv]
    exact h
  rw [abs_sub_comm]
  exact le_of_tendsto h1 h2

/-- The symmetric sinc integral `∫_{-z}^{z} sinc`. -/
def symSinc (z : ℝ) : ℝ := ∫ x in (-z)..z, Real.sinc x

theorem symSinc_eq (z : ℝ) : symSinc z = 2 * sineIntegral z := by
  unfold symSinc sineIntegral
  have hi : ∀ a b : ℝ, IntervalIntegrable Real.sinc volume a b := fun a b =>
    Real.continuous_sinc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-z) 0) (hi 0 z)]
  have h : ∫ x in (-z)..0, Real.sinc x = ∫ x in (0 : ℝ)..z, Real.sinc x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := z) Real.sinc
    simp only [Real.sinc_neg, neg_zero] at h
    exact h.symm
  rw [h]
  ring

theorem symSinc_neg (z : ℝ) : symSinc (-z) = -symSinc z := by
  unfold symSinc
  rw [neg_neg, intervalIntegral.integral_symm]

theorem abs_symSinc_sub_le {z m : ℝ} (hm : 0 < m) (hz : m ≤ |z|) :
    |symSinc z - π * (if 0 < z then 1 else -1)| ≤ 6 / m := by
  rcases lt_trichotomy z 0 with h | h | h
  · have hn : ¬ 0 < z := not_lt.2 h.le
    simp only [hn, ↓reduceIte]
    rw [abs_of_neg h] at hz
    have hz' : 0 < -z := neg_pos.2 h
    have hb := abs_sineIntegral_sub_pi_div_two_le hz'
    have e : symSinc z - π * -1 = -(2 * (sineIntegral (-z) - π / 2)) := by
      rw [← neg_neg z, symSinc_neg, symSinc_eq, neg_neg]; ring
    rw [e, abs_neg, abs_mul, abs_two]
    calc 2 * |sineIntegral (-z) - π / 2| ≤ 2 * (3 / -z) := by linarith
      _ = 6 / -z := by ring
      _ ≤ 6 / m := div_le_div_of_nonneg_left (by norm_num) hm hz
  · subst h; simp at hz; linarith
  · simp only [h, ↓reduceIte]
    rw [abs_of_pos h] at hz
    have hb := abs_sineIntegral_sub_pi_div_two_le h
    have e : symSinc z - π * 1 = 2 * (sineIntegral z - π / 2) := by
      rw [symSinc_eq]; ring
    rw [e, abs_mul, abs_two]
    calc 2 * |sineIntegral z - π / 2| ≤ 2 * (3 / z) := by linarith
      _ = 6 / z := by ring
      _ ≤ 6 / m := div_le_div_of_nonneg_left (by norm_num) hm hz

theorem integral_mul_sinc_mul (c T : ℝ) :
    ∫ t in (-T)..T, c * Real.sinc (c * t) = symSinc (c * T) := by
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_left (a := -T) (b := T) Real.sinc c
  rw [smul_eq_mul] at h
  rw [h, symSinc, mul_neg]

theorem mul_sinc_mul_mul (c t : ℝ) : c * Real.sinc (c * t) * t = Real.sin (c * t) := by
  by_cases h : c * t = 0
  · rcases mul_eq_zero.1 h with h | h <;> simp [h]
  · rw [Real.sinc_of_ne_zero h,
      show c * (Real.sin (c * t) / (c * t)) * t = Real.sin (c * t) * ((c * t) / (c * t)) by ring,
      div_self h, mul_one]

/-- Product to sum identity in sinc form; it holds at every `t`, including `t = 0`. -/
theorem cos_mul_sinc_eq (α β t : ℝ) :
    Real.cos (α * t) * (β * Real.sinc (β * t)) =
      1 / 2 * ((β + α) * Real.sinc ((β + α) * t) + (β - α) * Real.sinc ((β - α) * t)) := by
  by_cases ht : t = 0
  · subst ht; simp; ring
  · have e1 := mul_sinc_mul_mul β t
    have e2 := mul_sinc_mul_mul (β + α) t
    have e3 := mul_sinc_mul_mul (β - α) t
    have key : Real.cos (α * t) * (β * Real.sinc (β * t)) * t =
        (1 / 2 * ((β + α) * Real.sinc ((β + α) * t) +
          (β - α) * Real.sinc ((β - α) * t))) * t := by
      calc Real.cos (α * t) * (β * Real.sinc (β * t)) * t
          = Real.cos (α * t) * (β * Real.sinc (β * t) * t) := by ring
        _ = Real.cos (α * t) * Real.sin (β * t) := by rw [e1]
        _ = 1 / 2 * (Real.sin ((β + α) * t) + Real.sin ((β - α) * t)) := by
            rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]; ring
        _ = _ := by rw [← e2, ← e3]; ring
    exact mul_right_cancel₀ ht key

/-- An odd continuous function integrates to zero over a symmetric interval. -/
theorem integral_odd_eq_zero {f : ℝ → ℝ} (hf : ∀ t, f (-t) = -f t) (T : ℝ) :
    ∫ t in (-T)..T, f t = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) f
  simp only [hf, neg_neg, intervalIntegral.integral_neg] at h
  linarith

/-- The real form of the truncated integral. -/
theorem integral_cos_mul_kernel (α β T : ℝ) :
    ∫ t in (-T)..T, Real.cos (α * t) * (β / π * Real.sinc (β * t)) =
      (symSinc ((β + α) * T) + symSinc ((β - α) * T)) / (2 * π) := by
  have hpt : ∀ t, Real.cos (α * t) * (β / π * Real.sinc (β * t)) =
      1 / (2 * π) * ((β + α) * Real.sinc ((β + α) * t) +
        (β - α) * Real.sinc ((β - α) * t)) := by
    intro t
    have h := cos_mul_sinc_eq α β t
    calc Real.cos (α * t) * (β / π * Real.sinc (β * t))
        = (Real.cos (α * t) * (β * Real.sinc (β * t))) / π := by ring
      _ = _ := by rw [h]; ring
  simp_rw [hpt]
  have hc : ∀ c : ℝ, IntervalIntegrable (fun t => c * Real.sinc (c * t)) volume (-T) T :=
    fun c => (by fun_prop : Continuous fun t : ℝ => c * Real.sinc (c * t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hc _) (hc _),
    integral_mul_sinc_mul, integral_mul_sinc_mul]
  ring

/-- The complex truncated integral equals the real one. -/
theorem integral_exp_mul_kernel (α β T : ℝ) (hβ : 0 < β) :
    ∫ t in (-T)..T, Complex.exp (Complex.I * (α * t : ℝ)) *
        ((Real.sin (β * t) / (π * t) : ℝ) : ℂ) =
      (((symSinc ((β + α) * T) + symSinc ((β - α) * T)) / (2 * π) : ℝ) : ℂ) := by
  set K : ℝ → ℝ := fun t => β / π * Real.sinc (β * t) with hK
  have hae : ∀ᵐ t : ℝ ∂volume, t ∈ Set.uIoc (-T) T →
      Complex.exp (Complex.I * (α * t : ℝ)) * ((Real.sin (β * t) / (π * t) : ℝ) : ℂ) =
        ((Real.cos (α * t) * K t : ℝ) : ℂ) + Complex.I * ((Real.sin (α * t) * K t : ℝ) : ℂ) := by
    filter_upwards [show ∀ᵐ v : ℝ ∂volume, v ≠ 0 by simp [ae_iff, measure_singleton]]
      with t ht _
    have hbt : β * t ≠ 0 := mul_ne_zero hβ.ne' ht
    have hK' : Real.sin (β * t) / (π * t) = K t := by
      simp only [hK, Real.sinc_of_ne_zero hbt]
      field_simp
    rw [hK', mul_comm Complex.I, Complex.exp_mul_I]
    push_cast
    ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hcont : Continuous K := by simp only [hK]; fun_prop
  have i1 : IntervalIntegrable (fun t => ((Real.cos (α * t) * K t : ℝ) : ℂ)) volume (-T) T :=
    (by fun_prop : Continuous fun t => ((Real.cos (α * t) * K t : ℝ) : ℂ)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => Complex.I * ((Real.sin (α * t) * K t : ℝ) : ℂ))
      volume (-T) T :=
    (by fun_prop : Continuous fun t =>
      Complex.I * ((Real.sin (α * t) * K t : ℝ) : ℂ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hodd : ∫ t in (-T)..T, Real.sin (α * t) * K t = 0 := by
    apply integral_odd_eq_zero
    intro t
    simp only [hK, mul_neg, Real.sin_neg, Real.sinc_neg]
    ring
  rw [hodd, hK, integral_cos_mul_kernel]
  simp

theorem abs_aux {A B p q m ind : ℝ} (hm : 0 < m) (hA : |A - π * p| ≤ 6 / m)
    (hB : |B - π * q| ≤ 6 / m) (hind : 2 * ind = p + q) :
    |(A + B) / (2 * π) - ind| ≤ (6 / π) / m := by
  have hpi := Real.pi_pos
  have e : (A + B) / (2 * π) - ind = ((A - π * p) + (B - π * q)) / (2 * π) := by
    rw [show ind = (p + q) / 2 by linarith]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), div_le_iff₀ (by positivity)]
  have h := abs_add_le (A - π * p) (B - π * q)
  have e2 : 6 / π / m * (2 * π) = 6 / m + 6 / m := by field_simp; ring
  rw [e2]
  linarith

/-- Truncated Perron cutoff: the truncated integral is the indicator of `|α| < β`
up to an error `C / (T * ||α| - β|)`. -/
theorem perron_cutoff : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ β : ℝ, 0 < β → ∀ α : ℝ,
    |α| ≠ β →
    ‖(∫ t in (-T)..T, Complex.exp (Complex.I * (α * t : ℝ)) *
        ((Real.sin (β * t) / (π * t) : ℝ) : ℂ))
        - (if |α| < β then (1 : ℂ) else 0)‖ ≤ C / (T * |(|α| - β)|) := by
  refine ⟨6 / π, by positivity, ?_⟩
  intro T hT β hβ α hαβ
  have hT0 : 0 < T := by linarith
  rw [integral_exp_mul_kernel α β T hβ]
  have hind : (if |α| < β then (1 : ℂ) else 0) = ((if |α| < β then 1 else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp
  rw [hind, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set m := T * |(|α| - β)| with hm_def
  have hm : 0 < m := mul_pos hT0 (abs_pos.2 (sub_ne_zero.2 hαβ))
  have hz1 : m ≤ |(β + α) * T| := by
    rw [abs_mul, abs_of_pos hT0, hm_def, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hT0.le
    have := abs_abs_sub_abs_le_abs_sub α (-β)
    rw [abs_neg, abs_of_pos hβ, sub_neg_eq_add, add_comm] at this
    exact this
  have hz2 : m ≤ |(β - α) * T| := by
    rw [abs_mul, abs_of_pos hT0, hm_def, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hT0.le
    have := abs_abs_sub_abs_le_abs_sub α β
    rw [abs_of_pos hβ, abs_sub_comm α β] at this
    exact this
  apply abs_aux hm (abs_symSinc_sub_le hm hz1) (abs_symSinc_sub_le hm hz2)
  have s1 : ∀ c : ℝ, (0 < c * T ↔ 0 < c) := fun c => by
    constructor
    · intro h; exact pos_of_mul_pos_left h hT0.le
    · intro h; exact mul_pos h hT0
  simp only [s1]
  by_cases h : |α| < β
  · have h' := abs_lt.1 h
    have a1 : 0 < β + α := by linarith
    have a2 : 0 < β - α := by linarith
    simp only [h, a1, a2, ↓reduceIte]; norm_num
  · have h2 : β < |α| := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hαβ)
    rcases lt_abs.1 h2 with h3 | h3
    · have a1 : 0 < β + α := by linarith
      have a2 : ¬ 0 < β - α := by linarith
      simp only [h, a1, a2, ↓reduceIte]; norm_num
    · have a1 : ¬ 0 < β + α := by linarith
      have a2 : 0 < β - α := by linarith
      simp only [h, a1, a2, ↓reduceIte]; norm_num

/-- Pointwise majorant of the kernel. -/
theorem abs_sin_div_le (β t : ℝ) (hβ : 0 < β) :
    |Real.sin (β * t) / (π * t)| ≤ 2 / π * (β / (1 + β * |t|)) := by
  have hpi := Real.pi_pos
  by_cases ht : t = 0
  · subst ht; simp; positivity
  · have hta : 0 < |t| := abs_pos.2 ht
    have hu : 0 < β * |t| := mul_pos hβ hta
    have hs1 := Real.abs_sin_le_one (β * t)
    have hs2 : |Real.sin (β * t)| ≤ β * |t| := by
      have := Real.abs_sin_le_abs (x := β * t)
      rwa [abs_mul, abs_of_pos hβ] at this
    rw [abs_div, abs_mul, abs_of_pos hpi]
    rw [div_le_iff₀ (by positivity)]
    have e : 2 / π * (β / (1 + β * |t|)) * (π * |t|) = 2 * (β * |t|) / (1 + β * |t|) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hsn := abs_nonneg (Real.sin (β * t))
    rcases le_total (β * |t|) 1 with h | h
    · nlinarith
    · nlinarith

theorem integral_majorant_half (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, 2 / π * (β / (1 + β * |t|)) = 2 / π * Real.log (1 + β * T) := by
  have hcongr : ∫ t in (0 : ℝ)..T, 2 / π * (β / (1 + β * |t|)) =
      ∫ t in (0 : ℝ)..T, 2 / π * (β / (1 + β * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    simp only [abs_of_nonneg ht.1]
  rw [hcongr]
  have hpos : ∀ t ∈ Set.uIcc 0 T, 0 < 1 + β * t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have := mul_nonneg hβ.le ht.1
    linarith
  have hderiv : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (fun y => 2 / π * Real.log (1 + β * y)) (2 / π * (β / (1 + β * t))) t := by
    intro t ht
    have h1 : HasDerivAt (fun y => 1 + β * y) β t := by
      simpa using ((hasDerivAt_id t).const_mul β).const_add 1
    exact (h1.log (hpos t ht).ne').const_mul (2 / π)
  have hint : IntervalIntegrable (fun t => 2 / π * (β / (1 + β * t))) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; exact (hpos t ht).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- L¹ bound for the truncated kernel. -/
theorem integral_abs_sin_div_le : ∀ T : ℝ, 1 ≤ T → ∀ β : ℝ, 0 < β →
    ∫ t in (-T)..T, |Real.sin (β * t) / (π * t)| ≤ 2 * (1 + Real.log (1 + β * T)) := by
  intro T hT β hβ
  have hT0 : 0 ≤ T := by linarith
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun t => 2 / π * (β / (1 + β * |t|)) with hg
  have hgc : Continuous g := by
    simp only [hg]
    apply continuous_const.mul
    apply continuous_const.div (by fun_prop)
    intro t; have := mul_nonneg hβ.le (abs_nonneg t); linarith
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  have hle : ∫ t in (-T)..T, |Real.sin (β * t) / (π * t)| ≤ ∫ t in (-T)..T, g t := by
    refine le_trans (le_abs_self _) ?_
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ (hgi _ _)
    exact Filter.Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_sin_div_le β t hβ
  have hsplit : ∫ t in (-T)..T, g t = 2 * (2 / π * Real.log (1 + β * T)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi (-T) 0) (hgi 0 T)]
    have hneg : ∫ t in (-T)..0, g t = ∫ t in (0 : ℝ)..T, g t := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := T) g
      simp only [hg, abs_neg, neg_zero] at h
      simp only [hg]
      exact h.symm
    rw [hneg, hg, integral_majorant_half β T hβ hT0]
    ring
  have hlog : 0 ≤ Real.log (1 + β * T) := Real.log_nonneg (by nlinarith)
  have h4 : 2 / π * Real.log (1 + β * T) ≤ Real.log (1 + β * T) := by
    have : 2 / π ≤ 1 := by rw [div_le_one hpi]; linarith [Real.two_le_pi]
    nlinarith
  linarith

end

end LeanLab.PNTPort.Perron


