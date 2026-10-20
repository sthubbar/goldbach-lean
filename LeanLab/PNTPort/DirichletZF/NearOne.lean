module

public import LeanLab.PNTPort.DirichletZF.Growth
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `L(s, χ)` and `L'(s, χ)` near `s = 1`: bounds by powers of `log N`

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input. These are the
upper bounds Siegel's theorem needs, Davenport chapter 21.

For a non-principal `χ` mod `N ≥ 8`, `ℓ = log N`, and `1 - 1/ℓ ≤ Re s ≤ 1`:
* `norm_LFunction_le_log`: `‖L(s, χ)‖ ≤ e² ‖s‖ ℓ`;
* `norm_deriv_LFunction_le_log`: `‖L'(s, χ)‖ ≤ e² ℓ + 4e² ‖s‖ ℓ²`.
The proof uses `‖A(t)‖ ≤ min(t, N) ≤ t^θ N^{1-θ}` with `θ = Re s - 1/ℓ` in the integral
representation of Growth.lean, so no splitting of the integral is needed.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Finset Filter Asymptotics MeasureTheory Set
open scoped LSeries.notation

variable {N : ℕ}

lemma norm_A_le_floor (χ : DirichletCharacter ℂ N) {t : ℝ} (ht : 0 ≤ t) : ‖A χ t‖ ≤ t := by
  unfold A
  calc ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ ≤ ∑ k ∈ Icc 1 ⌊t⌋₊, ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) := sum_le_sum fun k _ ↦ DirichletCharacter.norm_le_one χ k
    _ = ⌊t⌋₊ := by simp
    _ ≤ t := Nat.floor_le ht

/-- `‖A(t)‖ ≤ t^θ N^{1-θ}` for `0 ≤ θ ≤ 1`, `t ≥ 1`. -/
lemma norm_A_le_interp [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖A χ t‖ ≤ t ^ θ * (N : ℝ) ^ (1 - θ) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht0 : 0 < t := by linarith
  rcases le_total t N with h | h
  · calc ‖A χ t‖ ≤ t := norm_A_le_floor χ ht0.le
      _ = t ^ θ * t ^ (1 - θ) := by
          rw [← Real.rpow_add ht0]; simp
      _ ≤ t ^ θ * (N : ℝ) ^ (1 - θ) := by
          gcongr
  · calc ‖A χ t‖ ≤ N := norm_A_le hχ t
      _ = (N : ℝ) ^ θ * (N : ℝ) ^ (1 - θ) := by
          rw [← Real.rpow_add (by linarith)]; simp
      _ ≤ t ^ θ * (N : ℝ) ^ (1 - θ) := by
          gcongr

lemma one_le_log_half {N : ℕ} (hN : 8 ≤ N) : 2 ≤ Real.log N := by
  rw [Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < N by omega))]
  have h8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  nlinarith

/-- `∫_1^∞ ‖A(t) t^{-s-1}‖ ≤ e² log N` near `1`. -/
lemma integral_bound [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hN : 8 ≤ N)
    {s : ℂ} (hσ : 1 - 1 / Real.log N ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      Real.exp 1 * Real.exp 1 * Real.log N := by
  set ℓ := Real.log N with hℓ
  have hl2 : 2 ≤ ℓ := one_le_log_half hN
  have hl : 0 < ℓ := by linarith
  set θ := s.re - 1 / ℓ with hθ
  have hinv : 1 / ℓ ≤ 1 / 2 := by rw [div_le_div_iff₀ hl (by norm_num)]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith [one_div_pos.mpr hl]
  set K := (N : ℝ) ^ (1 - θ) with hK
  have hint : IntegrableOn (fun t : ℝ ↦ K * t ^ (θ - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by rw [hθ]; linarith [one_div_pos.mpr hl]) zero_lt_one).const_mul _
  have hle : ‖∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Ioi (1 : ℝ), K * t ^ (θ - s.re - 1) := norm_integral_le_of_norm_le hint (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [this]
    calc ‖A χ t‖ * t ^ (-(s.re + 1)) ≤ (t ^ θ * K) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (norm_A_le_interp hχ hθ0 hθ1 (le_of_lt ht))
            (Real.rpow_nonneg ht0.le _)
      _ = K * t ^ (θ - s.re - 1) := by
          rw [mul_comm (t ^ θ) K, mul_assoc, ← Real.rpow_add ht0]; ring_nf)
  have hval : ∫ t in Ioi (1 : ℝ), K * t ^ (θ - s.re - 1) = K * ℓ := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by rw [hθ]; linarith [one_div_pos.mpr hl])
      zero_lt_one, Real.one_rpow]
    congr 1
    rw [show θ - s.re - 1 + 1 = -(1 / ℓ) by rw [hθ]; ring]
    field_simp
  have hKe : K ≤ Real.exp 1 * Real.exp 1 := by
    rw [hK, hθ]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : ℓ * (1 - (s.re - 1 / ℓ)) = ℓ * (1 - s.re) + 1 := by field_simp; ring
    rw [← hℓ, this]
    have h := mul_le_mul_of_nonneg_left (show 1 - s.re ≤ 1 / ℓ by linarith) hl.le
    rw [mul_one_div_cancel hl.ne'] at h
    linarith
  rw [hval] at hle
  calc _ ≤ K * ℓ := hle
    _ ≤ Real.exp 1 * Real.exp 1 * ℓ := mul_le_mul_of_nonneg_right hKe hl.le

/-- The value bound near `1`: `‖L(s, χ)‖ ≤ e² ‖s‖ log N`. -/
theorem norm_LFunction_le_log [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hN : 8 ≤ N) {s : ℂ} (hσ : 1 - 1 / Real.log N ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ Real.exp 1 * Real.exp 1 * ‖s‖ * Real.log N := by
  have hl2 : 2 ≤ Real.log N := one_le_log_half hN
  have hpos : 0 < s.re := by
    have : 1 / Real.log N ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  rw [LFunction_eq_integral hχ hpos, norm_mul]
  have := integral_bound hχ hN hσ hσ1
  calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (Real.exp 1 * Real.exp 1 * Real.log N) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

lemma hasDerivAt_mellin_g [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (mellin (g χ)) (mellin (fun t ↦ Real.log t • g χ t) (-s)) (-s) := by
  have hmeas : Measurable (g χ) := (measurable_A χ).indicator measurableSet_Ioi
  have hbdd : ∀ t, ‖g χ t‖ ≤ N := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem ht]; exact norm_A_le hχ t
    · simp [g, indicator_of_notMem ht]
  refine (mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_).2
  · intro x hx
    refine ⟨Ioi 0 ∩ Iio (x + 1), inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith)), ?_⟩
    refine Measure.integrableOn_of_bounded (M := N) ?_ hmeas.aestronglyMeasurable
      (Eventually.of_forall hbdd)
    rw [Ioi_inter_Iio, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine IsBigO.of_bound N (Eventually.of_forall fun t ↦ ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]; exact hbdd t
  · simpa using hs
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have : t ∉ Ioi (1 : ℝ) := fun h ↦ by
      rw [Set.mem_Ioi] at h; linarith [ht.2]
    simp only [g, indicator_of_notMem this]
  · simp

lemma mellin_log_g_eq (χ : DirichletCharacter ℂ N) (s : ℂ) :
    mellin (fun t ↦ Real.log t • g χ t) (-s) =
      ∫ t in Ioi (1 : ℝ), (Real.log t : ℂ) * A χ t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  have : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Real.log t • g χ t) =
      (Ioi (1 : ℝ)).indicator (fun t ↦ (Real.log t : ℂ) * A χ t * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem ht, smul_eq_mul, Complex.real_smul]
      rw [show -s - 1 = -(s + 1) by ring]; ring
    · simp [g, indicator_of_notMem ht]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi]
  simp

/-- `∫_1^∞ ‖log t · A(t) t^{-s-1}‖ ≤ 4e² log² N` near `1`. -/
lemma integral_log_bound [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hN : 8 ≤ N)
    {s : ℂ} (hσ : 1 - 1 / Real.log N ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖∫ t in Ioi (1 : ℝ), (Real.log t : ℂ) * A χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      4 * (Real.exp 1 * Real.exp 1) * Real.log N ^ 2 := by
  set ℓ := Real.log N with hℓ
  have hl2 : 2 ≤ ℓ := one_le_log_half hN
  have hl : 0 < ℓ := by linarith
  set θ := s.re - 1 / ℓ with hθ
  have hinv : 1 / ℓ ≤ 1 / 2 := by rw [div_le_div_iff₀ hl (by norm_num)]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith [one_div_pos.mpr hl]
  set v := 1 / (2 * ℓ) with hv
  have hvpos : 0 < v := by positivity
  set K := (N : ℝ) ^ (1 - θ) with hK
  have hexp : θ + v - s.re - 1 < -1 := by
    rw [hθ, hv]
    have : 1 / (2 * ℓ) < 1 / ℓ := by
      rw [div_lt_div_iff₀ (by positivity) hl]; linarith
    linarith
  have hint : IntegrableOn (fun t : ℝ ↦ K / v * t ^ (θ + v - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul _
  have hle : ‖∫ t in Ioi (1 : ℝ), (Real.log t : ℂ) * A χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Ioi (1 : ℝ), K / v * t ^ (θ + v - s.re - 1) :=
    norm_integral_le_of_norm_le hint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (le_of_lt ht)
      have hlogle : Real.log t ≤ t ^ v / v := by
        rw [le_div_iff₀ hvpos, mul_comm, ← Real.log_rpow ht0]
        have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 v)
        linarith
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog0]
      have : (-(s + 1)).re = -(s.re + 1) := by simp
      rw [this]
      have hA := norm_A_le_interp hχ hθ0 hθ1 (le_of_lt ht)
      have hr : 0 ≤ t ^ (-(s.re + 1)) := Real.rpow_nonneg ht0.le _
      calc Real.log t * ‖A χ t‖ * t ^ (-(s.re + 1))
          ≤ (t ^ v / v) * (t ^ θ * K) * t ^ (-(s.re + 1)) := by
            gcongr
      _ = K / v * t ^ (θ + v - s.re - 1) := by
            rw [show θ + v - s.re - 1 = v + θ + (-(s.re + 1)) by ring,
              Real.rpow_add ht0, Real.rpow_add ht0]
            ring)
  have hval : ∫ t in Ioi (1 : ℝ), K / v * t ^ (θ + v - s.re - 1) = K * (4 * ℓ ^ 2) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
    rw [show θ + v - s.re - 1 + 1 = -(1 / (2 * ℓ)) by rw [hθ, hv]; ring, hv]
    field_simp
    ring
  have hKe : K ≤ Real.exp 1 * Real.exp 1 := by
    rw [hK, hθ]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : ℓ * (1 - (s.re - 1 / ℓ)) = ℓ * (1 - s.re) + 1 := by field_simp; ring
    rw [← hℓ, this]
    have h := mul_le_mul_of_nonneg_left (show 1 - s.re ≤ 1 / ℓ by linarith) hl.le
    rw [mul_one_div_cancel hl.ne'] at h
    linarith
  rw [hval] at hle
  calc _ ≤ K * (4 * ℓ ^ 2) := hle
    _ ≤ (Real.exp 1 * Real.exp 1) * (4 * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_right hKe (by positivity)
    _ = _ := by ring

/-- The derivative bound near `1`: `‖L'(s, χ)‖ ≤ e² log N + 4e² ‖s‖ log² N`. -/
theorem norm_deriv_LFunction_le_log [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hN : 8 ≤ N) {s : ℂ} (hσ : 1 - 1 / Real.log N ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤
      Real.exp 1 * Real.exp 1 * Real.log N +
        4 * (Real.exp 1 * Real.exp 1) * ‖s‖ * Real.log N ^ 2 := by
  have hl2 : 2 ≤ Real.log N := one_le_log_half hN
  have hpos : 0 < s.re := by
    have : 1 / Real.log N ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  set U : Set ℂ := {z | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds s] fun z ↦ z * mellin (g χ) (-z) := by
    filter_upwards [hUo.mem_nhds hpos] with z hz
    rw [LFunction_eq_integral hχ hz, integral_eq_mellin]
  have hM := hasDerivAt_mellin_g hχ hpos
  have hD : HasDerivAt (fun z ↦ z * mellin (g χ) (-z))
      (1 * mellin (g χ) (-s) + s * (mellin (fun t ↦ Real.log t • g χ t) (-s) * -1)) s :=
    (hasDerivAt_id s).mul (hM.comp s (hasDerivAt_neg s))
  rw [hev.deriv_eq, hD.deriv, ← integral_eq_mellin, mellin_log_g_eq]
  have h1 := integral_bound hχ hN hσ hσ1
  have h2 := integral_log_bound hχ hN hσ hσ1
  calc _ ≤ ‖1 * ∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1))‖ +
        ‖s * ((∫ t in Ioi (1 : ℝ), (Real.log t : ℂ) * A χ t * (t : ℂ) ^ (-(s + 1))) * -1)‖ :=
        norm_add_le _ _
    _ ≤ Real.exp 1 * Real.exp 1 * Real.log N +
        ‖s‖ * (4 * (Real.exp 1 * Real.exp 1) * Real.log N ^ 2) := by
        rw [one_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one]
        gcongr
    _ = _ := by ring

/-- A real zero `β ≥ 1 - 1/log N` of `L(s, χ)` satisfies
`‖L(1, χ)‖ ≤ 5e² (1 - β) log² N`. -/
theorem norm_LFunction_one_le_of_zero [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hN : 8 ≤ N) {β : ℝ} (hβ : 1 - 1 / Real.log N ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ β = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      5 * (Real.exp 1 * Real.exp 1) * Real.log N ^ 2 * (1 - β) := by
  have hl2 : 2 ≤ Real.log N := one_le_log_half hN
  have hL := DirichletCharacter.differentiable_LFunction hχ
  set C := 5 * (Real.exp 1 * Real.exp 1) * Real.log N ^ 2
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (a := β) (b := 1) (C := C)
    (f := fun x : ℝ ↦ DirichletCharacter.LFunction χ x)
    (f' := fun x : ℝ ↦ deriv (DirichletCharacter.LFunction χ) x)
    (fun x _ ↦ ((hL x).hasDerivAt.comp_ofReal).hasDerivWithinAt) (fun x hx ↦ ?_) 1
    ⟨hβ1, le_rfl⟩
  · simp only [Complex.ofReal_one, hz, sub_zero] at hmv
    exact hmv
  · have hx1 : 1 - 1 / Real.log N ≤ (x : ℂ).re := by
      rw [Complex.ofReal_re]; linarith [hx.1]
    have hx2 : (x : ℂ).re ≤ 1 := by simp; linarith [hx.2]
    have hb := norm_deriv_LFunction_le_log hχ hN hx1 hx2
    have hxn : ‖(x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      have : 1 / Real.log N ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      constructor <;> linarith [hx.1, hx.2]
    have he : 0 ≤ Real.exp 1 * Real.exp 1 := by positivity
    have hlsq : Real.log N ≤ Real.log N ^ 2 := by nlinarith
    calc ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖
        ≤ Real.exp 1 * Real.exp 1 * Real.log N +
          4 * (Real.exp 1 * Real.exp 1) * ‖(x : ℂ)‖ * Real.log N ^ 2 := hb
      _ ≤ Real.exp 1 * Real.exp 1 * Real.log N ^ 2 +
          4 * (Real.exp 1 * Real.exp 1) * 1 * Real.log N ^ 2 := by gcongr
      _ = C := by ring

end LeanLab.PNTPort.DirichletZF

