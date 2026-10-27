module

public import LeanLab.PNTPort.StrongPNT.MellinCalculus

/-!
AI-written Lean code, Claude, 2026-10-23, CLOUD run 20261023T1343Z-19109, unit U-1503, paper P0004.

# A Mellin bound without the factor `1/ε`, and the log integral on a vertical line

Known mathematics, no cited input. It uses the ported `Smooth1` and `MellinOfSmooth1a` of the
StrongPNT port, Apache-2.0, the PrimeNumberTheoremAnd contributors.

* `mellin_nu_bdd`: for `ν` of class `C¹` with support in `[1/2, 2]`, `‖𝓜 ν (w)‖ ≤ C` for
  `0 ≤ Re w ≤ 2`.
* `mellin_smooth1_le_inv`: `‖𝓜 (Smooth1 ν ε) (s)‖ ≤ C / ‖s‖` for `0 < Re s ≤ 2`, uniformly in
  `0 < ε < 1`. The port's `MellinOfSmooth1b` gives `C/(ε ‖s‖²)`; this file trades the decay for
  the absence of `1/ε`, which is what a contour shift to `Re s = Θ + 1/log X` with `ε = X^{Θ-1}`
  needs.
* `inv_norm_line_le`: `‖σ + it‖⁻¹ ≤ 4/(1 + |t|)` for `σ ≥ 1/2`.
* `integral_inv_one_add_abs`: `∫_{-T}^{T} (1 + |t|)⁻¹ dt = 2 log (1 + T)`.
* `norm_integral_line_le`: `‖∫_{-T}^{T} g‖ ≤ 8 A log (1 + T)` when `‖g t‖ ≤ A ‖σ + it‖⁻¹`.
-/

@[expose] public section

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory

local notation (name := mellintransform2) "𝓜" => mellin

namespace LeanLab.HardyLittlewood1923.U1503

/-- `x^a ≤ 2` for `x ∈ [1/2, 2]` and `a ∈ [-1, 1]`. -/
lemma rpow_le_two_of_mem {x a : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) :
    x ^ a ≤ 2 := by
  obtain ⟨h1, h2⟩ := hx
  have hx0 : 0 < x := by linarith
  rcases le_total 1 x with hx1 | hx1
  · calc x ^ a ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 ha2
      _ = x := Real.rpow_one x
      _ ≤ 2 := h2
  · calc x ^ a ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ha1
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 2 := by
          rw [inv_le_comm₀ hx0 (by norm_num)]; linarith

/-- **The Mellin transform of the bump is bounded** on `0 ≤ Re w ≤ 2`. -/
lemma mellin_nu_bdd {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 2 → ‖𝓜 (fun x ↦ (ν x : ℂ)) w‖ ≤ C := by
  let f := fun (x : ℝ) ↦ ‖ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (continuous_norm.comp diffν.continuous).continuousOn
  obtain ⟨a, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  have hfa : 0 ≤ f a := norm_nonneg _
  refine ⟨f a * 2 * (3 / 2) + 1, by positivity, fun w hw0 hw2 => ?_⟩
  have key : ‖𝓜 (fun x ↦ (ν x : ℂ)) w‖ ≤ f a * 2 * (3 / 2) := by
    simp only [mellin, smul_eq_mul]
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖((x : ℂ) ^ (w - 1) * (ν x : ℂ))‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖((x : ℂ) ^ (w - 1) * (ν x : ℂ))‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖((x : ℂ) ^ (w - 1) * (ν x : ℂ))‖‖ := le_abs_self _
      _ ≤ _ := ?_
    · exact norm_integral_le_integral_norm _
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · intro x hx
        simp only [Function.mem_support, ne_eq, norm_eq_zero, mul_eq_zero, not_or] at hx
        apply suppν
        simpa [Function.mem_support] using hx.2
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2)
        (f := fun x ↦ ‖(x : ℂ) ^ (w - 1)‖ * f x) (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul, f] at this ⊢
        rwa [(by norm_num : |(2 : ℝ) - 1 / 2| = 3 / 2),
          intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx
        have f_bound := isMaxOn_iff.mp hmax x hx
        have hx0 : 0 < x := by linarith [(mem_Icc.mp hx).1]
        have pow_bound : ‖(x : ℂ) ^ (w - 1)‖ ≤ 2 := by
          rw [norm_cpow_eq_rpow_re_of_pos hx0]
          simp only [sub_re, one_re]
          exact rpow_le_two_of_mem hx (by linarith) (by linarith)
        have hf0 : 0 ≤ f x := norm_nonneg _
        show ‖‖(x : ℂ) ^ (w - 1)‖ * f x‖ ≤ f a * 2
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hf0)]
        calc ‖(x : ℂ) ^ (w - 1)‖ * f x ≤ 2 * f a := mul_le_mul pow_bound f_bound hf0 (by norm_num)
          _ = f a * 2 := by ring
  linarith

/-- **`‖𝓜 (Smooth1 ν ε) (s)‖ ≤ C / ‖s‖` on `0 < Re s ≤ 2`, uniformly in `0 < ε < 1`.** -/
theorem mellin_smooth1_le_inv {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ s : ℂ, 0 < s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  obtain ⟨C, hC, hb⟩ := mellin_nu_bdd diffν suppν
  refine ⟨C, hC, fun ε εpos ε1 s hs0 hs2 => ?_⟩
  rw [MellinOfSmooth1a diffν suppν εpos hs0, norm_mul, norm_inv]
  have hre : ((ε : ℂ) * s).re = ε * s.re := by simp
  have h1 : 0 ≤ ((ε : ℂ) * s).re := by rw [hre]; positivity
  have h2 : ((ε : ℂ) * s).re ≤ 2 := by rw [hre]; nlinarith
  have := hb _ h1 h2
  calc ‖s‖⁻¹ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ ≤ ‖s‖⁻¹ * C :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * ‖s‖⁻¹ := by ring

/-- `‖σ + it‖⁻¹ ≤ 4/(1 + |t|)` for `σ ≥ 1/2`. -/
lemma inv_norm_line_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖(σ : ℂ) + t * I‖⁻¹ ≤ 4 * (1 + |t|)⁻¹ := by
  have hre : |σ| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I); simpa using this
  have him : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + t * I); simpa using this
  have hσa : |σ| = σ := abs_of_nonneg (by linarith)
  have hlow : (1 + |t|) / 4 ≤ ‖(σ : ℂ) + t * I‖ := by
    rcases le_total |t| 1 with h | h
    · linarith
    · linarith
  have hpos : 0 < (1 + |t|) / 4 := by positivity
  calc ‖(σ : ℂ) + t * I‖⁻¹ ≤ ((1 + |t|) / 4)⁻¹ := inv_anti₀ hpos hlow
    _ = 4 * (1 + |t|)⁻¹ := by field_simp

lemma continuous_inv_one_add_abs : Continuous fun t : ℝ ↦ (1 + |t|)⁻¹ :=
  Continuous.inv₀ (by fun_prop) (fun t ↦ by positivity)

/-- `∫_0^T (1 + |t|)⁻¹ dt = log (1 + T)`. -/
lemma integral_inv_one_add_abs_pos {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = Real.log (1 + T) := by
  have e : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (t + 1)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    simp only
    rw [abs_of_nonneg ht.1, add_comm]
  have h2 : ∫ t in (0 : ℝ)..T, (t + 1)⁻¹ = ∫ t in (0 + 1 : ℝ)..(T + 1), t⁻¹ :=
    intervalIntegral.integral_comp_add_right (fun t : ℝ ↦ t⁻¹) 1
  rw [e, h2, zero_add, integral_inv_of_pos one_pos (by linarith), div_one, add_comm]

/-- `∫_{-T}^{T} (1 + |t|)⁻¹ dt = 2 log (1 + T)`. -/
lemma integral_inv_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (-T)..T, (1 + |t|)⁻¹ = 2 * Real.log (1 + T) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ ↦ (1 + |t|)⁻¹) volume a b :=
    fun a b ↦ continuous_inv_one_add_abs.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) 0) (hi 0 T)]
  have hneg : ∫ t in (-T)..0, (1 + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
      (fun t : ℝ ↦ (1 + |t|)⁻¹)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [hneg, integral_inv_one_add_abs_pos hT]
  ring

/-- **The left edge**: `‖∫_{-T}^{T} g‖ ≤ 8 A log (1 + T)` when `‖g t‖ ≤ A ‖σ + it‖⁻¹`, `σ ≥ 1/2`. -/
theorem norm_integral_line_le {σ T A : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) (hA : 0 ≤ A)
    {g : ℝ → ℂ} (hg : ∀ t : ℝ, |t| ≤ T → ‖g t‖ ≤ A * ‖(σ : ℂ) + t * I‖⁻¹) :
    ‖∫ t in (-T)..T, g t‖ ≤ 8 * A * Real.log (1 + T) := by
  have hb : ∀ᵐ t, t ∈ Ioc (-T) T → ‖g t‖ ≤ 4 * A * (1 + |t|)⁻¹ := by
    refine Eventually.of_forall fun t ht ↦ ?_
    have habs : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    refine (hg t habs).trans ?_
    have := inv_norm_line_le hσ t
    calc A * ‖(σ : ℂ) + t * I‖⁻¹ ≤ A * (4 * (1 + |t|)⁻¹) := mul_le_mul_of_nonneg_left this hA
      _ = 4 * A * (1 + |t|)⁻¹ := by ring
  have hii : IntervalIntegrable (fun t : ℝ ↦ 4 * A * (1 + |t|)⁻¹) volume (-T) T :=
    (continuous_const.mul continuous_inv_one_add_abs).intervalIntegrable _ _
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) hb hii).trans ?_
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs hT]
  exact le_of_eq (by ring)

end LeanLab.HardyLittlewood1923.U1503
