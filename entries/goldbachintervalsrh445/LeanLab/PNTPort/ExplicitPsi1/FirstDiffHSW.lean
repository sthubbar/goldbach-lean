module

public import LeanLab.Dudek2014.SigmaHSW

/-!
# Components of a Schoenfeld-shape RH bound for `ψ`

I-5250, unit U-6656, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics.

Toward `|ψ(x) - x| ≤ √x log² x/(8π)` for large `x` by one unsmoothing of the explicit formula
for `ψ₁`: the first difference of the zero sum needs, per zero,
* `first_diff_small`: `|f(x + h) - f(x)| ≤ h (x + h)^{1/2}/|ρ|`, `f(y) = y^{ρ+1}/(ρ(ρ+1))`;
* `first_diff_large`: `|f(x + h) - f(x)| ≤ 2 (x + h)^{3/2}/|ρ(ρ+1)|`;
and over the zeros
* `head_inv`: `Σ_{14 ≤ |γ| ≤ T} 1/|γ| ≤ log²(T/2π)/(2π) + 1.57` for `T ≥ 14`, by a layer cake on
  the Hasanalizade-Shen-Wong count for `T ≥ 14`, `HSWHead14`.
Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.FirstDiff
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt c_lower c_upper)
open LeanLab.Dudek2014.SigmaT (rhoF fz f1 rhoF_re rhoF_ne hasDerivAt_fz norm_cpow_rhoF
  norm_rho_mul_ge' norm_fz_le log_le_half)
open LeanLab.Dudek2014.SigmaH (Mt_eq)

variable {ι : Type*}

/-! ### One zero -/

lemma norm_rhoF_ge (g : ℝ) : |g| ≤ ‖rhoF g‖ := by
  have := Complex.abs_im_le_norm (rhoF g); simpa [rhoF] using this

lemma norm_rhoF_pos (g : ℝ) : 0 < ‖rhoF g‖ := norm_pos_iff.mpr (rhoF_ne g)

/-- `|f(x + h) - f(x)| ≤ h (x + h)^{1/2}/|ρ|`. -/
lemma first_diff_small (g : ℝ) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖fz (rhoF g) (x + h) - fz (rhoF g) x‖ ≤ h * ((x + h) ^ (1 / 2 : ℝ) / ‖rhoF g‖) := by
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' (f := fz (rhoF g))
    (a := x) (b := x + h) (C := (x + h) ^ (1 / 2 : ℝ) / ‖rhoF g‖)
    (fun v hv => (hasDerivAt_fz g (by linarith [hv.1])).hasDerivWithinAt)
    (fun v hv => by
      have hv0 : 0 < v := by linarith [hv.1]
      unfold f1
      rw [norm_div]
      apply div_le_div_of_nonneg_right _ (norm_rhoF_pos g).le
      have e : (v : ℂ) ^ rhoF g = (v : ℂ) ^ (rhoF g + (0 : ℂ)) := by rw [add_zero]
      rw [e, norm_cpow_rhoF hv0]
      simp only [Complex.zero_re, add_zero]
      exact Real.rpow_le_rpow hv0.le hv.2.le (by norm_num))
    (x + h) ⟨by linarith, le_rfl⟩
  calc _ ≤ (x + h) ^ (1 / 2 : ℝ) / ‖rhoF g‖ * (x + h - x) := hm
    _ = _ := by ring

/-- `|f(x + h) - f(x)| ≤ 2 (x + h)^{3/2}/|ρ(ρ+1)|`. -/
lemma first_diff_large (g : ℝ) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖fz (rhoF g) (x + h) - fz (rhoF g) x‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) / ‖rhoF g * (rhoF g + 1)‖ := by
  have hn : 0 < ‖rhoF g * (rhoF g + 1)‖ := lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' g)
  have a := norm_fz_le g (by linarith : 0 < x + h) le_rfl
  have b := norm_fz_le g hx (by linarith : x ≤ x + h)
  rw [le_div_iff₀ hn]
  calc ‖fz (rhoF g) (x + h) - fz (rhoF g) x‖ * ‖rhoF g * (rhoF g + 1)‖
      ≤ (‖fz (rhoF g) (x + h)‖ + ‖fz (rhoF g) x‖) * ‖rhoF g * (rhoF g + 1)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) := by nlinarith

/-! ### The head sum `Σ 1/|γ|` -/

/-- Cited, the head clause of Hasanalizade-Shen-Wong Corollary 1.2 for `T ≥ 14`, `7/8` in the
error as in `SigmaH.HSWN70`, as counts over any finite set of the ordinates, both signs. -/
def HSWHead14 (γ : ι → ℝ) : Prop :=
  ∀ T : ℝ, 14 ≤ T → ∀ s : Finset ι, ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)

/-- The count majorant `m(t) = t (log t - log 2π - 1)/π + 22.25 + 0.502 log t`. -/
noncomputable def mF (t : ℝ) : ℝ := t * (log t - log (2 * π) - 1) / π + 22.25 + 0.502 * log t

/-- Its antiderivative against `1/t²`. -/
noncomputable def FF (t : ℝ) : ℝ :=
  (log t - log (2 * π) - 1) ^ 2 / (2 * π) - 22.25 / t - 0.502 * (log t + 1) / t

lemma log_ge_14 {t : ℝ} (ht : 14 ≤ t) : 2.6 ≤ log t := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have e : exp 2.6 = exp 1 ^ 2 * exp 0.6 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 : exp 0.6 ≤ 1.8222 := by
    have := Real.exp_bound' (x := 0.6) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [e]
  have : exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.6]

/-- `2(M(t) + R(t)) ≤ m(t)` for `t ≥ 14`. -/
lemma count_major {t : ℝ} (ht : 14 ≤ t) : 2 * (Mt t + Rt t) ≤ mF t := by
  have ht0 : 0 < t := by linarith
  have hl := log_ge_14 ht
  have hll := log_le_half (by linarith : (0 : ℝ) < log t)
  rw [Mt_eq ht0]
  unfold mF Rt
  have e : 2 * (t * (log t - log (2 * π) - 1) / (2 * π) + 7 / 8) =
      t * (log t - log (2 * π) - 1) / π + 7 / 4 := by field_simp; ring
  nlinarith

lemma hasDerivAt_FF {t : ℝ} (ht : 0 < t) : HasDerivAt FF (mF t / t ^ 2) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have h1 := (((hl.sub_const (log (2 * π))).sub_const 1).pow 2).div_const (2 * π)
  have h2 := (hasDerivAt_id t).inv ht.ne' |>.const_mul 22.25
  have h3 := ((hl.add_const 1).const_mul 0.502).div (hasDerivAt_id t) ht.ne'
  have h := (h1.sub h2).sub h3
  convert h using 1
  · funext y; simp [FF, div_eq_mul_inv]
  · unfold mF; simp only [id, Nat.cast_ofNat]; field_simp; ring

lemma continuousOn_mF_div : ContinuousOn (fun t => mF t / t ^ 2) (Ici 1) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  apply ContinuousAt.continuousWithinAt
  unfold mF
  have hlog : ContinuousAt log t := Real.continuousAt_log ht0.ne'
  apply ContinuousAt.div _ (continuousAt_id.pow 2) (pow_ne_zero 2 ht0.ne')
  fun_prop (disch := exact ht0.ne')

lemma one_div_sq_int {g T : ℝ} (hg : 0 < g) (hgT : g ≤ T) :
    ∫ t in Ioc g T, 1 / t ^ 2 = 1 / g - 1 / T := by
  rw [← intervalIntegral.integral_of_le hgT]
  have hd : ∀ t ∈ uIcc g T, HasDerivAt (fun y => -(1 / y)) (1 / t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hgT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hg ht.1
    have := ((hasDerivAt_id t).inv ht0.ne').neg
    convert this using 1
    · funext y; simp [one_div]
    · simp [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hgT]
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hg ht.1
    exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht0.ne')).continuousWithinAt

/-- **`Σ_{14 ≤ |γ| ≤ T} 1/|γ| ≤ log²(T/2π)/(2π) + 1.57`** for `T ≥ 14`, from `HSWHead14`. -/
lemma head_inv {γ : ι → ℝ} (hN : HSWHead14 γ) (h14 : ∀ i, 14 ≤ |γ i|) {T : ℝ} (hT : 14 ≤ T)
    (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => |γ i| ≤ T), 1 / |γ i| ≤ (log T - log (2 * π)) ^ 2 / (2 * π) + 1.57 := by
  have hT0 : 0 < T := by linarith
  set S := s.filter (fun i => |γ i| ≤ T)
  have hterm : ∀ i ∈ S, 1 / |γ i| =
      1 / T + ∫ t in Ioc 14 T, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, max_eq_right (h14 i),
      one_div_sq_int (by linarith [h14 i]) hi.2]
    ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Icc 14 T) := fun t ht =>
    (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (by linarith [ht.1] : (0 : ℝ) < t).ne')).continuousWithinAt
  have hint : ∀ i ∈ S, Integrable (fun t => (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t)
      (volume.restrict (Ioc 14 T)) :=
    fun i _ => ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ioi
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← integral_finsetSum S hint,
    Finset.sum_const, nsmul_eq_mul]
  have hmaj : IntegrableOn (fun t => mF t / t ^ 2) (Ioc 14 T) :=
    ((continuousOn_mF_div.mono (fun t ht => by simp only [mem_Ici]; linarith [ht.1])).integrableOn_Icc
      ).mono_set Ioc_subset_Icc_self
  have hI : ∫ t in Ioc 14 T, mF t / t ^ 2 = FF T - FF 14 := by
    rw [← intervalIntegral.integral_of_le hT]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht; rw [uIcc_of_le hT] at ht; exact hasDerivAt_FF (by linarith [ht.1])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT]
      exact continuousOn_mF_div.mono (fun t ht => by simp only [mem_Ici]; linarith [ht.1])
  have hle : ∫ t in Ioc 14 T, ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t ≤
      ∫ t in Ioc 14 T, mF t / t ^ 2 := by
    refine setIntegral_mono_on (integrable_finsetSum S hint) hmaj measurableSet_Ioc
      fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have e : ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t =
        ((S.filter (fun i => |γ i| < t)).card : ℝ) * (1 / t ^ 2) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : |γ i| < t
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    rw [e, ← mul_one_div (mF t)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hsub : S.filter (fun i => |γ i| < t) ⊆ s.filter (fun i => |γ i| ≤ t) := by
      intro i hi
      simp only [S, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.2.le⟩
    have hc1 : ((S.filter (fun i => |γ i| < t)).card : ℝ) ≤ ((s.filter (fun i => |γ i| ≤ t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc1.trans ((hN t ht.1.le s).trans (count_major ht.1.le))
  have hcard : (S.card : ℝ) * (1 / T) ≤ mF T * (1 / T) :=
    mul_le_mul_of_nonneg_right ((hN T hT s).trans (count_major hT)) (by positivity)
  have hfin : mF T * (1 / T) + (FF T - FF 14) ≤ (log T - log (2 * π)) ^ 2 / (2 * π) + 1.57 := by
    have hl := log_ge_14 hT
    have hc := c_lower
    have hc' := c_upper
    have hπ := Real.pi_gt_three
    have hπ' := Real.pi_lt_d2
    have h14l : log 14 ≤ 2.7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.7)
      have e : exp 2.7 = exp 1 ^ 2 * exp 0.7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h1 := Real.exp_one_gt_d9
      have : (2.7182818283 : ℝ) ^ 2 ≤ exp 1 ^ 2 := by gcongr
      nlinarith
    have h14g := log_ge_14 (le_refl 14)
    have e1 : mF T * (1 / T) = (log T - log (2 * π) - 1) / π + (22.25 + 0.502 * log T) / T := by
      unfold mF; field_simp; ring
    have e2 : FF T = (log T - log (2 * π) - 1) ^ 2 / (2 * π) - (22.25 + 0.502 * log T + 0.502) / T := by
      unfold FF; field_simp; ring
    have e3 : FF 14 ≥ -(22.25 + 0.502 * log 14 + 0.502) / 14 := by
      unfold FF
      have : 0 ≤ (log 14 - log (2 * π) - 1) ^ 2 / (2 * π) := by positivity
      have e4 : -(22.25 + 0.502 * log 14 + 0.502) / 14 = -(22.25 / 14) - 0.502 * (log 14 + 1) / 14 := by
        ring
      linarith
    have e5 : (log T - log (2 * π) - 1) ^ 2 / (2 * π) + (log T - log (2 * π) - 1) / π =
        (log T - log (2 * π)) ^ 2 / (2 * π) - 1 / (2 * π) := by field_simp; ring
    have e6 : 0.502 / T ≥ 0 := by positivity
    have e7 : 1 / (2 * π) ≥ 0.158 := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith
    have e8 : (22.25 + 0.502 * log 14 + 0.502) / 14 ≤ 1.7222 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [e1, e2]
    have e9 : (22.25 + 0.502 * log T) / T - (22.25 + 0.502 * log T + 0.502) / T = -(0.502 / T) := by
      field_simp; ring
    linarith
  have hsum : (S.card : ℝ) * (1 / T) +
      ∫ t in Ioc 14 T, ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t ≤
      mF T * (1 / T) + (FF T - FF 14) := by rw [← hI]; linarith
  have e0 : (S.card : ℝ) * (1 / T) = ↑S.card * (1 / T) := rfl
  calc _ = (S.card : ℝ) * (1 / T) +
        ∫ t in Ioc 14 T, ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t := by ring
    _ ≤ _ := hsum.trans hfin

/-! ### The first difference of the zero sum -/

/-- The head factor `S₁(T) = log²(T/2π)/(2π) + 1.57`. -/
noncomputable def S1 (T : ℝ) : ℝ := (log T - log (2 * π)) ^ 2 / (2 * π) + 1.57

/-- The tail factor `S₂(T) = log T/(πT) + (1.004 log T + 41.26 - 0.25 T)/T²`. -/
noncomputable def S2 (T : ℝ) : ℝ := log T / (π * T) + (1.004 * log T + 41.26 - 0.25 * T) / T ^ 2

/-- **`|Σ_ρ (f(x + h) - f(x))| ≤ h (x + h)^{1/2} S₁(T) + 2 (x + h)^{3/2} S₂(T)`** for `T ≥ 70`,
for any ordinate family with the Hasanalizade-Shen-Wong counts and every `|γ| ≥ 14`. -/
theorem zdiff_le {γ : ι → ℝ} (hN : LeanLab.Dudek2014.SigmaH.HSWN70 γ) (hH : HSWHead14 γ)
    (h14 : ∀ i, 14 ≤ |γ i|) {x h T : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hT : 70 ≤ T) :
    ‖(∑' i, fz (rhoF (γ i)) (x + h)) - ∑' i, fz (rhoF (γ i)) x‖ ≤
      h * (x + h) ^ (1 / 2 : ℝ) * S1 T + 2 * (x + h) ^ (3 / 2 : ℝ) * S2 T := by
  have hxh : 0 < x + h := by linarith
  set D : ι → ℂ := fun i => fz (rhoF (γ i)) (x + h) - fz (rhoF (γ i)) x
  have sa := LeanLab.Dudek2014.SigmaH.summable_fz hN hxh
  have sb := LeanLab.Dudek2014.SigmaH.summable_fz hN hx
  have eD : (∑' i, fz (rhoF (γ i)) (x + h)) - ∑' i, fz (rhoF (γ i)) x = ∑' i, D i :=
    (sa.tsum_sub sb).symm
  rw [eD]
  set B := 2 * (x + h) ^ (3 / 2 : ℝ)
  have hB : 0 ≤ B := by positivity
  set a := h * (x + h) ^ (1 / 2 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hne : ∀ i, γ i ≠ 0 := fun i h0 => by have := h14 i; rw [h0, abs_zero] at this; linarith
  have hDn : ∀ i, ‖D i‖ ≤ B * LeanLab.Dudek2014.SigmaT.wgt γ i := fun i => by
    have := first_diff_large (γ i) hx hh
    unfold LeanLab.Dudek2014.SigmaT.wgt; rw [mul_one_div]; exact this
  have hsumN : Summable (fun i => ‖D i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hDn
      ((LeanLab.Dudek2014.SigmaH.summable_wgt hN).mul_left B)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖D i‖ ≤ a * S1 T + B * S2 T := by
    intro s
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)]
    have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), ‖D i‖ ≤ a * S1 T := by
      calc _ ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T), a * (1 / |γ i|) := by
            apply Finset.sum_le_sum; intro i _
            have h0 : 0 < |γ i| := abs_pos.mpr (hne i)
            have := first_diff_small (γ i) hx hh
            refine this.trans ?_
            rw [← mul_div_assoc, mul_one_div]
            exact div_le_div_of_nonneg_left ha h0 (norm_rhoF_ge _)
        _ = a * ∑ i ∈ s.filter (fun i => |γ i| ≤ T), 1 / |γ i| := by rw [Finset.mul_sum]
        _ ≤ a * S1 T := by gcongr; exact head_inv hH h14 (by linarith) s
    have h2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), ‖D i‖ ≤ B * S2 T := by
      calc _ ≤ ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), B * (1 / γ i ^ 2) := by
            apply Finset.sum_le_sum; intro i _
            exact (hDn i).trans (mul_le_mul_of_nonneg_left
              (LeanLab.Dudek2014.SigmaT.wgt_le_inv_sq γ (hne i)) hB)
        _ = B * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2 := by rw [Finset.mul_sum]
        _ ≤ B * S2 T := by gcongr; exact LeanLab.Dudek2014.SigmaH.tail_inv_sq hN hT s
    linarith
  calc ‖∑' i, D i‖ ≤ ∑' i, ‖D i‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ a * S1 T + B * S2 T := hsumN.tsum_le_of_sum_le hfin

end LeanLab.PNTPort.ExplicitPsi1.FirstDiff
