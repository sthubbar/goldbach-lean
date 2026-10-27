module

public import Mathlib
public import LeanLab.Dudek2014.Display
public import LeanLab.ChirreHagen2025.Lemma26Proof

/-!
P0100 A. Dudek, On the Riemann hypothesis and the difference between primes, arXiv 1402.6417,
unit U-6503, CLOUD 20261020T1415Z-cloud44, 2026-10-20.
The page 5 zero-sum bound `SigmaBd` of Display.lean, for the second difference of
`Z(y) = Re Σ_ρ y^{ρ+1}/(ρ(ρ+1))` over a family of ordinates with every `ρ = 1/2 + iγ`, PROVED
CONDITIONAL ON `TrudgianN70`: Trudgian's `N(T)` bound, J. Number Theory 134 (2014), in its
`N(T)` form with `0.2/T`, read as counts of the ordinates, both signs, for `T ≥ 70`.
The paper's split at `|γ| = αx/h`, `α = 2`: below, `|Δ²| ≤ h²(x - h)^{-1/2}`; above,
`|Δ²| ≤ 4(x + h)^{3/2}/γ²` with `Σ_{|γ|>T} 1/γ² ≤ log T/(πT)` by a layer cake.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.SigmaT
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.Lemma26P (Mt Rt Mt_eq c_lower c_upper)
open LeanLab.Dudek2014.Section22 (hD hD_small SigmaBd)

variable {ι : Type*}

/-- Cited, Trudgian 2014 in its `N(T)` form, as counts over any finite set of the ordinates, both
signs, for `70 ≤ T ≤ t`. -/
def TrudgianN70 (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 70 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)) ∧
  (∀ T t : ℝ, 70 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + Rt t) - (Mt T - Rt T)))

/-! ### Elementary bounds -/

lemma log_le_half {y : ℝ} (hy : 0 < y) : log y ≤ y / 2 := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  have e : log y = 2 * log (√y) := by
    rw [← Real.log_rpow (Real.sqrt_pos.mpr hy), Real.rpow_two, Real.sq_sqrt hy.le]
    
  have hs := Real.sq_sqrt hy.le
  nlinarith [sq_nonneg (√y - 2)]

lemma log_70 : log 70 ≤ 4.3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 : (1.3 : ℝ) ≤ exp 0.3 := by linarith [Real.add_one_le_exp (0.3 : ℝ)]
  have e : exp 4.3 = exp 1 ^ 4 * exp 0.3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 4 ≤ exp 1 ^ 4 := by gcongr
  nlinarith

lemma log_le_tenth {T : ℝ} (hT : 70 ≤ T) : log T ≤ T / 10 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / 70)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  linarith [log_70]

lemma log_ge_four {T : ℝ} (hT : 70 ≤ T) : 4 ≤ log T := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  have e : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
  nlinarith

/-- `R(t) ≤ 0.251 log t + 2.51 + 0.2/T` for `70 ≤ T ≤ t`. -/
lemma Rt_le {T t : ℝ} (hT : 70 ≤ T) (hTt : T ≤ t) : Rt t ≤ 0.251 * log t + 2.51 + 0.2 / T := by
  have ht : 0 < t := by linarith
  have hl := log_ge_four (hT.trans hTt)
  have hll := log_le_half (by linarith : (0 : ℝ) < log t)
  have h2 : 0.2 / t ≤ 0.2 / T := by gcongr
  unfold Rt; nlinarith

/-! ### The zero counts -/

/-- `#{|γ| ≤ T} ≤ T log T/π` for `T ≥ 70`. -/
lemma head_count {γ : ι → ℝ} (hN : TrudgianN70 γ) {T : ℝ} (hT : 70 ≤ T) (s : Finset ι) :
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ T * log T / π := by
  have hT0 : 0 < T := by linarith
  have h := hN.1 T hT s
  have hR := Rt_le hT le_rfl
  have hl := log_le_tenth hT
  have hc := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have h02 : 0.2 / T ≤ 0.01 := by rw [div_le_iff₀ hT0]; nlinarith
  rw [Mt_eq hT0] at h
  rw [le_div_iff₀ Real.pi_pos]
  have e : 2 * (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 + Rt T) * π =
      T * (log T - log (2 * π) - 1) + (7 / 4 + 2 * Rt T) * π := by field_simp; ring
  have h' := mul_le_mul_of_nonneg_right h Real.pi_pos.le
  rw [e] at h'
  nlinarith

/-- `2/t³ = (d/dt)(-1/t²)`. -/
lemma hasDerivAt_inv_sq {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => -(1 / x ^ 2)) (2 / t ^ 3) t := by
  have h := ((hasDerivAt_pow 2 t).inv (by positivity)).neg
  convert h using 1
  · funext x; simp [one_div]
  · field_simp; ring

lemma tendsto_inv_sq : Tendsto (fun x : ℝ => -(1 / x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
  simpa [one_div] using h.neg

lemma integral_two_div_cube {g : ℝ} (hg : 0 < g) : ∫ t in Ioi g, 2 / t ^ 3 = 1 / g ^ 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (hasDerivAt_inv_sq hg).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_inv_sq (by simp at hx; linarith))
    (fun x hx => by simp at hx; have : 0 < x := by linarith
                    positivity) tendsto_inv_sq]
  ring

lemma integrableOn_two_div_cube {g : ℝ} (hg : 0 < g) : IntegrableOn (fun t => 2 / t ^ 3) (Ioi g) :=
  integrableOn_Ioi_deriv_of_nonneg (hasDerivAt_inv_sq hg).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_inv_sq (by simp at hx; linarith))
    (fun x hx => by simp at hx; have : 0 < x := by linarith
                    positivity) tendsto_inv_sq

/-- The constant part of the error, `A_T = 5.02 + 0.4/T + 2R(T)`. -/
noncomputable def AT (T : ℝ) : ℝ := 5.02 + 0.4 / T + 2 * Rt T

/-- The majorant of the count times `2/t³`. -/
noncomputable def h2 (T t : ℝ) : ℝ :=
  ((t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π + 0.502 * log t + AT T)
    * (2 / t ^ 3)

/-- Its tail integral. -/
noncomputable def H2 (T x : ℝ) : ℝ :=
  2 * (log x - log (2 * π)) / (π * x) - T * (log T - log (2 * π) - 1) / (π * x ^ 2)
    + 1.004 * (2 * log x + 1) / (4 * x ^ 2) + AT T / x ^ 2

lemma hasDerivAt_negH2 (T : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => -H2 T y) (h2 T x) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have h1 := ((hl.sub_const (log (2 * π))).const_mul 2).div ((hasDerivAt_id x).const_mul π)
    (by rw [id]; positivity)
  have h2' := (hasDerivAt_const x (T * (log T - log (2 * π) - 1))).div
    ((hasDerivAt_pow 2 x).const_mul π) (by positivity)
  have h3 := ((hl.const_mul 2).add_const 1).const_mul 1.004 |>.div
    ((hasDerivAt_pow 2 x).const_mul 4) (by positivity)
  have h4 := (hasDerivAt_const x (AT T)).div (hasDerivAt_pow 2 x) (by positivity)
  have h := (((h1.sub h2').add h3).add h4).neg
  convert h using 1
  · funext y
    simp only [H2, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, id]
  · unfold h2
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring

lemma tendsto_H2 (T : ℝ) : Tendsto (H2 T) atTop (𝓝 0) := by
  have a1 := LeanLab.ChirreHagen2025.Lemma26P.tendsto_log_pow_div 1
  have a0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have b1 := LeanLab.ChirreHagen2025.Lemma26P.tendsto_log_pow_div_sq 1
  have b0 := LeanLab.ChirreHagen2025.Lemma26P.tendsto_log_pow_div_sq 0
  have h := ((((a1.const_mul (2 / π)).sub (a0.const_mul (2 * log (2 * π) / π))).sub
    (b0.const_mul (T * (log T - log (2 * π) - 1) / π))).add
    ((b1.const_mul (1.004 * 2 / 4)).add (b0.const_mul (1.004 / 4)))).add (b0.const_mul (AT T))
  simp only [mul_zero, add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [H2, pow_one, pow_zero]
  field_simp

lemma AT_le {T : ℝ} (hT : 70 ≤ T) : AT T ≤ 0.502 * log T + 10.07 := by
  have hT0 : 0 < T := by linarith
  have hR := Rt_le hT le_rfl
  have h04 : 0.4 / T ≤ 0.01 := by rw [div_le_iff₀ hT0]; nlinarith
  have h02 : 0.2 / T ≤ 0.005 := by rw [div_le_iff₀ hT0]; nlinarith
  unfold AT; linarith

lemma h2_nonneg {T t : ℝ} (hT : 70 ≤ T) (ht : T ≤ t) : 0 ≤ h2 T t := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hlT := log_ge_four hT
  have hlt := Real.log_le_log hT0 ht
  have hc := c_upper
  have hR : 0 ≤ Rt T := by
    have := log_le_half (by linarith : (0 : ℝ) < log T)
    have hll : 0 ≤ log (log T) := Real.log_nonneg (by linarith)
    unfold Rt; positivity
  unfold h2 AT
  apply mul_nonneg _ (by positivity)
  have : 0 ≤ (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π := by
    apply div_nonneg _ Real.pi_pos.le
    nlinarith
  have : 0 ≤ 0.4 / T := by positivity
  nlinarith

lemma integral_h2 {T : ℝ} (hT : 70 ≤ T) :
    IntegrableOn (h2 T) (Ioi T) ∧ ∫ t in Ioi T, h2 T t = H2 T T := by
  have hT0 : 0 < T := by linarith
  have hc : ContinuousWithinAt (fun y => -H2 T y) (Ici T) T :=
    (hasDerivAt_negH2 T hT0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioi T, HasDerivAt (fun y => -H2 T y) (h2 T x) x :=
    fun x hx => hasDerivAt_negH2 T (by simp at hx; linarith)
  have hp : ∀ x ∈ Ioi T, 0 ≤ h2 T x := fun x hx => h2_nonneg hT (le_of_lt hx)
  have hl : Tendsto (fun y => -H2 T y) atTop (𝓝 0) := by simpa using (tendsto_H2 T).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hp hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd hp hl]; ring

lemma H2_bound {T : ℝ} (hT : 70 ≤ T) : H2 T T ≤ log T / (π * T) := by
  have hT0 : 0 < T := by linarith
  have hl := log_le_tenth hT
  have hl4 := log_ge_four hT
  have hA := AT_le hT
  have hc := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have e : H2 T T = (log T - log (2 * π) + 1) / (π * T)
      + (0.502 * log T + 0.251 + AT T) / T ^ 2 := by
    unfold H2; field_simp; ring
  rw [e]
  have h1 : (0.502 * log T + 0.251 + AT T) / T ^ 2 ≤ 0.8 / (π * T) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0.502 * log T + 0.251 + AT T) * π ≤ 0.8 * T := by nlinarith
    nlinarith
  have h2' : (log T - log (2 * π) + 1) / (π * T) + 0.8 / (π * T) ≤ log T / (π * T) := by
    rw [← add_div]; gcongr; linarith
  linarith

/-- `Σ_{|γ| > T} 1/γ² ≤ log T/(πT)` for `T ≥ 70`, over any finite set. -/
lemma tail_inv_sq {γ : ι → ℝ} (hN : TrudgianN70 γ) {T : ℝ} (hT : 70 ≤ T) (s : Finset ι) :
    (∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2) ≤ log T / (π * T) := by
  have hT0 : 0 < T := by linarith
  set S := s.filter (fun i => ¬ |γ i| ≤ T)
  obtain ⟨hhi, hhint⟩ := integral_h2 hT
  have hterm : ∀ i ∈ S, 1 / γ i ^ 2 =
      ∫ t in Ioi T, (Ioi |γ i|).indicator (fun t => 2 / t ^ 3) t := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hg : T < |γ i| := lt_of_not_ge hi.2
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hg.le,
      integral_two_div_cube (by linarith), sq_abs]
  have hint : ∀ i ∈ S, Integrable (fun t => (Ioi |γ i|).indicator (fun t => 2 / t ^ 3) t)
      (volume.restrict (Ioi T)) :=
    fun i _ => (integrableOn_two_div_cube hT0).indicator measurableSet_Ioi
  rw [Finset.sum_congr rfl hterm, ← integral_finset_sum S hint]
  refine (setIntegral_mono_on (integrable_finset_sum S hint) hhi measurableSet_Ioi
    fun t ht => ?_).trans (hhint.trans_le (H2_bound hT))
  have ht' : T < t := ht
  have ht0 : 0 < t := by linarith
  have hφ : 0 ≤ 2 / t ^ 3 := by positivity
  have e : ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 2 / t ^ 3) t =
      ((S.filter (fun i => |γ i| < t)).card : ℝ) * (2 / t ^ 3) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : |γ i| < t
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [e]
  have hsub : S.filter (fun i => |γ i| < t) ⊆ s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t) := by
    intro i hi
    simp only [S, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1.1, lt_of_not_ge hi.1.2, hi.2.le⟩
  have hc1 : ((S.filter (fun i => |γ i| < t)).card : ℝ) ≤
      ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hc2 := hN.2 T t hT ht'.le s
  have hRt := Rt_le hT ht'.le
  have hcount : ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤
      (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π + 0.502 * log t + AT T := by
    rw [Mt_eq ht0, Mt_eq hT0] at hc2
    have e2 : 2 * ((t * (log t - log (2 * π) - 1) / (2 * π) + 7 / 8 + Rt t) -
        (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 - Rt T)) =
        (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π
          + 2 * Rt t + 2 * Rt T := by field_simp; ring
    rw [e2] at hc2
    have : 0.4 / T = 2 * (0.2 / T) := by ring
    unfold AT; linarith
  unfold h2
  exact mul_le_mul_of_nonneg_right (hc1.trans hcount) hφ

/-! ### One zero: the second difference of `t^{ρ+1}/(ρ(ρ+1))` -/

/-- `ρ = 1/2 + iγ`. -/
noncomputable def rhoF (g : ℝ) : ℂ := 1 / 2 + g * Complex.I

/-- `t^{ρ+1}/(ρ(ρ+1))`. -/
noncomputable def fz (ρ : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

/-- `t^ρ/ρ`. -/
noncomputable def f1 (ρ : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ ρ / ρ

lemma rhoF_re (g : ℝ) : (rhoF g).re = 1 / 2 := by simp [rhoF]

lemma rhoF_ne (g : ℝ) : rhoF g ≠ 0 := fun h => by
  have := congrArg Complex.re h; rw [rhoF_re] at this; simp at this

lemma rhoF_ne' (g : ℝ) : rhoF g ≠ -1 := fun h => by
  have := congrArg Complex.re h; rw [rhoF_re] at this; simp at this; norm_num at this

lemma hasDerivAt_fz (g : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (fz (rhoF g)) (f1 (rhoF g) t) t := by
  have h0 := rhoF_ne g
  have h1 : rhoF g + 1 ≠ 0 := fun h => rhoF_ne' g (by linear_combination h)
  have := (hasDerivAt_ofReal_cpow_const' ht.ne' (rhoF_ne' g)).div_const (rhoF g)
  convert this using 1
  · funext y; unfold fz; field_simp
  · unfold f1; rfl

lemma hasDerivAt_f1 (g : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (f1 (rhoF g)) ((t : ℂ) ^ (rhoF g - 1)) t := by
  have h0 := rhoF_ne g
  have := hasDerivAt_ofReal_cpow_const' ht.ne' (r := rhoF g - 1) (by
    intro h; exact h0 (by linear_combination h))
  simp only [sub_add_cancel] at this
  exact this

lemma norm_cpow_rhoF {g t : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖(t : ℂ) ^ (rhoF g + w)‖ = t ^ (1 / 2 + w.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp [rhoF_re]

/-- `|Δ²| ≤ h² (x - h)^{-1/2}`. -/
lemma second_diff_small (g : ℝ) {x h : ℝ} (hh : 0 < h) (hhx : h < x) :
    ‖fz (rhoF g) (x + h) - 2 * fz (rhoF g) x + fz (rhoF g) (x - h)‖
      ≤ h ^ 2 * (x - h) ^ (-1 / 2 : ℝ) := by
  set K := (x - h) ^ (-1 / 2 : ℝ)
  have hxh : 0 < x - h := by linarith
  -- the first derivative moves by at most `K h`
  have step1 : ∀ u ∈ Icc (0 : ℝ) h,
      ‖f1 (rhoF g) (x + u) - f1 (rhoF g) (x - h + u)‖ ≤ K * h := by
    intro u hu
    have hm := norm_image_sub_le_of_norm_deriv_le_segment' (f := f1 (rhoF g))
      (a := x - h + u) (b := x + u) (C := K)
      (fun v hv => (hasDerivAt_f1 g (by linarith [hv.1, hu.1])).hasDerivWithinAt)
      (fun v hv => by
        have hv0 : 0 < v := by linarith [hv.1, hu.1]
        have e : (v : ℂ) ^ (rhoF g - 1) = (v : ℂ) ^ (rhoF g + (-1 : ℂ)) := by ring_nf
        rw [e, norm_cpow_rhoF hv0]
        have e2 : (1 / 2 : ℝ) + (-1 : ℂ).re = -1 / 2 := by norm_num
        rw [e2]
        exact Real.rpow_le_rpow_of_nonpos hxh (by linarith [hv.1, hu.1]) (by norm_num))
      (x + u) ⟨by linarith, le_rfl⟩
    calc _ ≤ K * (x + u - (x - h + u)) := hm
      _ = K * h := by ring
  have hK : 0 ≤ K := Real.rpow_nonneg hxh.le _
  set G : ℝ → ℂ := fun u => fz (rhoF g) (x + u) - fz (rhoF g) (x - h + u)
  have hG : ∀ u ∈ Icc (0 : ℝ) h, HasDerivWithinAt G
      (f1 (rhoF g) (x + u) - f1 (rhoF g) (x - h + u)) (Icc 0 h) u := by
    intro u hu
    have a1 := (hasDerivAt_fz g (by linarith [hu.1] : 0 < x + u)).comp_const_add x u
    have a2 := (hasDerivAt_fz g (by linarith [hu.1] : 0 < x - h + u)).comp_const_add (x - h) u
    exact (a1.sub a2).hasDerivWithinAt
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hG
    (fun u hu => step1 u (Ico_subset_Icc_self hu)) h ⟨hh.le, le_rfl⟩
  have e : G h - G 0 = fz (rhoF g) (x + h) - 2 * fz (rhoF g) x + fz (rhoF g) (x - h) := by
    simp only [G, add_zero, sub_add_cancel]; ring
  rw [← e]
  calc ‖G h - G 0‖ ≤ K * h * (h - 0) := hm
    _ = h ^ 2 * K := by ring

lemma norm_rho_mul_ge (g : ℝ) : g ^ 2 ≤ ‖rhoF g * (rhoF g + 1)‖ := by
  rw [norm_mul]
  have h1 : |g| ≤ ‖rhoF g‖ := by
    have := Complex.abs_im_le_norm (rhoF g); simpa [rhoF] using this
  have h2 : |g| ≤ ‖rhoF g + 1‖ := by
    have := Complex.abs_im_le_norm (rhoF g + 1); simpa [rhoF] using this
  calc g ^ 2 = |g| * |g| := by rw [← sq, sq_abs]
    _ ≤ ‖rhoF g‖ * ‖rhoF g + 1‖ := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

lemma norm_rho_mul_ge' (g : ℝ) : 3 / 4 ≤ ‖rhoF g * (rhoF g + 1)‖ := by
  rw [norm_mul]
  have h1 : 1 / 2 ≤ ‖rhoF g‖ := by
    have := Complex.abs_re_le_norm (rhoF g); rw [rhoF_re] at this; simpa using this
  have h2 : 3 / 2 ≤ ‖rhoF g + 1‖ := by
    have := Complex.abs_re_le_norm (rhoF g + 1); simp [rhoF_re] at this; norm_num at this
    simpa using this
  nlinarith

lemma norm_fz_le (g : ℝ) {t B : ℝ} (ht : 0 < t) (htB : t ≤ B) :
    ‖fz (rhoF g) t‖ * ‖rhoF g * (rhoF g + 1)‖ ≤ B ^ (3 / 2 : ℝ) := by
  have hn : 0 < ‖rhoF g * (rhoF g + 1)‖ := lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' g)
  unfold fz
  rw [norm_div, div_mul_cancel₀ _ hn.ne', show rhoF g + 1 = rhoF g + (1 : ℂ) from rfl,
    norm_cpow_rhoF ht]
  norm_num
  exact Real.rpow_le_rpow ht.le htB (by norm_num)

/-- `|Δ²| ≤ 4 (x + h)^{3/2}/|ρ(ρ+1)|`. -/
lemma second_diff_large (g : ℝ) {x h : ℝ} (hh : 0 < h) (hhx : h < x) :
    ‖fz (rhoF g) (x + h) - 2 * fz (rhoF g) x + fz (rhoF g) (x - h)‖
      ≤ 4 * (x + h) ^ (3 / 2 : ℝ) / ‖rhoF g * (rhoF g + 1)‖ := by
  have hn : 0 < ‖rhoF g * (rhoF g + 1)‖ := lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' g)
  have a := norm_fz_le g (by linarith : 0 < x + h) le_rfl
  have b := norm_fz_le g (by linarith : 0 < x) (by linarith : x ≤ x + h)
  have c := norm_fz_le g (by linarith : 0 < x - h) (by linarith : x - h ≤ x + h)
  rw [le_div_iff₀ hn]
  calc ‖fz (rhoF g) (x + h) - 2 * fz (rhoF g) x + fz (rhoF g) (x - h)‖ * ‖rhoF g * (rhoF g + 1)‖
      ≤ (‖fz (rhoF g) (x + h)‖ + 2 * ‖fz (rhoF g) x‖ + ‖fz (rhoF g) (x - h)‖)
          * ‖rhoF g * (rhoF g + 1)‖ := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]; norm_num
    _ ≤ 4 * (x + h) ^ (3 / 2 : ℝ) := by nlinarith

/-! ### The zero sum and `SigmaBd` -/

/-- `Z(y) = Re Σ_i y^{ρ_i+1}/(ρ_i(ρ_i+1))`, `ρ_i = 1/2 + iγ_i`. -/
noncomputable def Zr (γ : ι → ℝ) (y : ℝ) : ℝ := (∑' i, fz (rhoF (γ i)) y).re

/-- `1/|ρ(ρ+1)|`. -/
noncomputable def wgt (γ : ι → ℝ) (i : ι) : ℝ := 1 / ‖rhoF (γ i) * (rhoF (γ i) + 1)‖

lemma wgt_le (γ : ι → ℝ) (i : ι) : wgt γ i ≤ 4 / 3 := by
  unfold wgt
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' _))]
  linarith [norm_rho_mul_ge' (γ i)]

lemma wgt_le_inv_sq (γ : ι → ℝ) {i : ι} (hi : γ i ≠ 0) : wgt γ i ≤ 1 / γ i ^ 2 := by
  unfold wgt
  exact one_div_le_one_div_of_le (by positivity) (norm_rho_mul_ge _)

lemma wgt_nonneg (γ : ι → ℝ) (i : ι) : 0 ≤ wgt γ i := by unfold wgt; positivity

lemma split_bound {γ : ι → ℝ} (hN : TrudgianN70 γ) {T a b : ℝ} (hT : 70 ≤ T) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (F : ι → ℝ) (hFs : ∀ i, |γ i| ≤ T → F i ≤ a)
    (hFl : ∀ i, ¬ |γ i| ≤ T → F i ≤ b / γ i ^ 2) (s : Finset ι) :
    ∑ i ∈ s, F i ≤ T * log T / π * a + b * (log T / (π * T)) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)]
  have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), F i ≤ T * log T / π * a := by
    calc _ ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T), a :=
          Finset.sum_le_sum fun i hi => hFs i (Finset.mem_filter.mp hi).2
      _ = ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) * a := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T * log T / π * a := by gcongr; exact head_count hN hT s
  have h2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), F i ≤ b * (log T / (π * T)) := by
    calc _ ≤ ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), b * (1 / γ i ^ 2) :=
          Finset.sum_le_sum fun i hi => by
            have := hFl i (Finset.mem_filter.mp hi).2; rw [mul_one_div]; exact this
      _ = b * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ b * (log T / (π * T)) := by gcongr; exact tail_inv_sq hN hT s
  linarith

lemma ne_of_large {γ : ι → ℝ} {T : ℝ} (hT : 70 ≤ T) {i : ι} (h : ¬ |γ i| ≤ T) : γ i ≠ 0 := by
  intro h0; rw [h0, abs_zero] at h; exact h (by linarith)

lemma summable_wgt {γ : ι → ℝ} (hN : TrudgianN70 γ) : Summable (wgt γ) :=
  summable_of_sum_le (fun i => wgt_nonneg γ i) fun s =>
    split_bound hN (a := 4 / 3) (b := 1) (le_refl 70) (by norm_num) (by norm_num) (wgt γ)
      (fun i _ => wgt_le γ i) (fun i hi => by
        exact wgt_le_inv_sq γ (ne_of_large (le_refl 70) hi)) s

lemma norm_fz_le' (g : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖fz (rhoF g) y‖ ≤ y ^ (3 / 2 : ℝ) * (1 / ‖rhoF g * (rhoF g + 1)‖) := by
  have hn : 0 < ‖rhoF g * (rhoF g + 1)‖ := lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' g)
  rw [mul_one_div, le_div_iff₀ hn]; exact norm_fz_le g hy le_rfl

lemma summable_fz {γ : ι → ℝ} (hN : TrudgianN70 γ) {y : ℝ} (hy : 0 < y) :
    Summable (fun i => fz (rhoF (γ i)) y) :=
  Summable.of_norm_bounded ((summable_wgt hN).mul_left (y ^ (3 / 2 : ℝ)))
    (fun i => norm_fz_le' (γ i) hy)

lemma log_65000_le : log 65000 ≤ 11.1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 : (1.1 : ℝ) ≤ exp 0.1 := by linarith [Real.add_one_le_exp (0.1 : ℝ)]
  have e : exp 11.1 = exp 1 ^ 11 * exp 0.1 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 11 ≤ exp 1 ^ 11 := by gcongr
  nlinarith

/-- `T = 2x/h ≥ 70` for `x ≥ 65000`, `h = (2/π)√x log x`. -/
lemma T_ge {x : ℝ} (hx : 65000 ≤ x) : 70 ≤ 2 * x / hD x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hh0, _⟩ := hD_small hx
  set s := √(x / 65000)
  have hs1 : 1 ≤ s := by rw [Real.le_sqrt (by norm_num) (by positivity)]; rw [le_div_iff₀ (by norm_num)]; linarith
  have hxs : x = 65000 * s ^ 2 := by rw [Real.sq_sqrt (by positivity)]; field_simp
  have hsq : √x = √65000 * s := by
    rw [hxs, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]
  have h65 : (254.9 : ℝ) ≤ √65000 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hlog : log x ≤ 11.1 + 2 * (s - 1) := by
    rw [hxs, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < s)
    push_cast; linarith [log_65000_le]
  have hL : 0 < log x := Real.log_pos (by linarith)
  have hπ := Real.pi_gt_d2
  have h1 : 3.14 * 254.9 ≤ π * √65000 := mul_le_mul hπ.le h65 (by norm_num) (by positivity)
  have key : 70 * log x ≤ π * √x := by
    rw [hsq, ← mul_assoc]
    have : 3.14 * 254.9 * s ≤ π * √65000 * s := mul_le_mul_of_nonneg_right h1 (by linarith)
    nlinarith
  unfold hD
  rw [le_div_iff₀ (by positivity)]
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0.le
  have : 70 * (2 / π * √x * log x) = 2 * √x * (70 * log x) / π := by field_simp
  rw [this, div_le_iff₀ (by positivity)]
  nlinarith [Real.sqrt_nonneg x]

/-- **Dudek's page 5 bound `SigmaBd`, PROVED CONDITIONAL ON `TrudgianN70`**, for the zero sum
`Zr γ` of any ordinate family on the critical line. -/
theorem sigmaBd_of_trudgian {γ : ι → ℝ} (hN : TrudgianN70 γ) :
    SigmaBd (fun x h => Zr γ (x + h) - 2 * Zr γ x + Zr γ (x - h)) := by
  intro x hx
  obtain ⟨hh0, hhx2⟩ := hD_small hx
  set h := hD x with hhdef
  have hx0 : 0 < x := by linarith
  have hhx : h < x := by linarith
  have hxh : 0 < x - h := by linarith
  set T := 2 * x / h with hTdef
  have hT := T_ge hx
  set D : ι → ℂ := fun i =>
    fz (rhoF (γ i)) (x + h) - 2 * fz (rhoF (γ i)) x + fz (rhoF (γ i)) (x - h)
  have sa := summable_fz hN (by linarith : 0 < x + h)
  have sb := summable_fz hN hx0
  have sc := summable_fz hN hxh
  have eD : ∑' i, D i = (∑' i, fz (rhoF (γ i)) (x + h)) - 2 * (∑' i, fz (rhoF (γ i)) x)
      + ∑' i, fz (rhoF (γ i)) (x - h) := by
    rw [← tsum_mul_left, ← sa.tsum_sub (sb.mul_left 2), ← (sa.sub (sb.mul_left 2)).tsum_add sc]
  have e : Zr γ (x + h) - 2 * Zr γ x + Zr γ (x - h) = (∑' i, D i).re := by
    rw [eD]; unfold Zr; simp [Complex.add_re, Complex.sub_re]
  show |Zr γ (x + h) - 2 * Zr γ x + Zr γ (x - h)| ≤ _
  rw [e]
  set B := 4 * (x + h) ^ (3 / 2 : ℝ)
  have hB : 0 ≤ B := by positivity
  set a := h ^ 2 * (x - h) ^ (-1 / 2 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hDn : ∀ i, ‖D i‖ ≤ B * wgt γ i := fun i => by
    have := second_diff_large (γ i) hh0 hhx; unfold wgt; rw [mul_one_div]; exact this
  have hsumN : Summable (fun i => ‖D i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hDn ((summable_wgt hN).mul_left B)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖D i‖ ≤ T * log T / π * a + B * (log T / (π * T)) :=
    split_bound hN hT ha hB (fun i => ‖D i‖) (fun i _ => second_diff_small (γ i) hh0 hhx)
      (fun i hi => (hDn i).trans (by
        rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left (wgt_le_inv_sq γ (ne_of_large hT hi)) hB))
  have htot := hsumN.tsum_le_of_sum_le hfin
  have hK : (x - h) ^ (-1 / 2 : ℝ) = 1 / √(x - h) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hxh.le]
    exact (one_div _).symm
  have eq : T * log T / π * a + B * (log T / (π * T)) =
      (2 * x * h / (π * √(x - h)) + 4 * h * (x + h) ^ (3 / 2 : ℝ) / (π * 2 * x)) *
        log (2 * x / h) := by
    have hs : 0 < √(x - h) := Real.sqrt_pos.mpr hxh
    simp only [a, B, hK, hTdef]
    field_simp
  calc |(∑' i, D i).re| ≤ ‖∑' i, D i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' i, ‖D i‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ _ := htot
    _ = _ := eq

end LeanLab.Dudek2014.SigmaT
