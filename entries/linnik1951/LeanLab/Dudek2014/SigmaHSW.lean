module

public import Mathlib
public import LeanLab.Dudek2014.SigmaTrudgian
public import LeanLab.ChirreHagen2025.Lemma26HSW

/-!
P0100 A. Dudek, On the Riemann hypothesis and the difference between primes, arXiv 1402.6417,
unit U-6650, CLOUD 20261020T1717Z-cloud47, 2026-10-20.
Dudek's page 5 zero-sum bound `SigmaBd`, PROVED CONDITIONAL ON `HSWN70`: the `N(T)` bound of
Hasanalizade, Shen and Wong, arXiv 2107.06506, Corollary 1.2,
`|N(T) - (T/2π) log(T/(2πe))| ≤ 0.1038 log T + 0.2573 log log T + 9.3675` for `T ≥ e`,
read as counts of the ordinates, both signs, for `T ≥ 70`, with the `7/8` of the main term `Mt`
moved into the error as in `ChirreHagen2025/Lemma26HSW.lean`.
This replaces `SigmaT.TrudgianN70`, whose `2.510 + 0.2/T` rests on Trudgian, JNT 134 (2014), which
Hasanalizade-Shen-Wong report contains an error, an incorrect `|ζ(1 + it)|` bound; see U-1247.
With the larger constant `10.2425` the separate bounds of SigmaTrudgian.lean fail near `T = 70`:
the tail `Σ_{|γ|>T} 1/γ² ≤ log T/(πT)` needs about `T ≥ 120`. The proof here keeps the split at
`T = 2x/h` and trades the slack of the head count, about `0.89 T`, against the tail excess,
using that the tail weight `4(x + h)^{3/2}` is at most `1.1 T²` times the head weight
`h²(x - h)^{-1/2}`. The single-zero bounds are reused from SigmaTrudgian.lean.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.SigmaH
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt c_lower c_upper)
open LeanLab.Dudek2014.Section22 (hD hD_small SigmaBd)
open LeanLab.Dudek2014.SigmaT (log_le_half log_le_tenth log_ge_four integral_two_div_cube
  integrableOn_two_div_cube rhoF fz Zr wgt wgt_le wgt_le_inv_sq wgt_nonneg ne_of_large
  norm_fz_le' second_diff_small second_diff_large T_ge)

variable {ι : Type*}

/-- Cited, Hasanalizade-Shen-Wong arXiv 2107.06506 Corollary 1.2 in its `N(T)` form, with the
`7/8` moved into the error, as counts over any finite set of the ordinates, both signs, for
`70 ≤ T ≤ t`. -/
def HSWN70 (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 70 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)) ∧
  (∀ T t : ℝ, 70 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + Rt t) - (Mt T - Rt T)))

lemma Mt_eq {x : ℝ} (hx : 0 < x) :
    Mt x = x * (log x - log (2 * π) - 1) / (2 * π) + 7 / 8 := by
  unfold Mt
  rw [Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) (Real.exp_pos 1).ne',
    Real.log_exp]
  ring

/-- `R(t) ≤ 0.251 log t + 10.25` for `t ≥ 70`. -/
lemma Rt_le {t : ℝ} (ht : 70 ≤ t) : Rt t ≤ 0.251 * log t + 10.25 := by
  have hl := log_ge_four ht
  have hll := log_le_half (by linarith : (0 : ℝ) < log t)
  unfold Rt; nlinarith

lemma Rt_nonneg {t : ℝ} (ht : 70 ≤ t) : 0 ≤ Rt t := by
  have hl := log_ge_four ht
  have hll : 0 ≤ log (log t) := Real.log_nonneg (by linarith)
  unfold Rt; positivity

/-! ### The zero counts -/

/-- The head count `#{|γ| ≤ T} ≤ T log T/π - (0.89 T - 22.25 - 0.502 log T)` for `T ≥ 70`. -/
lemma head_count {γ : ι → ℝ} (hN : HSWN70 γ) {T : ℝ} (hT : 70 ≤ T) (s : Finset ι) :
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤
      T * log T / π - (0.89 * T - 22.25 - 0.502 * log T) := by
  have hT0 : 0 < T := by linarith
  have h := hN.1 T hT s
  have hR := Rt_le hT
  have hc := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  rw [Mt_eq hT0] at h
  have e : 2 * (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 + Rt T) =
      T * log T / π - T * (log (2 * π) + 1) / π + (7 / 4 + 2 * Rt T) := by field_simp; ring
  rw [e] at h
  have h1 : 0.89 * T ≤ T * (log (2 * π) + 1) / π := by
    have hπ4 := Real.pi_lt_d4
    rw [le_div_iff₀ Real.pi_pos]
    have : 0 ≤ T * (log (2 * π) + 1 - 0.89 * π) := mul_nonneg hT0.le (by linarith)
    nlinarith
  linarith

/-- The constant part of the tail error, `A_T = 20.5 + 2R(T)`. -/
noncomputable def AT (T : ℝ) : ℝ := 20.5 + 2 * Rt T

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

lemma AT_le {T : ℝ} (hT : 70 ≤ T) : AT T ≤ 0.502 * log T + 41 := by
  have hR := Rt_le hT
  unfold AT; linarith

lemma h2_nonneg {T t : ℝ} (hT : 70 ≤ T) (ht : T ≤ t) : 0 ≤ h2 T t := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hlT := log_ge_four hT
  have hlt := Real.log_le_log hT0 ht
  have hc := c_upper
  have hR := Rt_nonneg hT
  unfold h2 AT
  apply mul_nonneg _ (by positivity)
  have : 0 ≤ (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π := by
    apply div_nonneg _ Real.pi_pos.le
    nlinarith
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

/-- `H2(T, T) ≤ log T/(πT) + (1.004 log T + 41.26 - 0.25 T)/T²`. -/
lemma H2_bound {T : ℝ} (hT : 70 ≤ T) :
    H2 T T ≤ log T / (π * T) + (1.004 * log T + 41.26 - 0.25 * T) / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hA := AT_le hT
  have hc := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have e : H2 T T = log T / (π * T) - (log (2 * π) - 1) / (π * T)
      + (0.502 * log T + 0.251 + AT T) / T ^ 2 := by
    unfold H2; field_simp; ring
  rw [e]
  have h1 : 0.25 * T / T ^ 2 ≤ (log (2 * π) - 1) / (π * T) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0.25 * π ≤ log (2 * π) - 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ T ^ 2)
    nlinarith
  have h2' : (0.502 * log T + 0.251 + AT T) / T ^ 2 ≤ (1.004 * log T + 41.26) / T ^ 2 := by
    have := log_ge_four hT
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have e2 : (1.004 * log T + 41.26 - 0.25 * T) / T ^ 2 =
      (1.004 * log T + 41.26) / T ^ 2 - 0.25 * T / T ^ 2 := by ring
  rw [e2]; linarith

/-- `Σ_{|γ| > T} 1/γ² ≤ log T/(πT) + (1.004 log T + 41.26 - 0.25 T)/T²`, over any finite set. -/
lemma tail_inv_sq {γ : ι → ℝ} (hN : HSWN70 γ) {T : ℝ} (hT : 70 ≤ T) (s : Finset ι) :
    (∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2) ≤
      log T / (π * T) + (1.004 * log T + 41.26 - 0.25 * T) / T ^ 2 := by
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
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum S hint]
  refine (setIntegral_mono_on (integrable_finsetSum S hint) hhi measurableSet_Ioi
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
  have hRt := Rt_le (hT.trans ht'.le)
  have hcount : ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤
      (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π + 0.502 * log t + AT T := by
    rw [Mt_eq ht0, Mt_eq hT0] at hc2
    have e2 : 2 * ((t * (log t - log (2 * π) - 1) / (2 * π) + 7 / 8 + Rt t) -
        (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 - Rt T)) =
        (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π
          + 2 * Rt t + 2 * Rt T := by field_simp; ring
    rw [e2] at hc2
    unfold AT; linarith
  unfold h2
  exact mul_le_mul_of_nonneg_right (hc1.trans hcount) hφ

/-! ### The split, with the head slack paying for the tail -/

/-- The two error terms balance: `0.89 T - 22.25 - 0.502 log T ≥ 0` and
`≥ 1.1 (1.004 log T + 41.26 - 0.25 T)` for `T ≥ 70`. -/
lemma slack {T : ℝ} (hT : 70 ≤ T) :
    0 ≤ 0.89 * T - 22.25 - 0.502 * log T ∧
      1.1 * (1.004 * log T + 41.26 - 0.25 * T) ≤ 0.89 * T - 22.25 - 0.502 * log T := by
  have hl := log_le_tenth hT
  constructor <;> nlinarith

lemma split_bound {γ : ι → ℝ} (hN : HSWN70 γ) {T a b : ℝ} (hT : 70 ≤ T) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : b ≤ 1.1 * a * T ^ 2) (F : ι → ℝ) (hFs : ∀ i, |γ i| ≤ T → F i ≤ a)
    (hFl : ∀ i, ¬ |γ i| ≤ T → F i ≤ b / γ i ^ 2) (s : Finset ι) :
    ∑ i ∈ s, F i ≤ T * log T / π * a + b * (log T / (π * T)) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hD0, hDE⟩ := slack hT
  set D := 0.89 * T - 22.25 - 0.502 * log T
  set E := 1.004 * log T + 41.26 - 0.25 * T
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)]
  have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), F i ≤ (T * log T / π - D) * a := by
    calc _ ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T), a :=
          Finset.sum_le_sum fun i hi => hFs i (Finset.mem_filter.mp hi).2
      _ = ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) * a := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T * log T / π - D) * a := by gcongr; exact head_count hN hT s
  have h2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), F i ≤ b * (log T / (π * T) + E / T ^ 2) := by
    calc _ ≤ ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), b * (1 / γ i ^ 2) :=
          Finset.sum_le_sum fun i hi => by
            have := hFl i (Finset.mem_filter.mp hi).2; rw [mul_one_div]; exact this
      _ = b * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ b * (log T / (π * T) + E / T ^ 2) := by gcongr; exact tail_inv_sq hN hT s
  have h3 : b * (E / T ^ 2) ≤ D * a := by
    rcases le_or_gt E 0 with hE | hE
    · have : b * (E / T ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb (div_nonpos_of_nonpos_of_nonneg hE (by positivity))
      have := mul_nonneg hD0 ha
      linarith
    · have hT2 : 0 < T ^ 2 := by positivity
      have : b * (E / T ^ 2) ≤ 1.1 * a * E := by
        rw [mul_div_assoc', div_le_iff₀ hT2]
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left hDE ha
      have e4 : a * (1.1 * E) = 1.1 * a * E := by ring
      have e5 : a * D = D * a := by ring
      linarith
  have e6 : (T * log T / π - D) * a = T * log T / π * a - D * a := by ring
  have e7 : b * (log T / (π * T) + E / T ^ 2) = b * (log T / (π * T)) + b * (E / T ^ 2) := by ring
  linarith

lemma summable_wgt {γ : ι → ℝ} (hN : HSWN70 γ) : Summable (wgt γ) :=
  summable_of_sum_le (fun i => wgt_nonneg γ i) fun s =>
    split_bound hN (a := 4 / 3) (b := 1) (le_refl 70) (by norm_num) (by norm_num) (by norm_num)
      (wgt γ) (fun i _ => wgt_le γ i) (fun i hi => by
        exact wgt_le_inv_sq γ (ne_of_large (le_refl 70) hi)) s

lemma summable_fz {γ : ι → ℝ} (hN : HSWN70 γ) {y : ℝ} (hy : 0 < y) :
    Summable (fun i => fz (rhoF (γ i)) y) :=
  Summable.of_norm_bounded ((summable_wgt hN).mul_left (y ^ (3 / 2 : ℝ)))
    (fun i => norm_fz_le' (γ i) hy)

/-- The tail weight is at most `1.1 T²` times the head weight:
`4(x + h)^{3/2} ≤ 1.1 · h²(x - h)^{-1/2} · (2x/h)²` when `h ≤ x/35`. -/
lemma weight_ratio {x h : ℝ} (hh : 0 < h) (hhx : 35 * h ≤ x) :
    4 * (x + h) ^ (3 / 2 : ℝ) ≤ 1.1 * (h ^ 2 * (x - h) ^ (-1 / 2 : ℝ)) * (2 * x / h) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hxh : 0 < x - h := by linarith
  have hs : 0 < √(x - h) := Real.sqrt_pos.mpr hxh
  have hK : (x - h) ^ (-1 / 2 : ℝ) = 1 / √(x - h) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hxh.le]
    exact (one_div _).symm
  have h32 : (x + h) ^ (3 / 2 : ℝ) = (x + h) * √(x + h) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hprod : √(x + h) * √(x - h) ≤ x := by
    rw [← Real.sqrt_mul (by linarith)]
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  rw [hK, h32]
  have e : 1.1 * (h ^ 2 * (1 / √(x - h))) * (2 * x / h) ^ 2 = 4.4 * x ^ 2 / √(x - h) := by
    field_simp; ring
  rw [e, le_div_iff₀ hs]
  have : 4 * ((x + h) * √(x + h)) * √(x - h) = 4 * (x + h) * (√(x + h) * √(x - h)) := by ring
  rw [this]
  have hxh' : 0 ≤ 4 * (x + h) := by linarith
  calc 4 * (x + h) * (√(x + h) * √(x - h)) ≤ 4 * (x + h) * x :=
        mul_le_mul_of_nonneg_left hprod hxh'
    _ ≤ 4.4 * x ^ 2 := by nlinarith

/-- **Dudek's page 5 bound `SigmaBd`, PROVED CONDITIONAL ON `HSWN70`**, the corrected
Hasanalizade-Shen-Wong `N(T)` bound, for the zero sum `Zr γ` of any ordinate family on the
critical line. -/
theorem sigmaBd_of_hsw {γ : ι → ℝ} (hN : HSWN70 γ) :
    SigmaBd (fun x h => Zr γ (x + h) - 2 * Zr γ x + Zr γ (x - h)) := by
  intro x hx
  obtain ⟨hh0, hhx2⟩ := hD_small hx
  set h := hD x with hhdef
  have hx0 : 0 < x := by linarith
  have hhx : h < x := by linarith
  have hxh : 0 < x - h := by linarith
  set T := 2 * x / h with hTdef
  have hT := T_ge hx
  have h35 : 35 * h ≤ x := by
    have hT' : 70 ≤ 2 * x / h := hT
    rw [le_div_iff₀ hh0] at hT'; linarith
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
  have hab : B ≤ 1.1 * a * T ^ 2 := weight_ratio hh0 h35
  have hDn : ∀ i, ‖D i‖ ≤ B * wgt γ i := fun i => by
    have := second_diff_large (γ i) hh0 hhx; unfold wgt; rw [mul_one_div]; exact this
  have hsumN : Summable (fun i => ‖D i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hDn ((summable_wgt hN).mul_left B)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖D i‖ ≤ T * log T / π * a + B * (log T / (π * T)) :=
    split_bound hN hT ha hB hab (fun i => ‖D i‖) (fun i _ => second_diff_small (γ i) hh0 hhx)
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

end LeanLab.Dudek2014.SigmaH

