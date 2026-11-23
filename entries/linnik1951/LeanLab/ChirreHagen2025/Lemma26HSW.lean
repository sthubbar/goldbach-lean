module

public import Mathlib
public import LeanLab.ChirreHagen2025.SmoothTheorem2

/-!
P0075 line, T2, OPEN AUDIT U-1248, I-0010, PC 20261020T1503Z-30533, 2026-10-20.
Chirre-Hagen, arXiv 2512.23534v1, Lemma 2.6, the cited `Lemma26` of SmoothTheorem2.lean, PROVED
CONDITIONAL ON `HSWN` only: the N(T) bound of Hasanalizade, Shen and Wong, Counting zeros of the
Riemann zeta function, arXiv 2107.06506, Corollary 1.2, `|N(T) - (T/2π) log(T/(2πe))| ≤ 0.1038 log T
+ 0.2573 log log T + 9.3675` for `T ≥ e`, read here as counts of the ordinates, both signs, with the
`7/8` of the main term `Mt` moved into the error, `R2 = 0.1038 log T + 0.2573 log log T + 10.2425`.
This replaces `Lemma26P.TrudgianN`, whose 2.510 + 0.2/T rests on Trudgian, JNT 134 (2014), which
Hasanalizade-Shen-Wong report contains an error, an incorrect |ζ(1 + it)| bound of Cheng-Graham.
The proof is `Lemma26Proof.lean` with only the error bounds `R_le_base`, `R_sum`, `R_le` redone.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.Lemma26H
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.SmoothT2 (Lemma26)

variable {ι : Type*}

/-- The main term `M(T) = (T/2π) log(T/(2πe)) + 7/8`. -/
noncomputable def Mt (T : ℝ) : ℝ := T / (2 * π) * log (T / (2 * π * exp 1)) + 7 / 8

/-- The Hasanalizade-Shen-Wong error with the `7/8` added, `R2(T) = 0.1038 log T + 0.2573 log log T + 10.2425`. -/
noncomputable def Rt (T : ℝ) : ℝ := 0.1038 * log T + 0.2573 * log (log T) + 10.2425

/-- Cited, Hasanalizade-Shen-Wong arXiv 2107.06506 Corollary 1.2, with `7/8` moved into the error, as counts over any finite set of the ordinates, both signs:
at most `2(M(T) + R(T))` with `|γ| ≤ T`, and at most `2((M(t) + R(t)) - (M(T) - R(T)))` with
`T < |γ| ≤ t`, for `10^13 ≤ T ≤ t`. -/
def HSWN (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 10 ^ 13 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)) ∧
  (∀ T t : ℝ, 10 ^ 13 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + Rt t) - (Mt T - Rt T)))

/-! ### Elementary bounds -/

lemma log_1e13 : 29.8 ≤ log ((10 : ℝ) ^ 13) := by
  have h2 := Real.log_two_gt_d9
  have : log ((2 : ℝ) ^ 43) ≤ log ((10 : ℝ) ^ 13) := Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at this
  norm_num at this
  linarith

lemma exp_one_lt' : exp 1 < 2.7182818286 := Real.exp_one_lt_d9

lemma c_lower : 1.8 ≤ log (2 * π) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h9 : exp 1.8 ^ 5 = exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h1 : exp 1 ^ 9 < 2.7182818286 ^ 9 := by
    gcongr; exact exp_one_lt'
  have h2 : (2.7182818286 : ℝ) ^ 9 < 6.28 ^ 5 := by norm_num
  have hp : (6.28 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_d2]
  by_contra hc
  push_neg at hc
  have : (2 * π) ^ 5 < exp 1.8 ^ 5 := by gcongr
  have : (6.28 : ℝ) ^ 5 ≤ (2 * π) ^ 5 := by gcongr
  linarith

lemma c_upper : log (2 * π) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have := Real.exp_one_gt_d9
  have h : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [Real.pi_lt_d2]

/-- `log² T ≤ T/1000` for `T ≥ 10^13`. -/
lemma log_sq_small {T : ℝ} (hT : 10 ^ 13 ≤ T) : log T ^ 2 ≤ T / 1000 := by
  have hT0 : 0 < T := by linarith
  set u := T ^ (1 / 4 : ℝ)
  have hu0 : 0 < u := by positivity
  have hu4 : u ^ 4 = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hlog : log T = 4 * log u := by rw [← hu4, Real.log_pow]; norm_num
  have hlu : log u ≤ u := (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
  have hlu0 : 0 ≤ log u := by
    rw [hlog] at *
    have : (1 : ℝ) ≤ u := by
      by_contra h; push_neg at h
      have : u ^ 4 < 1 := by
        calc u ^ 4 < 1 ^ 4 := by gcongr
          _ = 1 := by norm_num
      linarith
    exact Real.log_nonneg this
  have hu : (1500 : ℝ) ≤ u := by
    by_contra h; push_neg at h
    have : u ^ 4 < 1500 ^ 4 := by gcongr
    norm_num at this; linarith
  rw [hlog]
  calc (4 * log u) ^ 2 ≤ (4 * u) ^ 2 := by gcongr
    _ = 16 * u ^ 2 := by ring
    _ ≤ u ^ 4 / 1000 := by nlinarith [sq_nonneg u]
    _ = T / 1000 := by rw [hu4]

lemma log30_lt : log (30 : ℝ) < 3.4013 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have hs : exp (3.4013 : ℝ) = exp 1 ^ 3 * exp 0.4013 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h04 : (1.4937 : ℝ) < exp 0.4013 := by
    have := Real.sum_le_exp_of_nonneg (x := (0.4013 : ℝ)) (by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [hs]
  have h3 : (20.085 : ℝ) < exp 1 ^ 3 := by
    have : (2.7182818283 : ℝ) ^ 3 < exp 1 ^ 3 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have h' : (20.085 : ℝ) < 2.7182818283 ^ 3 := by norm_num
    linarith
  have := mul_lt_mul'' h3 h04 (by norm_num) (by norm_num)
  linarith

lemma loglog_le {L : ℝ} (hL : 0 < L) : log L ≤ L / 30 + 2.4013 := by
  have h := Real.log_le_sub_one_of_pos (x := L / 30) (by positivity)
  rw [Real.log_div hL.ne' (by norm_num)] at h
  linarith [log30_lt]

lemma R_le_base {T t : ℝ} (hT : 10 ^ 13 ≤ T) (hTt : T ≤ t) :
    Rt T ≤ 0.1038 * log t + 0.2573 * log (log t) + 10.2425 := by
  have hT0 : 0 < T := by linarith
  have hl := Real.log_le_log hT0 hTt
  have hlT := log_1e13.trans (Real.log_le_log (by positivity) hT)
  have hll : log (log T) ≤ log (log t) := Real.log_le_log (by linarith) hl
  unfold Rt; linarith

lemma R_sum {T t : ℝ} (hT : 10 ^ 13 ≤ T) (hTt : T ≤ t) : Rt T + Rt t ≤ log t := by
  have h1 := R_le_base hT hTt
  have h2 := R_le_base (hT.trans hTt) le_rfl
  have hl := log_1e13.trans (Real.log_le_log (by positivity) (hT.trans hTt))
  have hll := loglog_le (L := log t) (by linarith)
  linarith

lemma R_le {t : ℝ} (ht : 10 ^ 13 ≤ t) : 2 * Rt t ≤ log t := by
  have := R_sum ht le_rfl; linarith

lemma Mt_eq {x : ℝ} (hx : 0 < x) :
    Mt x = x * (log x - log (2 * π) - 1) / (2 * π) + 7 / 8 := by
  unfold Mt
  rw [Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) (Real.exp_pos 1).ne',
    Real.log_exp]
  ring

/-- `M(t) - M(T) ≤ (t - T)(log t - log 2π)/(2π)`. -/
lemma M_diff {T t : ℝ} (hT : 0 < T) (hTt : T ≤ t) :
    Mt t - Mt T ≤ (t - T) * (log t - log (2 * π)) / (2 * π) := by
  have ht : 0 < t := by linarith
  rw [Mt_eq ht, Mt_eq hT]
  have key : T * (log t - log T) ≤ t - T := by
    rw [← Real.log_div ht.ne' hT.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ht hT)
    calc T * log (t / T) ≤ T * (t / T - 1) := by gcongr
      _ = t - T := by field_simp
  have hπ : 0 < 2 * π := by positivity
  rw [div_add' _ _ _ hπ.ne', div_add' _ _ _ hπ.ne', ← sub_div]
  apply div_le_div_of_nonneg_right _ hπ.le
  nlinarith

/-! ### The kernel `(2 log t - 1)/t³` and the antiderivative -/

/-- `φ(t) = (2 log t - 1)/t³ = -(d/dt)(log t/t²)`. -/
noncomputable def φ (t : ℝ) : ℝ := (2 * log t - 1) / t ^ 3

lemma phi_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ φ t := by
  have : 1 / 2 ≤ log t := by
    have := Real.log_two_gt_d9
    linarith [Real.log_le_log (by norm_num) ht]
  unfold φ; apply div_nonneg (by linarith); positivity

lemma hasDerivAt_F {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => -(log x / x ^ 2)) (φ t) t := by
  have h := ((Real.hasDerivAt_log ht.ne').div (hasDerivAt_pow 2 t)
    (by positivity)).neg
  convert h using 1
  unfold φ; field_simp; ring

lemma tendsto_log_pow_div (n : ℕ) : Tendsto (fun x => log x ^ n / x) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  simpa using this

lemma tendsto_log_pow_div_sq (n : ℕ) : Tendsto (fun x => log x ^ n / x ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div n).mul tendsto_inv_atTop_zero
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

lemma tendsto_F : Tendsto (fun x => -(log x / x ^ 2)) atTop (𝓝 0) := by
  have := (tendsto_log_pow_div_sq 1).neg
  simpa using this

lemma integrableOn_phi {a : ℝ} (ha : 2 ≤ a) : IntegrableOn φ (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg (hasDerivAt_F (by linarith)).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_F (by simp at hx; linarith))
    (fun x hx => phi_nonneg (by simp at hx; linarith)) tendsto_F

/-- `∫_g^∞ (2 log t - 1)/t³ dt = log g/g²`. -/
lemma integral_phi {g : ℝ} (hg : 2 ≤ g) : ∫ t in Ioi g, φ t = log g / g ^ 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (hasDerivAt_F (by linarith)).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_F (by simp at hx; linarith))
    (fun x hx => phi_nonneg (by simp at hx; linarith)) tendsto_F]
  ring

/-- The majorant `h_T(t) = ((t - T)(log t - log 2π)/π + 2 log t) φ(t)`. -/
noncomputable def hf (T t : ℝ) : ℝ := ((t - T) * (log t - log (2 * π)) / π + 2 * log t) * φ t

/-- Its tail integral, `H_T(x) = ∫_x^∞ h_T`. -/
noncomputable def Hf (T x : ℝ) : ℝ :=
  (2 * log x ^ 2 + (3 - 2 * log (2 * π)) * log x + 3 - log (2 * π)) / (π * x)
    - T * (4 * log x ^ 2 + (2 - 4 * log (2 * π)) * log x + 1) / (4 * π * x ^ 2)
    + (2 * log x ^ 2 + log x + 1 / 2) / x ^ 2

lemma hasDerivAt_negHf (T : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => -Hf T y) (hf T x) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have h1 := ((((hl.pow 2).const_mul 2).add (hl.const_mul (3 - 2 * log (2 * π)))).add_const
    (3 - log (2 * π))).div ((hasDerivAt_id x).const_mul π) (by rw [id]; positivity)
  have h2 := ((((hl.pow 2).const_mul 4).add (hl.const_mul (2 - 4 * log (2 * π)))).add_const
    1).const_mul T |>.div ((hasDerivAt_pow 2 x).const_mul (4 * π)) (by positivity)
  have h3 := ((((hl.pow 2).const_mul 2).add hl).add_const (1 / 2)).div (hasDerivAt_pow 2 x)
    (by positivity)
  have h := ((h1.sub h2).add h3).neg
  convert h using 1
  · funext y
    simp only [Hf, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply, id]
    ring
  · unfold hf φ
    simp only [Pi.add_apply, Pi.pow_apply, id, Nat.cast_ofNat]
    field_simp
    ring

lemma tendsto_Hf (T : ℝ) : Tendsto (Hf T) atTop (𝓝 0) := by
  have a2 := tendsto_log_pow_div 2
  have a1 := tendsto_log_pow_div 1
  have a0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have b2 := tendsto_log_pow_div_sq 2
  have b1 := tendsto_log_pow_div_sq 1
  have b0 := tendsto_log_pow_div_sq 0
  have h := ((((a2.const_mul (2 / π)).add (a1.const_mul ((3 - 2 * log (2 * π)) / π))).add
    (a0.const_mul ((3 - log (2 * π)) / π))).sub
    (((b2.const_mul (T / π)).add (b1.const_mul (T * (2 - 4 * log (2 * π)) / (4 * π)))).add
      (b0.const_mul (T / (4 * π))))).add
    (((b2.const_mul 2).add b1).add (b0.const_mul (1 / 2)))
  simp only [mul_zero, add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Hf, pow_one, pow_zero]
  field_simp
  ring

lemma hf_nonneg {T t : ℝ} (hT : 10 ^ 13 ≤ T) (ht : T ≤ t) : 0 ≤ hf T t := by
  have hl := log_1e13.trans (Real.log_le_log (by positivity) (hT.trans ht))
  have hc := c_upper
  unfold hf
  apply mul_nonneg _ (phi_nonneg (by linarith))
  have : 0 ≤ (t - T) * (log t - log (2 * π)) / π :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) Real.pi_pos.le
  linarith

lemma integral_hf {T : ℝ} (hT : 10 ^ 13 ≤ T) :
    IntegrableOn (hf T) (Ioi T) ∧ ∫ t in Ioi T, hf T t = Hf T T := by
  have hT0 : 0 < T := by linarith
  have hc : ContinuousWithinAt (fun y => -Hf T y) (Ici T) T :=
    (hasDerivAt_negHf T hT0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioi T, HasDerivAt (fun y => -Hf T y) (hf T x) x :=
    fun x hx => hasDerivAt_negHf T (by simp at hx; linarith)
  have hp : ∀ x ∈ Ioi T, 0 ≤ hf T x := fun x hx => hf_nonneg hT (le_of_lt hx)
  have hl : Tendsto (fun y => -Hf T y) atTop (𝓝 0) := by
    simpa using (tendsto_Hf T).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hp hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd hp hl]; ring

lemma Hf_bound {T : ℝ} (hT : 10 ^ 13 ≤ T) :
    Hf T T ≤ 1.028 * log T ^ 2 / (π * T) := by
  have hT0 : 0 < T := by linarith
  have hl := log_1e13.trans (Real.log_le_log (by positivity) hT)
  have hs := log_sq_small hT
  have hc1 := c_lower
  have hc2 := c_upper
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  set ℓ := log T
  set c := log (2 * π)
  have e : Hf T T = (ℓ ^ 2 + (5 / 2 - c) * ℓ + 11 / 4 - c) / (π * T)
      + (2 * ℓ ^ 2 + ℓ + 1 / 2) / T ^ 2 := by
    unfold Hf; field_simp; ring
  rw [e]
  have h1 : (2 * ℓ ^ 2 + ℓ + 1 / 2) / T ^ 2 ≤ 1 / (π * T) := by
    have hq : 2 * ℓ ^ 2 + ℓ + 1 / 2 ≤ T / 100 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * ℓ ^ 2 + ℓ + 1 / 2) * (π * T) ≤ T / 100 * (π * T) := by gcongr
    nlinarith
  have h2 : ℓ ^ 2 + (5 / 2 - c) * ℓ + 11 / 4 - c + 1 ≤ 1.028 * ℓ ^ 2 := by nlinarith
  calc (ℓ ^ 2 + (5 / 2 - c) * ℓ + 11 / 4 - c) / (π * T) + (2 * ℓ ^ 2 + ℓ + 1 / 2) / T ^ 2
      ≤ (ℓ ^ 2 + (5 / 2 - c) * ℓ + 11 / 4 - c) / (π * T) + 1 / (π * T) := by linarith
    _ = (ℓ ^ 2 + (5 / 2 - c) * ℓ + 11 / 4 - c + 1) / (π * T) := by ring
    _ ≤ 1.028 * ℓ ^ 2 / (π * T) := by gcongr

/-! ### Lemma 2.6 -/

/-- The first estimate: `Σ_{|γ| ≤ T} log |γ| ≤ T log² T/π`, both signs. -/
lemma part1 {γ : ι → ℝ} (hN : HSWN γ) {T : ℝ} (hT : 10 ^ 13 ≤ T) (s : Finset ι) :
    (∑ i ∈ s.filter (fun i => |γ i| ≤ T), log |γ i|) ≤ T * log T ^ 2 / π := by
  have hT0 : 0 < T := by linarith
  have hl := log_1e13.trans (Real.log_le_log (by positivity) hT)
  have hs := log_sq_small hT
  have hR := R_le hT
  have hc1 := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have hcard := hN.1 T hT s
  have hterm : ∀ i ∈ s.filter (fun i => |γ i| ≤ T), log |γ i| ≤ log T := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases eq_or_lt_of_le (abs_nonneg (γ i)) with h0 | hpos
    · rw [← h0, Real.log_zero]; linarith
    · exact Real.log_le_log hpos hi.2
  calc (∑ i ∈ s.filter (fun i => |γ i| ≤ T), log |γ i|)
      ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T), log T := Finset.sum_le_sum hterm
    _ = ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) * log T := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (Mt T + Rt T) * log T := by gcongr
    _ ≤ T * log T / π * log T := by
        gcongr
        rw [Mt_eq hT0, le_div_iff₀ Real.pi_pos]
        have : T * (log T - log (2 * π) - 1) / (2 * π) * 2 * π = T * (log T - log (2 * π) - 1) := by
          field_simp
        nlinarith
    _ = T * log T ^ 2 / π := by ring

/-- The second estimate: `Σ_{|γ| > T} log |γ|/γ² ≤ 1.028 log² T/(π T)`, both signs. -/
lemma part2 {γ : ι → ℝ} (hN : HSWN γ) {T : ℝ} (hT : 10 ^ 13 ≤ T) (s : Finset ι) :
    (∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), log |γ i| / γ i ^ 2)
      ≤ 1.028 * log T ^ 2 / (π * T) := by
  have hT0 : 0 < T := by linarith
  set S := s.filter (fun i => ¬ |γ i| ≤ T)
  obtain ⟨hhi, hhint⟩ := integral_hf hT
  -- each term as an integral over `(T, ∞)`
  have hterm : ∀ i ∈ S, log |γ i| / γ i ^ 2 =
      ∫ t in Ioi T, (Ioi |γ i|).indicator φ t := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hg : T < |γ i| := lt_of_not_ge hi.2
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hg.le,
      integral_phi (by linarith), sq_abs]
  have hint : ∀ i ∈ S, Integrable (fun t => (Ioi |γ i|).indicator φ t) (volume.restrict (Ioi T)) := by
    intro i _
    exact ((integrableOn_phi (a := T) (by linarith)).indicator measurableSet_Ioi)
  rw [Finset.sum_congr rfl hterm, ← integral_finset_sum S hint]
  refine (setIntegral_mono_on (integrable_finset_sum S hint) hhi measurableSet_Ioi
    fun t ht => ?_).trans (hhint.trans_le (Hf_bound hT))
  have ht' : T < t := ht
  have hφ := phi_nonneg (t := t) (by linarith)
  have e : ∑ i ∈ S, (Ioi |γ i|).indicator φ t = ((S.filter (fun i => |γ i| < t)).card : ℝ) * φ t := by
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
  have hM := M_diff hT0 ht'.le
  have hR := R_sum hT ht'.le
  have hπ := Real.pi_pos
  have hcount : ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤
      (t - T) * (log t - log (2 * π)) / π + 2 * log t := by
    have : 2 * (Mt t - Mt T) ≤ (t - T) * (log t - log (2 * π)) / π := by
      have e2 : (t - T) * (log t - log (2 * π)) / π =
          2 * ((t - T) * (log t - log (2 * π)) / (2 * π)) := by field_simp
      rw [e2]; linarith
    linarith
  unfold hf
  exact mul_le_mul_of_nonneg_right (hc1.trans hcount) hφ

/-- **Chirre-Hagen Lemma 2.6, PROVED CONDITIONAL ON `HSWN`**, the Hasanalizade-Shen-Wong `N(T)` bound. -/
theorem lemma26_of_hsw {γ : ι → ℝ} (hN : HSWN γ) : Lemma26 γ :=
  fun T hT s => ⟨part1 hN hT s, part2 hN hT s⟩

end LeanLab.ChirreHagen2025.Lemma26H

