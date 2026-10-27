module

public import Mathlib
public import LeanLab.ChirreHagen2025.SmoothJ
public import LeanLab.ChirreHagen2025.U1348Abel

/-!
P0075 line, T2, unit U-1348, I-5171, PC run 20261021T0403Z-14344, 2026-10-21.
A better weight for the lab's Section 5 bilinear argument, Bilinear.lean and Bilinear128.lean.
The pairing `A(t) A(x - t) = 0`, `A(t) = θ((1+δ)t) - θ(t)`, is weighted by
`ψ(t) = 11 t/(5 x)` on `[x/64, 5x/11]` and `ψ(t) = 1` on `[5x/11, x/2]`, in place of `2t/x` on
`[x/16, x/2]`; the AM-GM split stays `E(t)²/2 + ψ² E(x - t)²/2`. The weight on `E(u)²` is then `1/2`
up to `6x/11` and `(121/50)(1 - u/x)²` from `6x/11` to `63x/64`, nonincreasing, so Abel summation
against the cumulative bound for `J_θ` applies with 256 scales, U1348Abel.lean. The main term
rises from `0.051928 x³δ²` to `0.0567215 x³δ²` and the Abel constant from `0.2300` to `0.24922`;
the ratio drops from `4.429` to `4.394`. The cross terms use `|θ(u) - u| ≤ u/10^6` for
`u ≥ 10^16`, `ThetaRel6`, proved here from Schoenfeld's Corollary 1 as `ThetaRel` was.
`large_c_u1348` is the analogue of `large_c_of128` for any mean-square constant `c`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.U1348
open Real Chebyshev
open LeanLab.ChirreHagen2025

/-- `|θ(u) - u| ≤ u / 10^6` for `u ≥ 10^16`. -/
def ThetaRel6 : Prop := ∀ u : ℝ, 10 ^ 16 ≤ u → |θ u - u| ≤ u / 10 ^ 6

/-- Schoenfeld 1976, Corollary 1, gives `ThetaRel6`: `√u log² u/(8π) ≤ 5.8·10⁻⁷ u` for
`u ≥ 10^16`. Same proof as `thetaRel_of_schoenfeld`, last constant changed. -/
theorem thetaRel6_of_schoenfeld (h : SchoenfeldTheta) : ThetaRel6 := by
  intro u hu
  have hu0 : 0 < u := by linarith
  refine le_trans (h u (by linarith)) ?_
  set w := √u with hw
  have hw2 : w ^ 2 = u := Real.sq_sqrt hu0.le
  have hw8 : (10 : ℝ) ^ 8 ≤ w := by
    rw [hw, Real.le_sqrt (by positivity) hu0.le]; norm_num at hu ⊢; linarith
  have hw0 : 0 < w := by linarith
  have hlog : Real.log u = 2 * Real.log w := by
    rw [hw, Real.log_sqrt hu0.le]; ring
  have he2 : Real.exp 2 ≤ (10 : ℝ) ^ 8 := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 10 ^ 8 := by norm_num
  have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.mpr he2)
    (Set.mem_Ici.mpr (le_trans he2 hw8)) hw8
  simp only at hanti
  have hs8 : √((10 : ℝ) ^ 8) = 10 ^ 4 := by
    rw [show (10 : ℝ) ^ 8 = (10 ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs8] at hanti
  have hl0 : 0 ≤ Real.log w / √w := div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hb : Real.log w / √w ≤ 19 / 10 ^ 4 :=
    le_trans hanti (div_le_div_of_nonneg_right log_1e8_le (by norm_num))
  have hsq := pow_le_pow_left₀ hl0 hb 2
  rw [div_pow, Real.sq_sqrt hw0.le] at hsq
  have e : √u * Real.log u ^ 2 = 4 * u * (Real.log w ^ 2 / w) := by
    rw [← hw, hlog, ← hw2]; field_simp; ring
  rw [e]
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : 4 * u * (Real.log w ^ 2 / w) ≤ 4 * u * ((19 / 10 ^ 4) ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  nlinarith

/-- The flat cross weight `x - t`. -/
noncomputable def glf (x t : ℝ) : ℝ := x - t

theorem gl_D {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu0 : 0 ≤ u) (hux : u ≤ x) :
    |glf x (u / (1 + δ)) / (1 + δ) - glf x u| ≤ 3 * δ * x := by
  obtain ⟨hp0, hp1, hpd, q1, q2, q3, q4⟩ := p_facts hδ
  set p := 1 / (1 + δ) with hp
  have e : glf x (u / (1 + δ)) / (1 + δ) - glf x u = -(x * (1 - p)) + u * (1 - p ^ 2) := by
    unfold glf; rw [hp]; field_simp; ring
  rw [e]
  have q0 : 0 ≤ 1 - p := by linarith
  have a2 := mul_le_mul hux q2 q1 hx.le
  have a3 := mul_nonneg hu0 q1
  have a5 := mul_le_mul_of_nonneg_left hpd hx.le
  have a6 := mul_nonneg hx.le q0
  rw [abs_le]; constructor <;> nlinarith

theorem gl_abs {x t : ℝ} (hx : 0 < x) (h0 : 0 ≤ t) (h1 : t ≤ x) : |glf x t| ≤ 2 * x := by
  unfold glf; rw [abs_le]; constructor <;> linarith

/-- The bilinear inequality for a general continuous weight `ψ ≥ 0`, integrated over `[α, β]`,
the second cross term and the second square reflected by `u = x - t`. -/
theorem bil_piece {x h δ α β : ℝ} (pw : ℝ → ℝ) (hpc : Continuous pw)
    (hp0 : ∀ t, α ≤ t → t ≤ β → 0 ≤ pw t) (h2α : 2 ≤ α) (hαβ : α ≤ β) (hβx : β ≤ x - 2)
    (hδ : 0 < δ) (hδh : δ * x ≤ h)
    (hno : ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) :
    δ ^ 2 * (∫ t in α..β, pw t * t * (x - t))
      + δ * (∫ t in α..β, pw t * (x - t) * Eθ δ t)
      + δ * (∫ u in x - β..x - α, pw (x - u) * (x - u) * Eθ δ u)
    ≤ (∫ t in α..β, F δ t) / 2 + ∫ u in x - β..x - α, pw (x - u) ^ 2 / 2 * F δ u := by
  have iE : ∀ a b, IntervalIntegrable (Eθ δ) MeasureTheory.volume a b := Eθ_ii hδ
  have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
    fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
  have iEr : IntervalIntegrable (fun t => Eθ δ (x - t)) MeasureTheory.volume α β := by
    have := (iE (x - α) (x - β)).comp_sub_left x
    simpa [sub_sub_cancel] using this
  have iFr : IntervalIntegrable (fun t => F δ (x - t)) MeasureTheory.volume α β := by
    have := (iF (x - β) (x - α) (by linarith) (by linarith)).symm.comp_sub_left x
    simpa [sub_sub_cancel] using this
  have hm : Continuous fun t => pw t * t * (x - t) :=
    (hpc.mul continuous_id).mul (continuous_const.sub continuous_id)
  have hg1 : Continuous fun t => pw t * (x - t) := hpc.mul (continuous_const.sub continuous_id)
  have hg2 : Continuous fun t => pw t * t := hpc.mul continuous_id
  have iM : IntervalIntegrable (fun t => δ ^ 2 * (pw t * t * (x - t))) MeasureTheory.volume α β :=
    (continuous_const.mul hm).intervalIntegrable _ _
  have iL1 : IntervalIntegrable (fun t => δ * (pw t * (x - t)) * Eθ δ t) MeasureTheory.volume α β :=
    (iE _ _).continuousOn_mul (continuous_const.mul hg1).continuousOn
  have iL2 : IntervalIntegrable (fun t => δ * (pw t * t) * Eθ δ (x - t)) MeasureTheory.volume α β :=
    iEr.continuousOn_mul (continuous_const.mul hg2).continuousOn
  have iR1 : IntervalIntegrable (fun t => F δ t / 2) MeasureTheory.volume α β :=
    (iF _ _ (by linarith) hαβ).div_const 2
  have iR2 : IntervalIntegrable (fun t => pw t ^ 2 * F δ (x - t) / 2) MeasureTheory.volume α β :=
    (iFr.continuousOn_mul (hpc.pow 2).continuousOn).div_const 2
  have hint : (∫ t in α..β, (δ ^ 2 * (pw t * t * (x - t)) + δ * (pw t * (x - t)) * Eθ δ t
        + δ * (pw t * t) * Eθ δ (x - t)))
      ≤ ∫ t in α..β, (F δ t / 2 + pw t ^ 2 * F δ (x - t) / 2) := by
    apply intervalIntegral.integral_mono_on hαβ
    · exact (iM.add iL1).add iL2
    · exact iR1.add iR2
    · intro t ht
      have h0 := hp0 t ht.1 ht.2
      have := pointwise_bil (t := t) hδ hδh (by linarith [ht.1]) (by linarith [ht.2]) hno (pw t) h0
      rw [F_eq_Eθ, F_eq_Eθ]
      linarith [this]
  have sL := intervalIntegral.integral_add (iM.add iL1) iL2
  have sL' := intervalIntegral.integral_add iM iL1
  have sR := intervalIntegral.integral_add iR1 iR2
  rw [sL, sL', sR] at hint
  have h1 : (∫ t in α..β, δ ^ 2 * (pw t * t * (x - t)))
      = δ ^ 2 * ∫ t in α..β, pw t * t * (x - t) := intervalIntegral.integral_const_mul _ _
  have h2 : (∫ t in α..β, δ * (pw t * (x - t)) * Eθ δ t)
      = δ * ∫ t in α..β, pw t * (x - t) * Eθ δ t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by first | ring | (beta_reduce; ring))
  have h3 : (∫ t in α..β, δ * (pw t * t) * Eθ δ (x - t))
      = δ * ∫ u in x - β..x - α, pw (x - u) * (x - u) * Eθ δ u := by
    rw [← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_sub_left
      (fun u => δ * (pw (x - u) * (x - u) * Eθ δ u)) x (a := α) (b := β)
    rw [← this]
    exact intervalIntegral.integral_congr (fun t _ => by simp only [sub_sub_cancel]; ring)
  have h4 : (∫ t in α..β, F δ t / 2) = (∫ t in α..β, F δ t) / 2 :=
    intervalIntegral.integral_div _ _
  have h5 : (∫ t in α..β, pw t ^ 2 * F δ (x - t) / 2)
      = ∫ u in x - β..x - α, pw (x - u) ^ 2 / 2 * F δ u := by
    have := intervalIntegral.integral_comp_sub_left
      (fun u => pw (x - u) ^ 2 / 2 * F δ u) x (a := α) (b := β)
    rw [← this]
    exact intervalIntegral.integral_congr (fun t _ => by simp only [sub_sub_cancel]; ring)
  rw [h1, h2, h3, h4, h5] at hint
  exact hint

/-- The right side is at most the Abel sum over the 256 scales of U1348Abel.lean. -/
theorem rhs_le_abel_u1348 {x δ : ℝ} (hx : 64 ≤ x) (hδ : 0 < δ) :
    (∫ t in x / 64..5 * x / 11, F δ t) / 2 + (∫ t in 5 * x / 11..x / 2, F δ t) / 2
      + (∫ u in x / 2..6 * x / 11, 1 / 2 * F δ u)
      + ∫ u in 6 * x / 11..63 * x / 64, 121 / 50 * ((x - u) / x) ^ 2 * F δ u
      ≤ abelSum wc (Gs δ x sc) 256 := by
  have hxpos : 0 < x := by linarith
  have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
    fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
  have hsb : ∀ j, 0 ≤ sc j * x := fun j => by nlinarith [(sc_bounds j).1]
  have hsj : ∀ j, sc j * x ≤ sc (j + 1) * x := fun j => by
    nlinarith [sc_mono (Nat.le_succ j)]
  have hcw : Continuous fun u : ℝ => 121 / 50 * ((x - u) / x) ^ 2 := by fun_prop
  have iW : ∀ j, IntervalIntegrable (fun u => 121 / 50 * ((x - u) / x) ^ 2 * F δ u)
      MeasureTheory.volume (sc j * x) (sc (j + 1) * x) := fun j =>
    (iF _ _ (hsb j) (hsj j)).continuousOn_mul hcw.continuousOn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j => sc j * x)
    (f := fun u => 121 / 50 * ((x - u) / x) ^ 2 * F δ u) (n := 256) (fun j _ => iW j)
  have e0 : sc 0 * x = 6 * x / 11 := by rw [sc_zero]; ring
  have e256 : sc 256 * x = 63 * x / 64 := by rw [sc_top]; ring
  simp only [e0, e256] at hsum
  have hpieces : (∫ u in 6 * x / 11..63 * x / 64, 121 / 50 * ((x - u) / x) ^ 2 * F δ u)
      ≤ ∑ j ∈ Finset.range 256, wc j * (Gs δ x sc (j + 1) - Gs δ x sc j) := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro j _
    have hb := sc_bounds j
    have hb1 := sc_bounds (j + 1)
    have hG : Gs δ x sc (j + 1) - Gs δ x sc j = ∫ u in sc j * x..sc (j + 1) * x, F δ u := by
      unfold Gs
      exact intervalIntegral.integral_interval_sub_left (iF 1 _ zero_le_one (by nlinarith))
        (iF 1 _ zero_le_one (by nlinarith))
    rw [hG, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hsj j) (iW j) ((iF _ _ (hsb j) (hsj j)).const_mul _)
    intro u hu
    have hF0 : 0 ≤ F δ u := sq_nonneg _
    have h1 : (x - u) / x ≤ 1 - sc j := by
      rw [div_le_iff₀ hxpos]; nlinarith [hu.1]
    have h0 : 0 ≤ (x - u) / x := div_nonneg (by nlinarith [hu.2]) hxpos.le
    have : ((x - u) / x) ^ 2 ≤ (1 - sc j) ^ 2 := pow_le_pow_left₀ h0 h1 2
    unfold wc
    nlinarith
  have hR1 : (∫ t in x / 64..5 * x / 11, F δ t) / 2 + (∫ t in 5 * x / 11..x / 2, F δ t) / 2
      + (∫ u in x / 2..6 * x / 11, 1 / 2 * F δ u) ≤ wc 0 * Gs δ x sc 0 := by
    rw [wc_zero]; unfold Gs; rw [e0, intervalIntegral.integral_const_mul]
    have s1 := intervalIntegral.integral_add_adjacent_intervals
      (iF 1 (x / 64) zero_le_one (by linarith)) (iF (x / 64) (5 * x / 11) (by positivity) (by linarith))
    have s2 := intervalIntegral.integral_add_adjacent_intervals
      (iF 1 (5 * x / 11) zero_le_one (by linarith)) (iF (5 * x / 11) (x / 2) (by positivity) (by linarith))
    have s3 := intervalIntegral.integral_add_adjacent_intervals
      (iF 1 (x / 2) zero_le_one (by linarith)) (iF (x / 2) (6 * x / 11) (by positivity) (by linarith))
    have h0 : 0 ≤ ∫ y in (1 : ℝ)..x / 64, F δ y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => sq_nonneg _)
    linarith
  unfold abelSum
  linarith

set_option maxHeartbeats 4000000 in
/-- The new bilinear argument with any mean-square constant `c` at the scales `x/2 ≤ X ≤ x`. -/
theorem large_c_u1348 {c H : ℝ} (hc0 : 0 ≤ c) (hH1 : 1 / 10 ≤ H) (hH : H ≤ 61.5)
    (hHc : c * 0.24922 < H * ((11 / 5 * (((5 / 11) ^ 3 - (1 / 64) ^ 3) / 3
        - ((5 / 11) ^ 4 - (1 / 64) ^ 4) / 4)
      + (((1 / 2) ^ 2 - (5 / 11) ^ 2) / 2 - ((1 / 2) ^ 3 - (5 / 11) ^ 3) / 3))
      - (11 / 10 * (10 * (5 / 11 - 1 / 64) + 2 * (5 / 11) + 2 * (1 / 64))
        + (3 * (1 / 2 - 5 / 11) + 2 * (1 / 2) + 2 * (5 / 11))
        + 11 / 10 * (16 * (63 / 64 - 6 / 11) + 2 * (63 / 64) + 2 * (6 / 11))
        + (3 * (6 / 11 - 1 / 2) + 2 * (6 / 11) + 2 * (1 / 2))) / 10 ^ 6))
    (hT : ThetaRel6) (x : ℝ) (hx : 1.1 * 10 ^ 18 ≤ x)
    (hJ : ∀ X : ℝ, x / 2 ≤ X → X ≤ x → Jtheta X (H * Real.log x ^ 2 / x)
      ≤ c * (H * Real.log x ^ 2 / x) * Real.log (2.0001 / (H * Real.log x ^ 2 / x)) ^ 2 * X ^ 2) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + H * Real.log x ^ 2 := by
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := H * Real.log x ^ 2 with hh
  have hδpos : 0 < h / x := div_pos (mul_pos (by linarith) (by positivity)) hxpos
  have hδle : h / x ≤ 1 / 10 ^ 13 := by
    have := threshold2 hx
    have : h / x ≤ 61.5 * Real.log x ^ 2 / x := by
      rw [hh]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
    linarith
  have hδx : h / x * x = h := by field_simp
  set δ := h / x with hδ
  -- the two pieces
  have P1 := bil_piece (x := x) (h := h) (δ := δ) (α := x / 64) (β := 5 * x / 11)
    (fun t => 11 / 5 * t / x) (by fun_prop)
    (fun t h1 _ => div_nonneg (by linarith) hxpos.le) (by linarith) (by linarith) (by linarith)
    hδpos hδx.le hno
  have P2 := bil_piece (x := x) (h := h) (δ := δ) (α := 5 * x / 11) (β := x / 2)
    (fun _ => 1) continuous_const (fun _ _ _ => zero_le_one) (by linarith) (by linarith)
    (by linarith) hδpos hδx.le hno
  beta_reduce at P1 P2
  have ea : x - 5 * x / 11 = 6 * x / 11 := by ring
  have eb : x - x / 64 = 63 * x / 64 := by ring
  have ec' : x - x / 2 = x / 2 := by ring
  rw [ea, eb] at P1
  rw [ec', ea] at P2
  -- main terms
  have M1 : (∫ t in x / 64..5 * x / 11, 11 / 5 * t / x * t * (x - t))
      = x ^ 3 * (11 / 5 * (((5 / 11) ^ 3 - (1 / 64) ^ 3) / 3 - ((5 / 11) ^ 4 - (1 / 64) ^ 4) / 4)) := by
    have e : (∫ t in x / 64..5 * x / 11, 11 / 5 * t / x * t * (x - t))
        = ∫ t in x / 64..5 * x / 11, (11 / 5 * t ^ 2 - 11 / (5 * x) * t ^ 3) :=
      intervalIntegral.integral_congr (fun t _ => by field_simp; try ring)
    rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    push_cast
    field_simp
    ring
  have M2 : (∫ t in 5 * x / 11..x / 2, 1 * t * (x - t))
      = x ^ 3 * (((1 / 2) ^ 2 - (5 / 11) ^ 2) / 2 - ((1 / 2) ^ 3 - (5 / 11) ^ 3) / 3) := by
    have e : (∫ t in 5 * x / 11..x / 2, 1 * t * (x - t))
        = ∫ t in 5 * x / 11..x / 2, (x * t ^ 1 - t ^ 2) :=
      intervalIntegral.integral_congr (fun t _ => by first | ring | (beta_reduce; ring))
    rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    push_cast
    ring
  -- cross terms as multiples of the lab's g1f, g2f and of glf
  have C1 : (∫ t in x / 64..5 * x / 11, 11 / 5 * t / x * (x - t) * Eθ δ t)
      = 11 / 10 * ∫ t in x / 64..5 * x / 11, g1f x t * Eθ δ t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by first | (unfold g1f; ring) | (beta_reduce; unfold g1f; ring))
  have C3 : (∫ u in 6 * x / 11..63 * x / 64, 11 / 5 * (x - u) / x * (x - u) * Eθ δ u)
      = 11 / 10 * ∫ u in 6 * x / 11..63 * x / 64, g2f x u * Eθ δ u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by first | (unfold g2f; ring) | (beta_reduce; unfold g2f; ring))
  have C2 : (∫ t in 5 * x / 11..x / 2, 1 * (x - t) * Eθ δ t)
      = ∫ t in 5 * x / 11..x / 2, glf x t * Eθ δ t :=
    intervalIntegral.integral_congr (fun t _ => by first | (unfold glf; ring) | (beta_reduce; unfold glf; ring))
  have C4 : (∫ u in x / 2..6 * x / 11, 1 * (x - u) * Eθ δ u)
      = ∫ u in x / 2..6 * x / 11, glf x u * Eθ δ u :=
    intervalIntegral.integral_congr (fun t _ => by first | (unfold glf; ring) | (beta_reduce; unfold glf; ring))
  have W1 : (∫ u in 6 * x / 11..63 * x / 64, (11 / 5 * (x - u) / x) ^ 2 / 2 * F δ u)
      = ∫ u in 6 * x / 11..63 * x / 64, 121 / 50 * ((x - u) / x) ^ 2 * F δ u :=
    intervalIntegral.integral_congr (fun t _ => by first | ring | (beta_reduce; ring))
  have W2 : (∫ u in x / 2..6 * x / 11, (1 : ℝ) ^ 2 / 2 * F δ u)
      = ∫ u in x / 2..6 * x / 11, 1 / 2 * F δ u :=
    intervalIntegral.integral_congr (fun t _ => by first | ring | (beta_reduce; ring))
  rw [M1, C1, C3, W1] at P1
  rw [M2, C2, C4, W2] at P2
  have hrhs := rhs_le_abel_u1348 (x := x) (by linarith) hδpos
  -- Abel summation against the J bound
  set K := c * δ * Real.log (2.0001 / δ) ^ 2 with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hc0 hδpos.le) (sq_nonneg _)
  have hGB : ∀ j, Gs δ x sc j ≤ x ^ 2 * K * sc j ^ 2 := by
    intro j
    have hb := sc_bounds j
    have := hJ (sc j * x) (by nlinarith) (by nlinarith)
    have e : Jtheta (sc j * x) δ = Gs δ x sc j := rfl
    rw [e] at this
    calc Gs δ x sc j ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * (sc j * x) ^ 2 := this
      _ = x ^ 2 * K * sc j ^ 2 := by rw [hK]; ring
  have hup := abelSum_mono wc (Gs δ x sc) (fun j => x ^ 2 * K * sc j ^ 2)
    wc_antitone wc_nonneg hGB 256
  have hfac : abelSum wc (fun j => x ^ 2 * K * sc j ^ 2) 256
      = x ^ 2 * K * abelSum wc (fun j => sc j ^ 2) 256 := by
    simp only [abelSum]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac] at hup
  have hxK : 0 ≤ x ^ 2 * K := mul_nonneg (by positivity) hK0
  have hup2 : abelSum wc (Gs δ x sc) 256 ≤ x ^ 2 * K * 0.24922 := by
    have := mul_le_mul_of_nonneg_left Uc_lt.le hxK
    linarith
  -- cross bounds
  have hδ1 : δ ≤ 1 / 10 ^ 13 := hδle
  have hρ : ∀ u, x / 64 ≤ u → u ≤ x → |Rθ u| ≤ x / 10 ^ 6 := by
    intro u h1 h2
    have := hT u (by linarith)
    unfold Rθ
    linarith [div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 10 ^ 6)]
  have hc1 := cross_bound (g := g1f x) (by unfold g1f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 64) (by nlinarith : (1 + δ) * (x / 64) ≤ 5 * x / 11)
    (fun u h1 h2 => hρ u h1 (by nlinarith)) (D := 10 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g1_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g1_abs hxpos (by linarith) (by nlinarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g1f x)
      (fun t ht0 ht1 => g1_abs hxpos ht0 ht1))
  have hc3 := cross_bound (g := g2f x) (by unfold g2f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < 6 * x / 11) (by nlinarith : (1 + δ) * (6 * x / 11) ≤ 63 * x / 64)
    (fun u h1 h2 => hρ u (by linarith) (by nlinarith)) (D := 16 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g2_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g2_abs hxpos (by linarith) (by nlinarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g2f x)
      (fun t ht0 ht1 => g2_abs hxpos ht0 ht1))
  have hc2 := cross_bound (g := glf x) (by unfold glf; fun_prop) hδpos
    (by positivity : (0 : ℝ) < 5 * x / 11) (by nlinarith : (1 + δ) * (5 * x / 11) ≤ x / 2)
    (fun u h1 h2 => hρ u (by linarith) (by nlinarith)) (D := 3 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => gl_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => gl_abs hxpos (by linarith) (by nlinarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (glf x)
      (fun t ht0 ht1 => gl_abs hxpos ht0 ht1))
  have hc4 := cross_bound (g := glf x) (by unfold glf; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 2) (by nlinarith : (1 + δ) * (x / 2) ≤ 6 * x / 11)
    (fun u h1 h2 => hρ u (by linarith) (by nlinarith)) (D := 3 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => gl_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => gl_abs hxpos (by linarith) (by nlinarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (glf x)
      (fun t ht0 ht1 => gl_abs hxpos ht0 ht1))
  have a1 := neg_abs_le (∫ t in x / 64..5 * x / 11, g1f x t * Eθ δ t)
  have a3 := neg_abs_le (∫ u in 6 * x / 11..63 * x / 64, g2f x u * Eθ δ u)
  have a2 := neg_abs_le (∫ t in 5 * x / 11..x / 2, glf x t * Eθ δ t)
  have a4 := neg_abs_le (∫ u in x / 2..6 * x / 11, glf x u * Eθ δ u)
  have hδ0 : 0 ≤ δ := hδpos.le
  have b1 := mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ δ * (11 / 10))
  have b3 := mul_le_mul_of_nonneg_left hc3 (by positivity : (0 : ℝ) ≤ δ * (11 / 10))
  have b2 := mul_le_mul_of_nonneg_left hc2 hδ0
  have b4 := mul_le_mul_of_nonneg_left hc4 hδ0
  have c1 := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ δ * (11 / 10))
  have c3 := mul_le_mul_of_nonneg_left a3 (by positivity : (0 : ℝ) ≤ δ * (11 / 10))
  have c2 := mul_le_mul_of_nonneg_left a2 hδ0
  have c4 := mul_le_mul_of_nonneg_left a4 hδ0
  -- numerics, everything divided by δ x²
  set L := Real.log x with hLdef
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; nlinarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, hh, div_div_eq_mul_div, div_le_iff₀ (mul_pos (by linarith) (by positivity))]
    have : (2.0001 : ℝ) ≤ H * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hdx : δ * x = H * L ^ 2 := by rw [hδ, hh]; field_simp
  have hD : 0 < δ * x ^ 2 := mul_pos hδpos (by positivity)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 11 / 5 * (((5 / 11 : ℝ) ^ 3 - (1 / 64) ^ 3) / 3 - ((5 / 11) ^ 4 - (1 / 64) ^ 4) / 4)
      + (((1 / 2 : ℝ) ^ 2 - (5 / 11) ^ 2) / 2 - ((1 / 2) ^ 3 - (5 / 11) ^ 3) / 3) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (11 / 10 * (10 * (5 / 11 - 1 / 64) + 2 * (5 / 11) + 2 * (1 / 64))
        + (3 * (1 / 2 - 5 / 11) + 2 * (1 / 2) + 2 * (5 / 11))
        + 11 / 10 * (16 * (63 / 64 - 6 / 11) + 2 * (63 / 64) + 2 * (6 / 11))
        + (3 * (6 / 11 - 1 / 2) + 2 * (6 / 11) + 2 * (1 / 2))) / (10 : ℝ) ^ 6 := ⟨_, rfl⟩
  have em : δ ^ 2 * (x ^ 3 * (11 / 5 * (((5 / 11) ^ 3 - (1 / 64) ^ 3) / 3
        - ((5 / 11) ^ 4 - (1 / 64) ^ 4) / 4)))
      + δ ^ 2 * (x ^ 3 * (((1 / 2) ^ 2 - (5 / 11) ^ 2) / 2 - ((1 / 2) ^ 3 - (5 / 11) ^ 3) / 3))
      = (δ * x ^ 2) * (δ * x * m) := by rw [hm]; ring
  have ec : δ * (11 / 10) * (10 * δ * x * (x / 10 ^ 6) * (5 * x / 11 - x / 64)
        + 2 * x * (x / 10 ^ 6) * (δ * (5 * x / 11)) + 2 * x * (x / 10 ^ 6) * (δ * (x / 64)))
      + δ * (11 / 10) * (16 * δ * x * (x / 10 ^ 6) * (63 * x / 64 - 6 * x / 11)
        + 2 * x * (x / 10 ^ 6) * (δ * (63 * x / 64)) + 2 * x * (x / 10 ^ 6) * (δ * (6 * x / 11)))
      + δ * (3 * δ * x * (x / 10 ^ 6) * (x / 2 - 5 * x / 11)
        + 2 * x * (x / 10 ^ 6) * (δ * (x / 2)) + 2 * x * (x / 10 ^ 6) * (δ * (5 * x / 11)))
      + δ * (3 * δ * x * (x / 10 ^ 6) * (6 * x / 11 - x / 2)
        + 2 * x * (x / 10 ^ 6) * (δ * (6 * x / 11)) + 2 * x * (x / 10 ^ 6) * (δ * (x / 2)))
      = (δ * x ^ 2) * (δ * x * κ) := by rw [hκ]; ring
  have hKx : x ^ 2 * K * 0.24922 = (δ * x ^ 2) * (c * 0.24922 * u ^ 2) := by rw [hK]; ring
  have key : (δ * x ^ 2) * (δ * x * m) ≤ (δ * x ^ 2) * (c * 0.24922 * u ^ 2 + δ * x * κ) := by
    rw [mul_add, ← em, ← hKx, ← ec]
    linarith only [P1, P2, hrhs, hup2, b1, b2, b3, b4, c1, c2, c3, c4]
  have k2 := le_of_mul_le_mul_left key hD
  rw [hdx] at k2
  have hL2 : 0 < L ^ 2 := by positivity
  have hfin : c * 0.24922 * u ^ 2 ≤ c * 0.24922 * L ^ 2 :=
    mul_le_mul_of_nonneg_left hu2 (mul_nonneg hc0 (by norm_num))
  have hHc' : c * 0.24922 < H * (m - κ) := by rw [hm, hκ]; exact hHc
  nlinarith [k2, hfin, hL2, hHc']

end LeanLab.ChirreHagen2025.U1348
