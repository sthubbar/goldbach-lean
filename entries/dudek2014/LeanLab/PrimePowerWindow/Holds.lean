module

public import Mathlib
public import LeanLab.PrimePowerWindow.Window

/-!
I-5230, unit U-6601, CLOUD 20261020T1618Z-cloud46: `window_holds`, Dudek's Schoenfeld step
PROVED with no cited input, by the prime power count of `Window.lean` and a polynomial
inequality in `u = x^{1/6}`, for every `x ≥ 65000`.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.PrimePowerWindow
open Real Finset
open LeanLab.Dudek2014.Section22

/-- The sixth root `u = x^{1/6}` and its powers. -/
theorem sixth_root {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 6 : ℝ)) ^ 6 = x ∧ √x = (x ^ (1 / 6 : ℝ)) ^ 3 ∧
      x ^ (1 / 3 : ℝ) = (x ^ (1 / 6 : ℝ)) ^ 2 := by
  have hpow : ∀ n : ℕ, (x ^ (1 / 6 : ℝ)) ^ n = x ^ ((n : ℝ) / 6) := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; ring_nf
  refine ⟨?_, ?_, ?_⟩
  · rw [hpow]; norm_num
  · rw [hpow, Real.sqrt_eq_rpow]; norm_num
  · rw [hpow]; norm_num

/-- `log x ≤ 1.5 u + 2.32` with `u = x^{1/6}`. -/
theorem log_le_u {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 1.5 * x ^ (1 / 6 : ℝ) + 2.32 := by
  set u := x ^ (1 / 6 : ℝ) with hu
  obtain ⟨h6, -, -⟩ := sixth_root hx.le
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx _
  have hlx : Real.log x = 6 * Real.log u := by
    rw [← h6, Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos (show 0 < u / 4 by positivity)
  rw [Real.log_div hu0.ne' (by norm_num)] at h1
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9
  rw [hlx]
  nlinarith

/-- All the size facts at `x ≥ 65000`. -/
theorem facts {x : ℝ} (hx : 65000 ≤ x) :
    let u := x ^ (1 / 6 : ℝ)
    6.34 ≤ u ∧ u ^ 6 = x ∧ √x = u ^ 3 ∧ x ^ (1 / 3 : ℝ) = u ^ 2 ∧
      Real.log x ≤ 1.5 * u + 2.32 ∧ 11 ≤ Real.log x ∧
      0 ≤ hD x ∧ hD x ≤ 0.63662 * u ^ 3 * Real.log x := by
  intro u
  have hx0 : 0 < x := by linarith
  obtain ⟨h6, hs, h3⟩ := sixth_root hx0.le
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx0.le _
  have hu : 6.34 ≤ u := by
    by_contra hlt
    push Not at hlt
    have : u ^ 6 < (6.34 : ℝ) ^ 6 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
    have h6' : u ^ 6 = x := h6
    rw [h6'] at this; norm_num at this; linarith
  have hL : 11 ≤ Real.log x := le_trans (by linarith [log_65000]) (Real.log_le_log (by norm_num) hx)
  obtain ⟨hpi1, hpi2⟩ := pi_bounds
  refine ⟨hu, h6, hs, h3, log_le_u hx0, hL, hD_nonneg (by linarith), ?_⟩
  unfold hD
  rw [hs]
  have : 0 ≤ u ^ 3 * Real.log x := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Dudek's Schoenfeld step, PROVED with no cited input.** -/
theorem window_holds : SchoenfeldWindow := by
  intro x hx
  obtain ⟨hu, h6, hs, h3, hLu, hL11, hh0, hhu⟩ := facts hx
  set u := x ^ (1 / 6 : ℝ) with hudef
  set h := hD x with hhdef
  set L := Real.log x with hLdef
  set a := x - h with ha
  set b := x + h with hb
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  -- h ≤ x / 10
  have hh10 : h ≤ x / 10 := by
    rw [← h6]
    have h1 : 0.63662 * u ^ 3 * L ≤ 0.63662 * u ^ 3 * (1.5 * u + 2.32) :=
      mul_le_mul_of_nonneg_left hLu (by positivity)
    have hu2 : 40.1956 ≤ u ^ 2 := by nlinarith
    have hq : 0 ≤ 0.1 * u ^ 3 - 0.955 * u - 1.477 := by
      have : 40.1956 * u ≤ u ^ 2 * u := mul_le_mul_of_nonneg_right hu2 hu0.le
      have e : u ^ 2 * u = u ^ 3 := by ring
      nlinarith
    have h2 : 0 ≤ u ^ 3 * (0.1 * u ^ 3 - 0.955 * u - 1.477) := mul_nonneg (by positivity) hq
    have e : u ^ 6 / 10 - 0.63662 * u ^ 3 * (1.5 * u + 2.32) =
        u ^ 3 * (0.1 * u ^ 3 - 0.95493 * u - 1.4769584) := by ring
    have h3 : u ^ 3 * (0.1 * u ^ 3 - 0.955 * u - 1.477) ≤
        u ^ 3 * (0.1 * u ^ 3 - 0.95493 * u - 1.4769584) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have ha9 : 0.9 * x ≤ a := by linarith
  have hb11 : b ≤ 1.1 * x := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hab : a ≤ b := by linarith
  -- square roots
  have hsa_le : √a ≤ u ^ 3 := by rw [← hs]; exact Real.sqrt_le_sqrt (by linarith)
  have hsb_ge : u ^ 3 ≤ √b := by rw [← hs]; exact Real.sqrt_le_sqrt (by linarith)
  have hsa_ge : 0.948 * u ^ 3 ≤ √a := by
    apply Real.le_sqrt_of_sq_le
    have : (0.948 * u ^ 3) ^ 2 = 0.898704 * u ^ 6 := by ring
    rw [this, h6]; linarith
  have hsqa := Real.sq_sqrt (show 0 ≤ a by linarith)
  have hsqb := Real.sq_sqrt (show 0 ≤ b by linarith)
  -- √b - √a ≤ 0.6716 L
  have hdiff : √b - √a ≤ 0.6716 * L := by
    have hprod : (√b - √a) * (√b + √a) = 2 * h := by nlinarith
    have hpos : 0 ≤ √b - √a := by linarith
    have h1 : (√b - √a) * (2 * (0.948 * u ^ 3)) ≤ 2 * h := by
      rw [← hprod]; apply mul_le_mul_of_nonneg_left _ hpos; linarith
    have h2 : (√b - √a) * (1.896 * u ^ 3) ≤ 2 * (0.63662 * u ^ 3 * L) := by nlinarith
    have hu3 : 0 < u ^ 3 := by positivity
    have h3' : ((√b - √a) * 1.896 - 1.27324 * L) * u ^ 3 ≤ 0 := by nlinarith
    have := nonpos_of_mul_nonpos_left h3' hu3
    nlinarith
  -- cube roots
  have hcb : u ^ 2 ≤ b ^ (1 / 3 : ℝ) := by
    rw [← h3]; exact Real.rpow_le_rpow hx0.le (by linarith) (by norm_num)
  set w := a ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by linarith) _
  have hw3 : w ^ 3 = a := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hwu : 0.965 * u ^ 2 ≤ w := by
    by_contra hlt
    push Not at hlt
    have : w ^ 3 < (0.965 * u ^ 2) ^ 3 := pow_lt_pow_left₀ hlt hw0 (by norm_num)
    rw [hw3] at this
    have e : (0.965 * u ^ 2) ^ 3 = 0.898632125 * u ^ 6 := by ring
    rw [e, h6] at this; linarith
  have hstep : b ^ (1 / 3 : ℝ) < a ^ (1 / 3 : ℝ) + 1 := by
    rw [← hw]
    have hbw : b < (w + 1) ^ 3 := by
      have hw2 : 0.931225 * u ^ 4 ≤ w ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hwu 2
        have e : (0.965 * u ^ 2) ^ 2 = 0.931225 * u ^ 4 := by ring
        linarith
      have h2h : 2 * h ≤ 1.27324 * u ^ 3 * (1.5 * u + 2.32) := by
        have : 0.63662 * u ^ 3 * L ≤ 0.63662 * u ^ 3 * (1.5 * u + 2.32) :=
          mul_le_mul_of_nonneg_left hLu (by positivity)
        linarith
      have hu3 : 0 < u ^ 3 := by positivity
      have hpoly : 1.27324 * u ^ 3 * (1.5 * u + 2.32) < 3 * (0.931225 * u ^ 4) := by
        have h1 : 0 < u ^ 3 * (0.883815 * u - 2.9539168) := mul_pos hu3 (by linarith)
        have e : 3 * (0.931225 * u ^ 4) - 1.27324 * u ^ 3 * (1.5 * u + 2.32) =
            u ^ 3 * (0.883815 * u - 2.9539168) := by ring
        linarith
      have e : (w + 1) ^ 3 = w ^ 3 + 3 * w ^ 2 + 3 * w + 1 := by ring
      rw [e, hw3]
      have hba : b = a + 2 * h := by rw [hb, ha]; ring
      rw [hba]
      linarith
    have hb0 : 0 ≤ b := by linarith
    calc b ^ (1 / 3 : ℝ) < ((w + 1) ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_lt_rpow hb0 hbw (by norm_num)
      _ = w + 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  -- the mass bound
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  rw [diff_eq hfl]
  refine lt_of_le_of_lt (mass_le ha1 hab hstep) ?_
  -- logs
  have hlb : Real.log b ≤ L + 0.1 := by
    have h1 : Real.log b ≤ Real.log (1.1 * x) := Real.log_le_log (by linarith) hb11
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.1 by norm_num)
    linarith
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  set M := Real.log b with hM
  have hM2 : M / Real.log 2 * (M / 3) ≤ M ^ 2 / 2.0794 := by
    rw [div_mul_div_comm, ← sq]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
  have hM1 : M / 2 * (√b - √a + 1) ≤ M / 2 * (0.6716 * L + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hRHS : 0.13 * u ^ 3 + 3 * u ^ 2 ≤
      1.11 * √b + 3 * b ^ (1 / 3 : ℝ) - 0.98 * √a := by nlinarith
  have hML : M ≤ 1.5 * u + 2.42 := by linarith
  have hLM : L ≤ M := Real.log_le_log hx0 (by linarith)
  have hpoly : M / 2 * (0.6716 * L + 1) + M ^ 2 / 2.0794 < 0.13 * u ^ 3 + 3 * u ^ 2 := by
    have h1 : M / 2 * (0.6716 * L + 1) ≤ M / 2 * (0.6716 * M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : M ^ 2 / 2.0794 ≤ 0.4810 * M ^ 2 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg M]
    have hMsq : M ^ 2 ≤ (1.5 * u + 2.42) ^ 2 := pow_le_pow_left₀ hlb0 hML 2
    have e1 : M / 2 * (0.6716 * M + 1) = 0.3358 * M ^ 2 + 0.5 * M := by ring
    have e2 : (1.5 * u + 2.42) ^ 2 = 2.25 * u ^ 2 + 7.26 * u + 5.8564 := by ring
    have hu2 : 6.34 * u ≤ u ^ 2 := by nlinarith
    have hu2' : 40.1956 ≤ u ^ 2 := by nlinarith
    have hu3 : 40.1956 * u ≤ u ^ 3 := by
      have := mul_le_mul_of_nonneg_right hu2' hu0.le
      have e : u ^ 2 * u = u ^ 3 := by ring
      linarith
    linarith
  linarith

end LeanLab.PrimePowerWindow

