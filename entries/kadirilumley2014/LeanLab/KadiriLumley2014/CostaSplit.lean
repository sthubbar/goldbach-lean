module

public import LeanLab.KadiriLumley2014.CostaTransfer
public import LeanLab.Common.PsiTheta.Bound
public import LeanLab.ChebyshevExplicit.Psi30

/-!
# Costa Pereira 1985 Theorem 5 from an explicit theta bound

Kadiri and Lumley 2014, arXiv 1407.7902v1, page 3, Lemma 2.1, equation 2.9, cites
Costa Pereira 1985 Theorem 5: for `x ≥ e^38`,
`0.999 √x + x^{1/3} < ψ(x) - θ(x) < 1.001 √x + x^{1/3}`.
The lab states it as the cited Prop `LeanLab.KadiriLumley2014.Task64.CostaEstimate`.

This file derives it from one explicit theta bound at `√x`, Dusart 2010 Theorem 5.2 row
`k = 2`, `η_2 = 0.05`, `x_2 = 122568683`, taken as the hypothesis `hD` of `costa_of_dusart`, together with
Mathlib's Costa Pereira type inequalities for `ψ - θ` and the lab's proved Chebyshev bounds.

AI wrote this Lean code, Claude, 2026-11-22. Checked only by the Lean kernel.
Binary Goldbach is open; nothing here bears on it directly.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.CostaSplit

open Real Chebyshev
open LeanLab.KadiriLumley2014.Task64 (CostaEstimate)

/-- `23^12 ≤ e^38`. -/
lemma exp38_ge : (23 : ℝ) ^ 12 ≤ Real.exp 38 := by
  have he : Real.exp 38 = Real.exp 1 ^ 38 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 : (2.718 : ℝ) ^ 38 ≤ Real.exp 1 ^ 38 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 38
  rw [he]
  refine le_trans ?_ h1
  norm_num

/-- The explicit theta bound in the form used below: `|θ(s) - s| ≤ s / 7220` once
`s ≥ 122568683` and `log s ≥ 19`. -/
lemma theta_close
    (hD : ∀ t : ℝ, 122568683 ≤ t → |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2)
    {s : ℝ} (hs : 122568683 ≤ s) (hl : 19 ≤ Real.log s) :
    |θ s - s| ≤ s / 7220 := by
  have h := hD s hs
  have hs0 : 0 ≤ s := by linarith
  have hl2 : (361 : ℝ) ≤ Real.log s ^ 2 := by nlinarith
  have : 0.05 * s / Real.log s ^ 2 ≤ 0.05 * s / 361 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hl2
  have : 0.05 * s / 361 = s / 7220 := by ring
  linarith

/-- Chebyshev lower bound for real arguments: `ψ(z) ≥ 0.9212 (z - 1) - 5 log z` for `z ≥ 30`. -/
lemma psi_ge_real {z : ℝ} (hz : 30 ≤ z) : 0.9212 * (z - 1) - 5 * Real.log z ≤ ψ z := by
  have hz0 : 0 ≤ z := by linarith
  set n := ⌊z⌋₊ with hn
  have hnz : (n : ℝ) ≤ z := Nat.floor_le hz0
  have hnz' : z < n + 1 := Nat.lt_floor_add_one z
  have hn30 : 30 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hz)
  have hpsi := LeanLab.ChebyshevExplicit.psi_ge_09212 n hn30
  rw [← psi_eq_psi_coe_floor] at hpsi
  have hn30' : (30 : ℝ) ≤ n := by exact_mod_cast hn30
  have hlog : Real.log n ≤ Real.log z := Real.log_le_log (by linarith) hnz
  linarith

/-- `log (v^4) ≤ 1.48 v` for `v > 0`. -/
lemma log_pow4_le {v : ℝ} (hv : 0 < v) : Real.log (v ^ 4) ≤ 1.48 * v := by
  rw [Real.log_pow]
  have h := LeanLab.Common.PsiTheta.log_le_div_e hv
  have he := Real.exp_one_gt_d9
  have h1 : v / Real.exp 1 ≤ v / 2.7182818283 :=
    div_le_div_of_nonneg_left hv.le (by norm_num) he.le
  have h2 : v / 2.7182818283 ≤ 0.37 * v := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  push_cast
  linarith

/-- Root bookkeeping: with `v = x^{1/12}`, `√x = v^6`, `x^{1/3} = v^4`, `x^{1/4} = v^3`. -/
lemma roots_eq {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x = (x ^ ((12 : ℕ) : ℝ)⁻¹) ^ 6 ∧
    x ^ (1 / 3 : ℝ) = (x ^ ((12 : ℕ) : ℝ)⁻¹) ^ 4 ∧
    x ^ (1 / 4 : ℝ) = (x ^ ((12 : ℕ) : ℝ)⁻¹) ^ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LeanLab.Common.PsiTheta.rpow_inv_pow' hx, Real.sqrt_eq_rpow]; norm_num
  · rw [LeanLab.Common.PsiTheta.rpow_inv_pow' hx]; norm_num
  · rw [LeanLab.Common.PsiTheta.rpow_inv_pow' hx]; norm_num

/-- **Costa Pereira 1985 Theorem 5 from the explicit theta bound.** Kadiri and Lumley 2014 page 3, Lemma 2.1,
equation 2.9: for `x ≥ e^38`, `0.999 √x + x^{1/3} < ψ(x) - θ(x) < 1.001 √x + x^{1/3}`.
This is the standard derivation of Costa Pereira Theorem 5 from an explicit bound for `θ` at
`√x`: Mathlib's inequalities `ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/7}) ≤ ψ(x) - θ(x) ≤
ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`, the bound `|θ(√x) - √x| < 0.05 √x / log² √x`, and the
lab's Chebyshev bounds for the smaller roots.
Conditional on the theta bound `hD`, Dusart 2010 Theorem 5.2 row `η_2 = 0.05`. -/
theorem costa_of_dusart
    (hD : ∀ t : ℝ, 122568683 ≤ t → |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2) :
    CostaEstimate := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 38) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  obtain ⟨hs, hz, h4⟩ := roots_eq hx0.le
  set v := x ^ ((12 : ℕ) : ℝ)⁻¹ with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos hx0 _
  have hv12 : v ^ 12 = x := LeanLab.Common.PsiTheta.rpow_inv_pow hx0.le 12 (by norm_num)
  have hv23 : 23 ≤ v :=
    le_of_pow_le_pow_left₀ (n := 12) (by norm_num) hv0.le (by rw [hv12]; linarith [exp38_ge])
  -- the theta bound at `s = √x = v^6`
  have hlogx : 38 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 38) hx; rwa [Real.log_exp] at this
  have hlogs : 19 ≤ Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]; linarith
  have hv2 : (529 : ℝ) ≤ v ^ 2 := by nlinarith
  have hv3 : 23 * v ^ 2 ≤ v ^ 3 := by nlinarith
  have hv4 : 23 * v ^ 3 ≤ v ^ 4 := by nlinarith
  have hv6 : 529 * v ^ 4 ≤ v ^ 6 := by nlinarith
  have hv4v : 12167 * v ≤ v ^ 4 := by nlinarith
  have hs8 : (148035889 : ℝ) ≤ Real.sqrt x := by
    rw [hs]; nlinarith
  have hth := theta_close hD (s := Real.sqrt x) (by linarith) hlogs
  rw [abs_le] at hth
  -- Mathlib forms of the roots
  have e2 : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  have e3 : x ^ (3 : ℝ)⁻¹ = x ^ (1 / 3 : ℝ) := by norm_num
  have hlz : Real.log (x ^ (1 / 3 : ℝ)) ≤ 1.48 * v := by rw [hz]; exact log_pow4_le hv0
  constructor
  · -- lower half
    have hCP := psi_sub_theta_ge_psi_add_psi_add_psi hx0.le
    rw [e2, e3] at hCP
    have h7 := psi_nonneg (x ^ (7 : ℝ)⁻¹)
    have hts := theta_le_psi (Real.sqrt x)
    have hz30 : (30 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by rw [hz]; nlinarith
    have hpz := psi_ge_real hz30
    rw [hs, hz] at hCP
    rw [hs] at hth hts ⊢
    rw [hz] at hpz hlz ⊢
    linarith
  · -- upper half
    have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
    rw [e2, e3] at hCP
    have h8 : (10 : ℝ) ^ 8 ≤ Real.sqrt x := by norm_num; linarith
    have hsq := LeanLab.Common.PsiTheta.psi_sub_theta_lt_125 h8
    have hsqs : Real.sqrt (Real.sqrt x) = v ^ 3 := by
      rw [hs, show v ^ 6 = (v ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hsqs] at hsq
    have hz1 : 1 ≤ x ^ (1 / 3 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have hpz := LeanLab.Common.PsiTheta.psi_le_real hz1
    have hc1 : 1 ≤ x ^ (5 : ℝ)⁻¹ := Real.one_le_rpow hx1 (by norm_num)
    have hpc := LeanLab.Common.PsiTheta.psi_le_real hc1
    have hc4 : x ^ (5 : ℝ)⁻¹ ≤ x ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [h4] at hc4
    have hlc0 : 0 ≤ Real.log (x ^ (5 : ℝ)⁻¹) := Real.log_nonneg hc1
    have hlz0 : 0 ≤ Real.log (x ^ (1 / 3 : ℝ)) := Real.log_nonneg hz1
    have hlcz : Real.log (x ^ (5 : ℝ)⁻¹) ≤ Real.log (x ^ (1 / 3 : ℝ)) := by
      apply Real.log_le_log (by linarith)
      rw [hz]; nlinarith
    have hlc2 : Real.log (x ^ (5 : ℝ)⁻¹) ^ 2 ≤ 2.2 * v ^ 2 := by nlinarith
    have hlz2 : Real.log (x ^ (1 / 3 : ℝ)) ^ 2 ≤ 2.2 * v ^ 2 := by nlinarith
    rw [hs, hz] at hCP
    rw [hs] at hth hsq ⊢
    rw [hz] at hpz hlz2 ⊢
    linarith

end LeanLab.KadiriLumley2014.CostaSplit
