module

public import Mathlib
public import LeanLab.ChirreHagen2025.Bilinear

/-!
U-5027, faithfulness of `ThetaRel`. Schoenfeld 1976, Math. Comp. 30, Corollary 1, under RH:
`|θ(x) - x| < √x log² x / (8π)` for `x ≥ 599`. The lab states it with `≤` as `SchoenfeldTheta`,
CITED, and proves here that it implies `ThetaRel`, `|θ(u) - u| ≤ u / 10^5` for `u ≥ 10^16`, so
`goldbach_12` rests on Theorem 3 of Chirre-Hagen, Schoenfeld's Corollary 1 and the 4e18 check.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- Schoenfeld 1976, Corollary 1, as a cited Prop; it holds under RH. -/
def SchoenfeldTheta : Prop :=
  ∀ u : ℝ, 599 ≤ u → |θ u - u| ≤ √u * Real.log u ^ 2 / (8 * π)

theorem log_1e8_le : Real.log (10 ^ 8) ≤ 19 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7 : ℝ) ^ 19 ≤ Real.exp 1 ^ 19 :=
    pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 19
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

theorem thetaRel_of_schoenfeld (h : SchoenfeldTheta) : ThetaRel := by
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
  -- √u log² u = w · 4 log² w = 4 w² (log² w / w)
  have e : √u * Real.log u ^ 2 = 4 * u * (Real.log w ^ 2 / w) := by
    rw [← hw, hlog, ← hw2]; field_simp; ring
  rw [e]
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : 4 * u * (Real.log w ^ 2 / w) ≤ 4 * u * ((19 / 10 ^ 4) ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  nlinarith

/-- `goldbach_12` from Schoenfeld's Corollary 1 in place of `ThetaRel`. -/
theorem goldbach_12_schoenfeld
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 12 * Real.log x ^ 2 :=
  fun hRH => goldbach_12 h3 hE (thetaRel_of_schoenfeld (hS hRH)) hRH

end LeanLab.ChirreHagen2025

