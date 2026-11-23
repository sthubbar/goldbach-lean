module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0923.
P0009 BJS 2022, Lemma 19 (60): `F(s) = (2e^γ/s)(1 + ∫_2^{s-1} log(t-1)/t dt)` for `3 ≤ s ≤ 4`.
The Section 9 margin needs an upper bound for `F(c) - 1` with `c` just below 4, through
`m̄ = max(1 - f(c), F(c) - 1)` of (137). PROVED here: `I3_le`,
`∫_2^3 log(t-1)/t dt ≤ 0.1476`, true value 0.1472207, and `Ic_le_I3`, the same for any upper
limit in `[2, 3]`.
Method: `log(1 + y) ≤ y - y²/2 + y³/3` for `y > -1`, by the sign of the derivative `y³/(1+y)`,
at `t - 1 = (3/2)(1 + y)`, then exact integration of the cubic over `t`.
-/

@[expose] public section

open Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.FInt

/-- `g y = y - y²/2 + y³/3 - log(1+y)`. -/
def g (y : ℝ) : ℝ := y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y)

lemma g_hasDeriv (y : ℝ) (hy : -1 < y) : HasDerivAt g (y ^ 3 / (1 + y)) y := by
  have h1 : (1 + y) ≠ 0 := by linarith
  have hl : HasDerivAt (fun y => log (1 + y)) (1 / (1 + y)) y := by
    have := ((hasDerivAt_id y).const_add 1).log h1
    simpa using this
  have h := ((((hasDerivAt_id' y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
    ((hasDerivAt_pow 3 y).div_const 3)).sub hl)
  have e : g = fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y) := rfl
  rw [e]
  convert h using 1
  push_cast
  field_simp
  ring

lemma g_cont : ContinuousOn g (Set.Ioi (-1)) := by
  intro y hy
  exact (g_hasDeriv y hy).continuousAt.continuousWithinAt

theorem g_nonneg (y : ℝ) (hy : -1 < y) : 0 ≤ g y := by
  have g0 : g 0 = 0 := by simp [g]
  rcases le_total 0 y with h | h
  · have hm : MonotoneOn g (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact g_cont.mono (fun x hx => by simp at hx ⊢; linarith)
      · intro x hx
        simp at hx
        exact (g_hasDeriv x (by linarith)).differentiableAt.differentiableWithinAt
      · intro x hx
        simp at hx
        rw [(g_hasDeriv x (by linarith)).deriv]
        have : 0 < 1 + x := by linarith
        positivity
    have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
    linarith
  · have ha : AntitoneOn g (Set.Ioc (-1) 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc (-1) 0)
      · exact g_cont.mono (fun x hx => hx.1)
      · intro x hx
        rw [interior_Ioc] at hx
        exact (g_hasDeriv x hx.1).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioc] at hx
        rw [(g_hasDeriv x hx.1).deriv]
        have h1 : 0 < 1 + x := by linarith [hx.1]
        have h2 : x ^ 3 ≤ 0 := by
          have : x ^ 3 = x * x ^ 2 := by ring
          rw [this]; exact mul_nonpos_of_nonpos_of_nonneg hx.2.le (sq_nonneg x)
        exact div_nonpos_of_nonpos_of_nonneg h2 h1.le
    have := ha ⟨hy, h⟩ ⟨by norm_num, le_rfl⟩ h
    linarith

lemma log_le_cubic (y : ℝ) (hy : -1 < y) : log (1 + y) ≤ y - y ^ 2 / 2 + y ^ 3 / 3 := by
  have := g_nonneg y hy; unfold g at this; linarith

/-- the pointwise bound on `[2, 3]`. -/
lemma integrand_le (t : ℝ) (ht : 2 ≤ t) :
    log (t - 1) / t ≤ (log (3 / 2) + (2 * t - 5) / 3 - ((2 * t - 5) / 3) ^ 2 / 2 +
      ((2 * t - 5) / 3) ^ 3 / 3) / t := by
  have ht0 : 0 < t := by linarith
  apply div_le_div_of_nonneg_right _ ht0.le
  have e : t - 1 = 3 / 2 * (1 + (2 * t - 5) / 3) := by ring
  rw [e, log_mul (by norm_num) (by nlinarith)]
  have := log_le_cubic ((2 * t - 5) / 3) (by linarith)
  linarith

lemma cubic_div_eq (t : ℝ) (ht : t ≠ 0) :
    (log (3 / 2) + (2 * t - 5) / 3 - ((2 * t - 5) / 3) ^ 2 / 2 + ((2 * t - 5) / 3) ^ 3 / 3) / t =
      (log (3 / 2) - 745 / 162) * t⁻¹ + 98 / 27 - 26 / 27 * t + 8 / 81 * t ^ 2 := by
  field_simp; ring

/-- `∫_2^3 log(t-1)/t dt ≤ log(3/2)² ... `, the exact integral of the cubic bound. -/
theorem I3_le_exact :
    ∫ t in (2 : ℝ)..3, log (t - 1) / t ≤
      (log (3 / 2) - 745 / 162) * log (3 / 2) + 98 / 27 - 26 / 27 * (5 / 2) +
        8 / 81 * (19 / 3) := by
  have hc1 : ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.uIcc 2 3) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div _ continuousOn_id (fun x hx => by simp at hx ⊢; linarith [hx.1])
    apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro x hx; simp at hx ⊢; linarith [hx.1]
  have hc2 : ContinuousOn (fun t : ℝ => (log (3 / 2) - 745 / 162) * t⁻¹ + 98 / 27 -
      26 / 27 * t + 8 / 81 * t ^ 2) (Set.uIcc 2 3) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.add _ (by fun_prop)
    apply ContinuousOn.sub _ (by fun_prop)
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_inv₀.mono (fun x hx => by simp at hx ⊢; linarith [hx.1])
  have hmono : ∫ t in (2 : ℝ)..3, log (t - 1) / t ≤
      ∫ t in (2 : ℝ)..3, ((log (3 / 2) - 745 / 162) * t⁻¹ + 98 / 27 - 26 / 27 * t +
        8 / 81 * t ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable)
      (hc2.intervalIntegrable)
    intro t ht
    rw [← cubic_div_eq t (by linarith [ht.1])]
    exact integrand_le t ht.1
  refine hmono.trans (le_of_eq ?_)
  have i1 : IntervalIntegrable (fun t : ℝ => (log (3 / 2) - 745 / 162) * t⁻¹) MeasureTheory.volume 2 3 :=
    (continuousOn_const.mul (continuousOn_inv₀.mono (fun x hx => by
      rw [Set.uIcc_of_le (by norm_num)] at hx; simp; linarith [hx.1]))).intervalIntegrable
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, integral_inv (by norm_num [Set.uIcc_of_le]),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  · norm_num
  all_goals first
    | exact i1
    | exact intervalIntegrable_const
    | exact (i1.add intervalIntegrable_const)
    | exact ((i1.add intervalIntegrable_const).sub ((continuous_const.mul continuous_id).intervalIntegrable _ _))
    | exact ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    | exact ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
    | skip

/-- **`∫_2^3 log(t-1)/t dt ≤ 0.1476`, PROVED.** -/
theorem I3_le : ∫ t in (2 : ℝ)..3, log (t - 1) / t ≤ 0.1476 := by
  have h := I3_le_exact
  have e : log (3 / 2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have a := log_two_gt_d9
  have b := log_two_lt_d9
  have c := log_three_gt_d9
  have d := log_three_lt_d9
  rw [e] at h
  norm_num at a b c d h ⊢
  nlinarith

/-- For `2 ≤ x ≤ 3`, `∫_2^x log(t-1)/t dt ≤ ∫_2^3`, the integrand is nonnegative on `[x, 3]`. -/
theorem Ic_le_I3 (x : ℝ) (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    ∫ t in (2 : ℝ)..x, log (t - 1) / t ≤ ∫ t in (2 : ℝ)..3, log (t - 1) / t := by
  have hc : ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.Icc 2 3) := by
    apply ContinuousOn.div _ continuousOn_id (fun x hx => by simp at hx ⊢; linarith [hx.1])
    apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro x hx; simp at hx ⊢; linarith [hx.1]
  have hint : ∀ a b : ℝ, a ∈ Set.Icc (2:ℝ) 3 → b ∈ Set.Icc (2:ℝ) 3 →
      IntervalIntegrable (fun t : ℝ => log (t - 1) / t) MeasureTheory.volume a b := by
    intro a b ha hb
    apply (hc.mono _).intervalIntegrable
    exact Set.uIcc_subset_Icc ha hb
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    (hint 2 x ⟨le_rfl, by norm_num⟩ ⟨hx2, hx3⟩) (hint x 3 ⟨hx2, hx3⟩ ⟨by norm_num, le_rfl⟩)]
  have : 0 ≤ ∫ t in x..3, log (t - 1) / t := by
    apply intervalIntegral.integral_nonneg hx3
    intro t ht
    have : 0 ≤ log (t - 1) := log_nonneg (by linarith [ht.1])
    exact div_nonneg this (by linarith [ht.1])
  linarith

end LeanLab.ChenExplicit.FInt
