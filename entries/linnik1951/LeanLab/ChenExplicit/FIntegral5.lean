module

public import LeanLab.ChenExplicit.FIntegral

/-!
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T0703Z-249, unit U-1041, track T2.
P0009 BJS 2022, Lemma 19 (60), the integral `∫_2^3 log(t-1)/t dt`, true value 0.1472207.
FIntegral.lean proves `≤ 0.1476` from the cubic Taylor bound; here the quintic bound
`log(1 + y) ≤ y - y²/2 + y³/3 - y⁴/4 + y⁵/5` for `y > -1`, by the sign of the derivative
`y⁵/(1+y)`, gives `I3_le5 : ∫_2^3 log(t-1)/t dt ≤ 0.14725`; the exact value of the quintic bound is
`(log(3/2) - 8845/972) log(3/2) + 66931/18225 ≈ 0.1472358`. The sharper bound lowers the Section 9
term `m̄` of (137) from 0.02208 to 0.02177, which the corrected margin at log log X₂ = 32.72 needs.
Chen's theorem is not in doubt; Goldbach is open.
-/

@[expose] public section

open Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.FInt5

/-- `g5 y = y - y²/2 + y³/3 - y⁴/4 + y⁵/5 - log(1+y)`. -/
def g5 (y : ℝ) : ℝ := y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - log (1 + y)

lemma g5_hasDeriv (y : ℝ) (hy : -1 < y) : HasDerivAt g5 (y ^ 5 / (1 + y)) y := by
  have h1 : (1 + y) ≠ 0 := by linarith
  have hl : HasDerivAt (fun y => log (1 + y)) (1 / (1 + y)) y := by
    have := ((hasDerivAt_id y).const_add 1).log h1
    simpa using this
  have h := ((((((hasDerivAt_id' y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
    ((hasDerivAt_pow 3 y).div_const 3)).sub ((hasDerivAt_pow 4 y).div_const 4)).add
    ((hasDerivAt_pow 5 y).div_const 5)).sub hl)
  have e : g5 = fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - log (1 + y) := rfl
  rw [e]
  convert h using 1
  push_cast
  field_simp
  ring

lemma g5_cont : ContinuousOn g5 (Set.Ioi (-1)) := by
  intro y hy
  exact (g5_hasDeriv y hy).continuousAt.continuousWithinAt

theorem g5_nonneg (y : ℝ) (hy : -1 < y) : 0 ≤ g5 y := by
  have g0 : g5 0 = 0 := by simp [g5]
  rcases le_total 0 y with h | h
  · have hm : MonotoneOn g5 (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact g5_cont.mono (fun x hx => by simp at hx ⊢; linarith)
      · intro x hx
        simp at hx
        exact (g5_hasDeriv x (by linarith)).differentiableAt.differentiableWithinAt
      · intro x hx
        simp at hx
        rw [(g5_hasDeriv x (by linarith)).deriv]
        have : 0 < 1 + x := by linarith
        positivity
    have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
    linarith
  · have ha : AntitoneOn g5 (Set.Ioc (-1) 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc (-1) 0)
      · exact g5_cont.mono (fun x hx => hx.1)
      · intro x hx
        rw [interior_Ioc] at hx
        exact (g5_hasDeriv x hx.1).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioc] at hx
        rw [(g5_hasDeriv x hx.1).deriv]
        have h1 : 0 < 1 + x := by linarith [hx.1]
        have h2 : x ^ 5 ≤ 0 := by
          have : x ^ 5 = x * (x ^ 2) ^ 2 := by ring
          rw [this]; exact mul_nonpos_of_nonpos_of_nonneg hx.2.le (by positivity)
        exact div_nonpos_of_nonpos_of_nonneg h2 h1.le
    have := ha ⟨hy, h⟩ ⟨by norm_num, le_rfl⟩ h
    linarith

lemma log_le_quintic (y : ℝ) (hy : -1 < y) :
    log (1 + y) ≤ y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 := by
  have := g5_nonneg y hy; unfold g5 at this; linarith

/-- the pointwise bound on `[2, 3]`. -/
lemma integrand_le5 (t : ℝ) (ht : 2 ≤ t) :
    log (t - 1) / t ≤ (log (3 / 2) + (2 * t - 5) / 3 - ((2 * t - 5) / 3) ^ 2 / 2 +
      ((2 * t - 5) / 3) ^ 3 / 3 - ((2 * t - 5) / 3) ^ 4 / 4 + ((2 * t - 5) / 3) ^ 5 / 5) / t := by
  have ht0 : 0 < t := by linarith
  apply div_le_div_of_nonneg_right _ ht0.le
  have e : t - 1 = 3 / 2 * (1 + (2 * t - 5) / 3) := by ring
  rw [e, log_mul (by norm_num) (by nlinarith)]
  have := log_le_quintic ((2 * t - 5) / 3) (by linarith)
  linarith

lemma quintic_div_eq (t : ℝ) (ht : t ≠ 0) :
    (log (3 / 2) + (2 * t - 5) / 3 - ((2 * t - 5) / 3) ^ 2 / 2 + ((2 * t - 5) / 3) ^ 3 / 3 -
      ((2 * t - 5) / 3) ^ 4 / 4 + ((2 * t - 5) / 3) ^ 5 / 5) / t =
      (log (3 / 2) - 8845 / 972) * t⁻¹ + (2882 / 243 + (-(1684 / 243) * t + (544 / 243 * t ^ 2 +
        (-(92 / 243) * t ^ 3 + 32 / 1215 * t ^ 4)))) := by
  field_simp; ring

/-- the exact integral of the quintic bound. -/
theorem I3_le_exact5 :
    ∫ t in (2 : ℝ)..3, log (t - 1) / t ≤ (log (3 / 2) - 8845 / 972) * log (3 / 2) + 66931 / 18225 := by
  have hc1 : ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.uIcc 2 3) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div _ continuousOn_id (fun x hx => by simp at hx ⊢; linarith [hx.1])
    apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro x hx; simp at hx ⊢; linarith [hx.1]
  have hinv : ContinuousOn (fun t : ℝ => (log (3 / 2) - 8845 / 972) * t⁻¹) (Set.uIcc 2 3) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_inv₀.mono (fun x hx => by simp at hx ⊢; linarith [hx.1])
  have hpoly : Continuous (fun t : ℝ => 2882 / 243 + (-(1684 / 243) * t + (544 / 243 * t ^ 2 +
      (-(92 / 243) * t ^ 3 + 32 / 1215 * t ^ 4)))) := by fun_prop
  have hmono : ∫ t in (2 : ℝ)..3, log (t - 1) / t ≤
      ∫ t in (2 : ℝ)..3, ((log (3 / 2) - 8845 / 972) * t⁻¹ + (2882 / 243 + (-(1684 / 243) * t +
        (544 / 243 * t ^ 2 + (-(92 / 243) * t ^ 3 + 32 / 1215 * t ^ 4))))) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable)
      ((hinv.add hpoly.continuousOn).intervalIntegrable)
    intro t ht
    simp only [Pi.add_apply]
    rw [← quintic_div_eq t (by linarith [ht.1])]
    exact integrand_le5 t ht.1
  refine hmono.trans (le_of_eq ?_)
  set A : ℝ := log (3 / 2) - 8845 / 972 with hA
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) 3, HasDerivAt (fun t : ℝ => A * log t + (2882 / 243 * t +
      (-(842 / 243) * t ^ 2 + (544 / 729 * t ^ 3 + (-(23 / 243) * t ^ 4 + 32 / 6075 * t ^ 5)))))
      (A * x⁻¹ + (2882 / 243 + (-(1684 / 243) * x + (544 / 243 * x ^ 2 +
        (-(92 / 243) * x ^ 3 + 32 / 1215 * x ^ 4))))) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := ((Real.hasDerivAt_log hx0).const_mul A).add
      ((((hasDerivAt_id x).const_mul (2882 / 243 : ℝ)).add
        ((((hasDerivAt_pow 2 x).const_mul (-(842 / 243) : ℝ)).add
          ((((hasDerivAt_pow 3 x).const_mul (544 / 729 : ℝ)).add
            ((((hasDerivAt_pow 4 x).const_mul (-(23 / 243) : ℝ)).add
              (((hasDerivAt_pow 5 x).const_mul (32 / 6075 : ℝ)))))))))))
    convert h using 1
    all_goals first
      | rfl
      | (funext t; simp [Pi.add_apply]; ring)
      | (push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hinv.add hpoly.continuousOn).intervalIntegrable)]
  have e : log (3 / 2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  rw [hA, e]
  ring

/-- **`∫_2^3 log(t-1)/t dt ≤ 0.14725`, PROVED.** -/
theorem I3_le5 : ∫ t in (2 : ℝ)..3, log (t - 1) / t ≤ 0.14725 := by
  have h := I3_le_exact5
  have e : log (3 / 2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have a := log_two_gt_d9
  have b := log_two_lt_d9
  have c := log_three_gt_d9
  have d := log_three_lt_d9
  rw [e] at h
  norm_num at a b c d h ⊢
  nlinarith [mul_le_mul_of_nonneg_left (show log 3 - log 2 ≥ 0.4054651 by linarith)
    (show (0:ℝ) ≤ 8845 / 972 - (log 3 - log 2) by linarith)]


end LeanLab.ChenExplicit.FInt5
