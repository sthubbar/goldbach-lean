module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import LeanLab.PNTPort.Perron.Cauchy

/-!
Ported from PrimeNumberTheoremAnd, commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
file PrimeNumberTheoremAnd/LaplaceInversion.lean (the declarations from
`intervalIntegral_sinc_tail_eq_ibp` through `tendsto_intervalIntegral_real_sinc_atTop`).
License: Apache-2.0, see LICENSE-PrimeNumberTheoremAnd.txt in this folder.
Original authors: the PrimeNumberTheoremAnd contributors.
Narrow port for the lab; AI made the port edits (only the declarations needed for the
Dirichlet integral are kept, placed under namespace LeanLab.PNTPort.Perron, and fixed
for Mathlib v4.35.0 where needed).
-/

@[expose] public section

/-!
# The Dirichlet integral

`∫ x in 0..A, sinc x → π / 2` as `A → ∞`.
-/

namespace LeanLab.PNTPort.Perron

open Real Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- Integration by parts for the positive sinc tail on a finite interval. -/
theorem intervalIntegral_sinc_tail_eq_ibp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sinc x =
      (-Real.cos b / b + Real.cos a / a) -
        ∫ x in a..b, Real.cos x / x ^ 2 := by
  have hpos_uIcc : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hsinc :
      (∫ x in a..b, Real.sinc x) = ∫ x in a..b, x⁻¹ * Real.sin x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    rw [Real.sinc_of_ne_zero hx0]
    ring
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    exact hasDerivAt_inv (hpos_uIcc x hx).ne'
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x _hx
    have h : HasDerivAt (fun y : ℝ => -Real.cos y) (-(-Real.sin x)) x :=
      (Real.hasDerivAt_cos x).neg
    rwa [neg_neg] at h
  have hu' : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x (by simpa [Set.uIcc_of_le hab] using hx)).ne').neg
  have hv' : IntervalIntegrable (fun x : ℝ => Real.sin x) volume a b :=
    Real.continuous_sin.intervalIntegrable a b
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x⁻¹) (v := fun x : ℝ => -Real.cos x)
    (u' := fun x : ℝ => -(x ^ 2)⁻¹) (v' := fun x : ℝ => Real.sin x)
    hu hv hu' hv'
  have hint :
      (∫ x in a..b, (-(x ^ 2)⁻¹) * -Real.cos x) =
        ∫ x in a..b, Real.cos x / x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    field_simp [sq]
  rw [hsinc, hIBP, hint]
  ring_nf

/-- The finite inverse-square integral on a positive interval. -/
theorem intervalIntegral_inv_sq_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (x ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  have hpos_uIcc : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have h : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ 2)⁻¹)) x :=
      (hasDerivAt_inv (hpos_uIcc x hx).ne').neg
    rwa [neg_neg] at h
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x (by simpa [Set.uIcc_of_le hab] using hx)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Uniform finite-tail control for the one-sided sinc integral. -/
theorem norm_intervalIntegral_sinc_tail_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∫ x in a..b, Real.sinc x‖ ≤ 3 * a⁻¹ := by
  have ha_pos : 0 < a := zero_lt_one.trans_le ha
  have hb_pos : 0 < b := ha_pos.trans_le hab
  have hpos_uIcc : ∀ x ∈ Set.Icc a b, 0 < x := by
    intro x hx
    exact ha_pos.trans_le hx.1
  have hboundary : ‖-Real.cos b / b + Real.cos a / a‖ ≤ 2 * a⁻¹ := by
    calc
      ‖-Real.cos b / b + Real.cos a / a‖
          = |(-Real.cos b / b) + (Real.cos a / a)| := by rw [Real.norm_eq_abs]
      _ ≤ |-Real.cos b / b| + |Real.cos a / a| := abs_add_le _ _
      _ ≤ b⁻¹ + a⁻¹ := by
            refine add_le_add ?_ ?_
            · calc
                |-Real.cos b / b| = |Real.cos b| / b := by
                  rw [abs_div, abs_neg, abs_of_pos hb_pos]
                _ ≤ 1 / b := div_le_div_of_nonneg_right (Real.abs_cos_le_one b) hb_pos.le
                _ = b⁻¹ := by rw [one_div]
            · calc
                |Real.cos a / a| = |Real.cos a| / a := by
                  rw [abs_div, abs_of_pos ha_pos]
                _ ≤ 1 / a := div_le_div_of_nonneg_right (Real.abs_cos_le_one a) ha_pos.le
                _ = a⁻¹ := by rw [one_div]
      _ ≤ a⁻¹ + a⁻¹ := by
            exact add_le_add (by
              simpa [one_div] using one_div_le_one_div_of_le ha_pos hab) le_rfl
      _ = 2 * a⁻¹ := by ring
  have hnormInt : IntervalIntegrable (fun x : ℝ => ‖Real.cos x / x ^ 2‖) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((Real.continuous_cos.continuousOn).div (continuousOn_pow 2) fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne').norm
  have hinvInt : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne'
  have hJ : ‖∫ x in a..b, Real.cos x / x ^ 2‖ ≤ a⁻¹ := by
    calc
      ‖∫ x in a..b, Real.cos x / x ^ 2‖
          ≤ ∫ x in a..b, ‖Real.cos x / x ^ 2‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on hab hnormInt hinvInt ?_
            intro x hx
            have hx_pos : 0 < x := hpos_uIcc x hx
            calc
              ‖Real.cos x / x ^ 2‖ = |Real.cos x| / x ^ 2 := by
                rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx_pos 2)]
              _ ≤ 1 / x ^ 2 :=
                div_le_div_of_nonneg_right (Real.abs_cos_le_one x) (sq_nonneg x)
              _ = (x ^ 2)⁻¹ := by rw [one_div]
      _ = a⁻¹ - b⁻¹ := intervalIntegral_inv_sq_of_pos ha_pos hab
      _ ≤ a⁻¹ := sub_le_self _ (inv_nonneg.mpr hb_pos.le)
  rw [intervalIntegral_sinc_tail_eq_ibp ha_pos hab]
  calc
    ‖(-Real.cos b / b + Real.cos a / a) - ∫ x in a..b, Real.cos x / x ^ 2‖
        ≤ ‖-Real.cos b / b + Real.cos a / a‖ +
            ‖∫ x in a..b, Real.cos x / x ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 * a⁻¹ + a⁻¹ := add_le_add hboundary hJ
    _ = 3 * a⁻¹ := by ring

theorem cauchySeq_intervalIntegral_real_sinc_atTop :
    CauchySeq (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x) := by
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  have hlim : Filter.Tendsto (fun M : ℝ => 3 * M⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Filter.Tendsto
      (fun M : ℝ => 3 * M⁻¹) Filter.atTop (nhds (3 * 0)))
  have hsmall : ∀ᶠ M : ℝ in Filter.atTop, 3 * M⁻¹ < ε :=
    hlim.eventually (gt_mem_nhds hε)
  have hlarge : ∀ᶠ M : ℝ in Filter.atTop, 1 ≤ M := Filter.eventually_ge_atTop 1
  rcases Filter.eventually_atTop.1 (hsmall.and hlarge) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro A hA B hB
  have hMsmall : 3 * M⁻¹ < ε := (hM M le_rfl).1
  have hM_one : 1 ≤ M := (hM M le_rfl).2
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_one
  have hA_one : 1 ≤ A := hM_one.trans hA
  have hB_one : 1 ≤ B := hM_one.trans hB
  by_cases hAB : A ≤ B
  · have hsub :
        (∫ x in (0 : ℝ)..B, Real.sinc x) -
          (∫ x in (0 : ℝ)..A, Real.sinc x) =
            ∫ x in A..B, Real.sinc x := by
      exact intervalIntegral.integral_interval_sub_left
        (Real.continuous_sinc.intervalIntegrable _ _)
        (Real.continuous_sinc.intervalIntegrable _ _)
    have hinv : A⁻¹ ≤ M⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hM_pos hA
    calc
      dist (∫ x in (0 : ℝ)..A, Real.sinc x) (∫ x in (0 : ℝ)..B, Real.sinc x)
          = dist (∫ x in (0 : ℝ)..B, Real.sinc x) (∫ x in (0 : ℝ)..A, Real.sinc x) :=
            dist_comm _ _
      _ = ‖(∫ x in (0 : ℝ)..B, Real.sinc x) -
            (∫ x in (0 : ℝ)..A, Real.sinc x)‖ := by
            rw [Real.dist_eq, Real.norm_eq_abs]
      _ = ‖∫ x in A..B, Real.sinc x‖ := by rw [hsub]
      _ ≤ 3 * A⁻¹ := norm_intervalIntegral_sinc_tail_le hA_one hAB
      _ ≤ 3 * M⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ < ε := hMsmall
  · have hBA : B ≤ A := le_of_not_ge hAB
    have hsub :
        (∫ x in (0 : ℝ)..A, Real.sinc x) -
          (∫ x in (0 : ℝ)..B, Real.sinc x) =
            ∫ x in B..A, Real.sinc x := by
      exact intervalIntegral.integral_interval_sub_left
        (Real.continuous_sinc.intervalIntegrable _ _)
        (Real.continuous_sinc.intervalIntegrable _ _)
    have hinv : B⁻¹ ≤ M⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hM_pos hB
    calc
      dist (∫ x in (0 : ℝ)..A, Real.sinc x) (∫ x in (0 : ℝ)..B, Real.sinc x)
          = ‖(∫ x in (0 : ℝ)..A, Real.sinc x) -
            (∫ x in (0 : ℝ)..B, Real.sinc x)‖ := by
            rw [Real.dist_eq, Real.norm_eq_abs]
      _ = ‖∫ x in B..A, Real.sinc x‖ := by rw [hsub]
      _ ≤ 3 * B⁻¹ := norm_intervalIntegral_sinc_tail_le hB_one hBA
      _ ≤ 3 * M⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ < ε := hMsmall

/-- Existence of the improper one-sided sinc integral as a finite-window limit. -/
theorem exists_tendsto_intervalIntegral_real_sinc_atTop :
    ∃ L : ℝ,
      Filter.Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x)
        Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_complete cauchySeq_intervalIntegral_real_sinc_atTop

/-- Exact integral of the derivative of `-exp (-a * x)` on a finite interval. -/
theorem intervalIntegral_exp_neg_mul_const_mul_self (a R B : ℝ) :
    ∫ x in R..B, a * Real.exp (-a * x) =
      Real.exp (-a * R) - Real.exp (-a * B) := by
  have hderiv : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => -Real.exp (-a * y)) (a * Real.exp (-a * x)) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have h := (Real.hasDerivAt_exp (-a * x)).comp x hlin
    rw [show a * Real.exp (-a * x) = -(Real.exp (-a * x) * -a) from by ring]
    exact h.neg
  have hint : IntervalIntegrable (fun x : ℝ => a * Real.exp (-a * x)) volume R B := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Uniform finite-tail control for the damped one-sided sinc integral. -/
theorem norm_intervalIntegral_exp_neg_mul_sinc_tail_le
    {a R B : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (hRB : R ≤ B) :
    ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  have hB_pos : 0 < B := hR_pos.trans_le hRB
  have hpos_uIcc : ∀ x ∈ Set.uIcc R B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hRB] at hx
    exact hR_pos.trans_le hx.1
  have hpos_Icc : ∀ x ∈ Set.Icc R B, 0 < x := by
    intro x hx
    exact hR_pos.trans_le hx.1
  have hsinc :
      (∫ x in R..B, Real.exp (-a * x) * Real.sinc x) =
        ∫ x in R..B, (Real.exp (-a * x) * x⁻¹) * Real.sin x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    simp only [Real.sinc_of_ne_zero hx0]
    ring
  have hu : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => Real.exp (-a * y) * y⁻¹)
        (-(a * Real.exp (-a * x) * x⁻¹) - Real.exp (-a * x) * (x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    have hlin : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have hexp := (Real.hasDerivAt_exp (-a * x)).comp x hlin
    have hinv := hasDerivAt_inv hx0
    have hmul := hexp.mul hinv
    rw [show -(a * Real.exp (-a * x) * x⁻¹) - Real.exp (-a * x) * (x ^ 2)⁻¹
        = Real.exp (-a * x) * -a * x⁻¹ + Real.exp (-a * x) * -(x ^ 2)⁻¹ from by ring]
    exact hmul
  have hv : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x _hx
    have h : HasDerivAt (fun y : ℝ => -Real.cos y) (-(-Real.sin x)) x :=
      (Real.hasDerivAt_cos x).neg
    rwa [neg_neg] at h
  have hu' : IntervalIntegrable
      (fun x : ℝ => -(a * Real.exp (-a * x) * x⁻¹) -
        Real.exp (-a * x) * (x ^ 2)⁻¹) volume R B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRB
    have hcont_exp : ContinuousOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc R B) := by
      fun_prop
    have hcont_inv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc R B) :=
      continuousOn_id.inv₀ fun x hx => (hpos_Icc x hx).ne'
    have hcont_inv_sq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc R B) :=
      (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_Icc x hx).ne'
    exact (((continuousOn_const.mul hcont_exp).mul hcont_inv).neg.sub
      (hcont_exp.mul hcont_inv_sq))
  have hv' : IntervalIntegrable (fun x : ℝ => Real.sin x) volume R B :=
    Real.continuous_sin.intervalIntegrable R B
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp (-a * x) * x⁻¹) (v := fun x : ℝ => -Real.cos x)
    (u' := fun x : ℝ => -(a * Real.exp (-a * x) * x⁻¹) -
      Real.exp (-a * x) * (x ^ 2)⁻¹)
    (v' := fun x : ℝ => Real.sin x) hu hv hu' hv'
  have hint :
      (∫ x in R..B,
        (-(a * Real.exp (-a * x) * x⁻¹) - Real.exp (-a * x) * (x ^ 2)⁻¹) *
          -Real.cos x) =
        ∫ x in R..B,
          (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
            Real.cos x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hrepr :
      ∫ x in R..B, Real.exp (-a * x) * Real.sinc x =
        (-Real.exp (-a * B) * B⁻¹ * Real.cos B +
            Real.exp (-a * R) * R⁻¹ * Real.cos R) -
          ∫ x in R..B,
            (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
              Real.cos x := by
    rw [hsinc, hIBP, hint]
    ring
  have hboundary :
      ‖-Real.exp (-a * B) * B⁻¹ * Real.cos B +
          Real.exp (-a * R) * R⁻¹ * Real.cos R‖ ≤ 2 * R⁻¹ := by
    calc
      ‖-Real.exp (-a * B) * B⁻¹ * Real.cos B +
          Real.exp (-a * R) * R⁻¹ * Real.cos R‖
          = |(-Real.exp (-a * B) * B⁻¹ * Real.cos B) +
              (Real.exp (-a * R) * R⁻¹ * Real.cos R)| := by rw [Real.norm_eq_abs]
      _ ≤ |-Real.exp (-a * B) * B⁻¹ * Real.cos B| +
            |Real.exp (-a * R) * R⁻¹ * Real.cos R| := abs_add_le _ _
      _ ≤ B⁻¹ + R⁻¹ := by
            refine add_le_add ?_ ?_
            · calc
                |-Real.exp (-a * B) * B⁻¹ * Real.cos B|
                    = Real.exp (-a * B) * B⁻¹ * |Real.cos B| := by
                      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
                        abs_of_pos (inv_pos.mpr hB_pos)]
                  _ ≤ 1 * B⁻¹ * 1 := by
                      gcongr
                      · exact Real.exp_le_one_iff.mpr (by
                          have hmul : 0 ≤ a * B := mul_nonneg ha.le hB_pos.le
                          nlinarith)
                      · exact Real.abs_cos_le_one B
                  _ = B⁻¹ := by ring
            · calc
                |Real.exp (-a * R) * R⁻¹ * Real.cos R|
                    = Real.exp (-a * R) * R⁻¹ * |Real.cos R| := by
                      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
                        abs_of_pos (inv_pos.mpr hR_pos)]
                  _ ≤ 1 * R⁻¹ * 1 := by
                      gcongr
                      · exact Real.exp_le_one_iff.mpr (by
                          have hmul : 0 ≤ a * R := mul_nonneg ha.le hR_pos.le
                          nlinarith)
                      · exact Real.abs_cos_le_one R
                  _ = R⁻¹ := by ring
      _ ≤ R⁻¹ + R⁻¹ := by
            exact add_le_add (by
              simpa [one_div] using one_div_le_one_div_of_le hR_pos hRB) le_rfl
      _ = 2 * R⁻¹ := by ring
  have hnormInt : IntervalIntegrable
      (fun x : ℝ =>
        ‖(a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
          Real.cos x‖) volume R B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRB
    have hcont_exp : ContinuousOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc R B) := by
      fun_prop
    have hcont_inv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc R B) :=
      continuousOn_id.inv₀ fun x hx => (hpos_Icc x hx).ne'
    have hcont_inv_sq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc R B) :=
      (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_Icc x hx).ne'
    exact ((((continuousOn_const.mul hcont_exp).mul hcont_inv).add
      (hcont_exp.mul hcont_inv_sq)).mul Real.continuous_cos.continuousOn).norm
  have hboundInt : IntervalIntegrable
      (fun x : ℝ => R⁻¹ * (a * Real.exp (-a * x)) + (x ^ 2)⁻¹) volume R B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRB
    have hcont_exp : ContinuousOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc R B) := by
      fun_prop
    have hcont_inv_sq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc R B) :=
      (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_Icc x hx).ne'
    exact ((continuousOn_const.mul (continuousOn_const.mul hcont_exp)).add hcont_inv_sq)
  have hJ :
      ‖∫ x in R..B,
        (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
          Real.cos x‖ ≤ 2 * R⁻¹ := by
    calc
      ‖∫ x in R..B,
        (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
          Real.cos x‖
          ≤ ∫ x in R..B,
              ‖(a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
                Real.cos x‖ :=
            intervalIntegral.norm_integral_le_integral_norm hRB
      _ ≤ ∫ x in R..B, R⁻¹ * (a * Real.exp (-a * x)) + (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on hRB hnormInt hboundInt ?_
            intro x hx
            have hx_pos : 0 < x := hpos_Icc x hx
            have hR_inv : x⁻¹ ≤ R⁻¹ := by
              simpa [one_div] using one_div_le_one_div_of_le hR_pos hx.1
            calc
              ‖(a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
                Real.cos x‖
                  ≤ |a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹| := by
                    rw [Real.norm_eq_abs, abs_mul]
                    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)
              _ = a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹ := by
                    rw [abs_of_nonneg]
                    positivity
              _ ≤ R⁻¹ * (a * Real.exp (-a * x)) + (x ^ 2)⁻¹ := by
                    refine add_le_add ?_ ?_
                    · calc
                        a * Real.exp (-a * x) * x⁻¹
                            = (a * Real.exp (-a * x)) * x⁻¹ := by ring
                        _ ≤ (a * Real.exp (-a * x)) * R⁻¹ :=
                            mul_le_mul_of_nonneg_left hR_inv
                              (mul_nonneg ha.le (Real.exp_pos _).le)
                        _ = R⁻¹ * (a * Real.exp (-a * x)) := by ring
                    · calc
                        Real.exp (-a * x) * (x ^ 2)⁻¹
                            ≤ 1 * (x ^ 2)⁻¹ := by
                              exact mul_le_mul_of_nonneg_right
                                (Real.exp_le_one_iff.mpr (by
                                  have hmul : 0 ≤ a * x := mul_nonneg ha.le hx_pos.le
                                  nlinarith))
                                (inv_nonneg.mpr (sq_nonneg x))
                        _ = (x ^ 2)⁻¹ := by ring
      _ = R⁻¹ * (∫ x in R..B, a * Real.exp (-a * x)) +
            ∫ x in R..B, (x ^ 2)⁻¹ := by
            rw [intervalIntegral.integral_add]
            · rw [intervalIntegral.integral_const_mul]
            · exact (Continuous.intervalIntegrable (by fun_prop) R B).const_mul _
            · apply ContinuousOn.intervalIntegrable_of_Icc hRB
              exact (continuousOn_pow 2).inv₀ fun x hx =>
                pow_ne_zero 2 (hpos_Icc x hx).ne'
      _ = R⁻¹ * (Real.exp (-a * R) - Real.exp (-a * B)) + (R⁻¹ - B⁻¹) := by
            rw [intervalIntegral_exp_neg_mul_const_mul_self a R B,
              intervalIntegral_inv_sq_of_pos hR_pos hRB]
      _ ≤ R⁻¹ * 1 + R⁻¹ := by
            gcongr
            · exact (sub_le_self _ (Real.exp_pos _).le).trans
                (Real.exp_le_one_iff.mpr (by
                  have hmul : 0 ≤ a * R := mul_nonneg ha.le hR_pos.le
                  nlinarith))
            · exact sub_le_self _ (inv_nonneg.mpr hB_pos.le)
      _ = 2 * R⁻¹ := by ring
  rw [hrepr]
  calc
    ‖(-Real.exp (-a * B) * B⁻¹ * Real.cos B +
        Real.exp (-a * R) * R⁻¹ * Real.cos R) -
        ∫ x in R..B,
          (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
            Real.cos x‖
        ≤ ‖-Real.exp (-a * B) * B⁻¹ * Real.cos B +
            Real.exp (-a * R) * R⁻¹ * Real.cos R‖ +
            ‖∫ x in R..B,
              (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
                Real.cos x‖ := norm_sub_le _ _
    _ ≤ 2 * R⁻¹ + 2 * R⁻¹ := add_le_add hboundary hJ
    _ = 4 * R⁻¹ := by ring

theorem integral_Ioi_exp_neg_mul_sin (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x = 1 / (a ^ 2 + 1) := by
  let z : ℂ := (-(a : ℂ)) + Complex.I
  have hzre : z.re < 0 := by simp [z, ha]
  have hint : Integrable (fun x : ℝ => Complex.exp (z * x)) (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_exp_mul_complex_Ioi (a := z) hzre 0
  have him := integral_im (μ := volume.restrict (Set.Ioi 0)) hint
  have hpoint : (fun x : ℝ => Real.exp (-a * x) * Real.sin x) =
      fun x : ℝ => (Complex.exp (z * x)).im := by
    funext x
    simp [z, Complex.exp_im, mul_add, mul_comm]
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x
        = ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).im := by
          rw [hpoint]
    _ = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).im := by
          simpa using him
    _ = (-Complex.exp (z * (0 : ℝ)) / z).im := by
          rw [integral_exp_mul_complex_Ioi (a := z) hzre 0]
    _ = 1 / (a ^ 2 + 1) := by
          simp [z, Complex.div_im, Complex.normSq]
          ring

/-- The arctangent tail integral in the denominator shape used by the damped
sine computation. -/
theorem integral_Ioi_one_div_one_add_sq_eq_pi_div_two_sub_arctan (a : ℝ) :
    ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) = π / 2 - Real.arctan a := by
  simpa [one_div, add_comm] using integral_Ioi_inv_one_add_sq (i := a)

/-- For a positive lower endpoint, the arctangent tail integral is
`arctan (1/a)`. -/
theorem integral_Ioi_one_div_one_add_sq_eq_arctan_inv (a : ℝ) (ha : 0 < a) :
    ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) = Real.arctan a⁻¹ := by
  rw [integral_Ioi_one_div_one_add_sq_eq_pi_div_two_sub_arctan]
  exact (Real.arctan_inv_of_pos ha).symm

/-- The exponentially damped sinc function is integrable on the positive
half-line. -/
theorem integrableOn_exp_neg_mul_sinc (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi 0) := by
  change Integrable (fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
    (volume.restrict (Set.Ioi 0))
  have h_exp : Integrable (fun x : ℝ => Real.exp (-a * x))
      (volume.restrict (Set.Ioi 0)) := by
    change IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0)
    simpa [mul_comm] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
  refine h_exp.mono ?_ ?_
  · exact (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (volume.restrict (Set.Ioi 0)))
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one x)

/-- Uniform half-line tail control for the damped one-sided sinc integral. -/
theorem norm_integral_Ioi_exp_neg_mul_sinc_tail_le
    {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) :
    ‖∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi R) := by
    exact (integrableOn_exp_neg_mul_sinc a ha).mono_set (Set.Ioi_subset_Ioi hR_pos.le)
  have htend :=
    intervalIntegral_tendsto_integral_Ioi
      (f := fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
      (a := R) (b := fun B : ℝ => B) hint Filter.tendsto_id
  have hnorm :
      Filter.Tendsto
        (fun B : ℝ => ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖)
        Filter.atTop
        (nhds ‖∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x‖) :=
    continuous_norm.tendsto
      (∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x) |>.comp htend
  have hbound : ∀ᶠ B : ℝ in Filter.atTop,
      ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop R] with B hRB
    exact norm_intervalIntegral_exp_neg_mul_sinc_tail_le ha hR hRB
  exact le_of_tendsto hnorm hbound

/-- On a fixed finite window, damping tends back to the undamped sinc integral. -/
theorem tendsto_intervalIntegral_exp_neg_mul_sinc_nhdsGT_zero (R : ℝ) :
    Filter.Tendsto
      (fun a : ℝ => ∫ x in (0 : ℝ)..R, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ))
      (nhds (∫ x in (0 : ℝ)..R, Real.sinc x)) := by
  let f : ℝ → ℝ → ℝ := fun a x => Real.exp (-a * x) * Real.sinc x
  have hf : Continuous f.uncurry := by
    dsimp [f, Function.uncurry]
    fun_prop
  have hcont : Continuous fun a : ℝ => ∫ x in (0 : ℝ)..R, f a x :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := f) hf (0 : ℝ) R
  have ht : Filter.Tendsto (fun a : ℝ => ∫ x in (0 : ℝ)..R, f a x)
      (𝓝 (0 : ℝ)) (nhds (∫ x in (0 : ℝ)..R, f 0 x)) :=
    hcont.tendsto (0 : ℝ)
  have ht' : Filter.Tendsto (fun a : ℝ => ∫ x in (0 : ℝ)..R, f a x)
      (𝓝[>] (0 : ℝ)) (nhds (∫ x in (0 : ℝ)..R, f 0 x)) :=
    ht.mono_left nhdsWithin_le_nhds
  simpa [f] using ht'

/-- Abel comparison: any finite-window sinc limit agrees with the damped
half-line limit. -/
theorem tendsto_integral_Ioi_exp_neg_mul_sinc_of_tendsto_interval
    {L : ℝ}
    (hL : Filter.Tendsto
      (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x)
      Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun a : ℝ => ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ)) (nhds L) := by
  rw [Metric.tendsto_nhds] at hL ⊢
  intro ε hε
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hL_event : ∀ᶠ R : ℝ in Filter.atTop,
      dist (∫ x in (0 : ℝ)..R, Real.sinc x) L < η :=
    hL η hη
  have htail_lim : Filter.Tendsto (fun R : ℝ => 4 * R⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Filter.Tendsto
      (fun R : ℝ => 4 * R⁻¹) Filter.atTop (nhds (4 * 0)))
  have htail_event : ∀ᶠ R : ℝ in Filter.atTop, 4 * R⁻¹ < η :=
    htail_lim.eventually (gt_mem_nhds hη)
  have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R := Filter.eventually_ge_atTop 1
  rcases Filter.eventually_atTop.1 (hL_event.and (htail_event.and hlarge)) with ⟨R, hR⟩
  have hFR_dist : dist (∫ x in (0 : ℝ)..R, Real.sinc x) L < η := (hR R le_rfl).1
  have htail_small : 4 * R⁻¹ < η := (hR R le_rfl).2.1
  have hR_one : 1 ≤ R := (hR R le_rfl).2.2
  have hR_pos : 0 < R := zero_lt_one.trans_le hR_one
  have hfinite_event :
      ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
        dist (∫ x in (0 : ℝ)..R, Real.exp (-a * x) * Real.sinc x)
          (∫ x in (0 : ℝ)..R, Real.sinc x) < η :=
    Metric.tendsto_nhds.mp (tendsto_intervalIntegral_exp_neg_mul_sinc_nhdsGT_zero R) η hη
  filter_upwards [hfinite_event, self_mem_nhdsWithin] with a hfinite ha_mem
  have ha : 0 < a := ha_mem
  let g : ℝ → ℝ := fun x => Real.exp (-a * x) * Real.sinc x
  let D : ℝ := ∫ x in (0 : ℝ)..R, g x
  let F : ℝ := ∫ x in (0 : ℝ)..R, Real.sinc x
  let T : ℝ := ∫ x : ℝ in Set.Ioi R, g x
  let G : ℝ := ∫ x : ℝ in Set.Ioi 0, g x
  have hg0 : IntegrableOn g (Set.Ioi 0) := by
    dsimp [g]
    exact integrableOn_exp_neg_mul_sinc a ha
  have hgR : IntegrableOn g (Set.Ioi R) := by
    exact hg0.mono_set (Set.Ioi_subset_Ioi hR_pos.le)
  have hsplit : D + T = G := by
    dsimp [D, T, G, g]
    exact intervalIntegral.integral_interval_add_Ioi hg0 hgR
  have hfinite_norm : ‖D - F‖ < η := by
    simpa [D, F, g, Real.dist_eq, Real.norm_eq_abs] using hfinite
  have hFR_norm : ‖F - L‖ < η := by
    simpa [F, Real.dist_eq, Real.norm_eq_abs] using hFR_dist
  have htail_norm : ‖T‖ < η := by
    have htail_le : ‖T‖ ≤ 4 * R⁻¹ := by
      dsimp [T, g]
      exact norm_integral_Ioi_exp_neg_mul_sinc_tail_le ha hR_one
    exact lt_of_le_of_lt htail_le htail_small
  have htriangle :
      ‖G - L‖ ≤ ‖D - F‖ + ‖T‖ + ‖F - L‖ := by
    calc
      ‖G - L‖ = ‖(D - F) + T + (F - L)‖ := by
        rw [← hsplit]
        congr 1
        ring
      _ ≤ ‖(D - F) + T‖ + ‖F - L‖ := norm_add_le _ _
      _ ≤ (‖D - F‖ + ‖T‖) + ‖F - L‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (norm_add_le (D - F) T) ‖F - L‖
      _ = ‖D - F‖ + ‖T‖ + ‖F - L‖ := by ring
  have hsum : ‖D - F‖ + ‖T‖ + ‖F - L‖ < ε := by
    have hsum_eta : ‖D - F‖ + ‖T‖ + ‖F - L‖ < η + η + η := by
      nlinarith [hfinite_norm, htail_norm, hFR_norm]
    have heta : η + η + η < ε := by
      dsimp [η]
      nlinarith [hε]
    exact lt_trans hsum_eta heta
  have hG : dist G L < ε := by
    simpa [Real.dist_eq, Real.norm_eq_abs] using lt_of_le_of_lt htriangle hsum
  simpa [G, g] using hG

/-- Positive half-line exponential tail with a variable decay constant. -/
theorem integral_Ioi_exp_neg_mul_const (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) = Real.exp (-a * x) / x := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith : -x < 0) a
  calc
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x)
        = ∫ u : ℝ in Set.Ioi a, Real.exp ((-x) * u) := by
          congr with u
          ring_nf
    _ = Real.exp (-a * x) / x := by
          rw [h]
          field_simp [hx.ne']

/-- The pointwise representation of the damped sinc kernel by an exponential
tail integral. -/
theorem integral_Ioi_exp_neg_mul_const_mul_sin (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x =
      Real.exp (-a * x) * Real.sinc x := by
  rw [integral_mul_const]
  rw [integral_Ioi_exp_neg_mul_const a x hx]
  rw [Real.sinc_of_ne_zero hx.ne']
  field_simp [hx.ne']

/-- Evaluation of the damped sinc integral from the one remaining Fubini swap.
The hypothesis is the exact product-integrability/swap term left to prove. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_integral_swap
    (a : ℝ) (ha : 0 < a)
    (hswap :
      (∫ x : ℝ in Set.Ioi 0,
        ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x) =
      ∫ u : ℝ in Set.Ioi a,
        ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ := by
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x
        = ∫ x : ℝ in Set.Ioi 0,
            ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact (integral_Ioi_exp_neg_mul_const_mul_sin a x hx).symm
    _ = ∫ u : ℝ in Set.Ioi a,
          ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x := hswap
    _ = ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact integral_Ioi_exp_neg_mul_sin u (lt_trans ha hu)
    _ = Real.arctan a⁻¹ := integral_Ioi_one_div_one_add_sq_eq_arctan_inv a ha

/-- The standard Fubini theorem gives the damped-sinc swap once the product
kernel is integrable. -/
theorem integral_Ioi_exp_neg_mul_sinc_integral_swap_of_integrable
    (a : ℝ)
    (hprod : Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a)))) :
    (∫ x : ℝ in Set.Ioi 0,
      ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x) =
    ∫ u : ℝ in Set.Ioi a,
      ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x := by
  simpa [Function.uncurry] using integral_integral_swap hprod

/-- Evaluation of the damped sinc integral from product-integrability of the
Fubini kernel. This is the canonical remaining input for the regularized sinc
route. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_product_integrable
    (a : ℝ) (ha : 0 < a)
    (hprod : Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a)))) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ :=
  integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_integral_swap a ha
    (integral_Ioi_exp_neg_mul_sinc_integral_swap_of_integrable a hprod)

/-- Product-integrability of the damped sine kernel on `(0,∞) × (a,∞)`.
The proof integrates the `u`-tail first and bounds the inner norm by
`exp (-a*x)` using `|sin x| ≤ x` for `x > 0`. -/
theorem integrable_exp_neg_mul_sin_prod_Ioi (a : ℝ) (ha : 0 < a) :
    Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a))) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  let ν := volume.restrict (Set.Ioi a)
  change Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν)
  have hsm : AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν) := by
    exact (by fun_prop : AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν))
  rw [integrable_prod_iff hsm]
  constructor
  · dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Integrable (fun u : ℝ => Real.exp (-u * x) * Real.sin x) ν
    have h_exp : Integrable (fun u : ℝ => Real.exp (-u * x)) ν := by
      dsimp [ν]
      change IntegrableOn (fun u : ℝ => Real.exp (-u * x)) (Set.Ioi a)
      simpa [mul_comm] using integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) a
    exact h_exp.mul_const (Real.sin x)
  · have h_exp_a : Integrable (fun x : ℝ => Real.exp (-a * x)) μ := by
      dsimp [μ]
      change IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0)
      simpa [mul_comm] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
    refine h_exp_a.mono ?_ ?_
    · exact hsm.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have h_exp_x : Integrable (fun y : ℝ => Real.exp (-y * x)) ν := by
        dsimp [ν]
        change IntegrableOn (fun y : ℝ => Real.exp (-y * x)) (Set.Ioi a)
        simpa [mul_comm] using integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx0) a
      have h_lhs : Integrable
          (fun y : ℝ => ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖) ν := by
        simpa [Function.uncurry] using (h_exp_x.mul_const (Real.sin x)).norm
      have h_rhs : Integrable (fun y : ℝ => Real.exp (-y * x) * x) ν :=
        h_exp_x.mul_const x
      calc
        ‖∫ y : ℝ, ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖ ∂ν‖
            = ∫ y : ℝ, ‖Function.uncurry
                (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖ ∂ν := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              exact integral_nonneg fun y => norm_nonneg _
        _ ≤ ∫ y : ℝ, Real.exp (-y * x) * x ∂ν := by
              refine integral_mono_ae h_lhs h_rhs ?_
              filter_upwards with y
              rw [Function.uncurry, Real.norm_eq_abs, abs_mul,
                abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_left
                (by simpa [abs_of_pos hx0] using (Real.abs_sin_le_abs (x := x)))
                (Real.exp_pos _).le
        _ = Real.exp (-a * x) := by
              dsimp [ν]
              rw [integral_mul_const]
              rw [integral_Ioi_exp_neg_mul_const a x hx0]
              field_simp [hx0.ne']
        _ = ‖Real.exp (-a * x)‖ := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The Laplace-regularized one-sided sinc integral. This is the Abelian input
for the classical `∫₀ᴬ sinc -> π/2` route. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ :=
  integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_product_integrable a ha
    (integrable_exp_neg_mul_sin_prod_Ioi a ha)

/-- Abel limit of the Laplace-regularized sinc integral as the damping tends
to zero from the right. -/
theorem tendsto_integral_Ioi_exp_neg_mul_sinc_nhdsGT_zero :
    Filter.Tendsto
      (fun a : ℝ => ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ)) (𝓝 (π / 2 : ℝ)) := by
  have hinv : Filter.Tendsto (fun a : ℝ => a⁻¹) (𝓝[>] (0 : ℝ)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have harctan : Filter.Tendsto (fun a : ℝ => Real.arctan a⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (π / 2 : ℝ)) :=
    (Real.tendsto_arctan_atTop.comp hinv).mono_right nhdsWithin_le_nhds
  refine harctan.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv a ha).symm

/-- The classical one-sided sinc integral tends to `π / 2`. -/
theorem tendsto_intervalIntegral_real_sinc_atTop :
    Filter.Tendsto
      (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x)
      Filter.atTop (nhds (π / 2 : ℝ)) := by
  rcases exists_tendsto_intervalIntegral_real_sinc_atTop with ⟨L, hL⟩
  have hAbelL := tendsto_integral_Ioi_exp_neg_mul_sinc_of_tendsto_interval hL
  have hlim : L = π / 2 :=
    tendsto_nhds_unique hAbelL tendsto_integral_Ioi_exp_neg_mul_sinc_nhdsGT_zero
  simpa [hlim] using hL

end

end LeanLab.PNTPort.Perron

