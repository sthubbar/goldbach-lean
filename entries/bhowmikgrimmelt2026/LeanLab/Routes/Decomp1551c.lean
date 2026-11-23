module

public import Mathlib
public import LeanLab.PNTPort.StrongPNT.ZetaBounds
public import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian
public import LeanLab.ChirreHagen2025.SmoothTheorem2

/-!
Unit U-1551, track T1, DECOMPOSE, run 20261026T1219Z-15327, 2026-10-26. PALOMAR line I5171.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Decomposition of the input `SmoothT2.Ordinates14 gZ` of
`LeanLab.Routes.U1508.goldbach_445_hsw_gZ` under RH: every nontrivial zero of ζ has
`|Im ρ| ≥ 14`. Under RH a zero is `1/2 + iγ`; by `riemannZeta_conj` one may take `γ ≥ 0`; so it
suffices that `ζ(1/2 + it) ≠ 0` for `0 ≤ t < 14`. This follows from the Euler-Maclaurin
approximant `EM10` with `N = 10` and two Bernoulli corrections, Edwards, Riemann's Zeta
Function 1974, section 6.4: its remainder is below `1/100` on the segment, LEAVES
`em10_remainder` and `rem_small`, while `‖EM10(1/2 + it)‖ ≥ 1/20` on `[0, 14]`, LEAVES
`em10_lower_a`, `em10_lower_b`, `em10_lower_c`, a finite certified computation. A float check
with mpmath at 30 digits on a grid of step 0.001 gives the minimum `0.1056` at `t = 14`, and
the remainder bound `0.0051` at `t = 14`.

ASSEMBLY `ordinates14_gZ_of_RH`, CONDITIONAL ON the five leaves.
-/

@[expose] public section

namespace LeanLab.Routes.Decomp1551c

open Complex MeasureTheory Set Filter
open scoped Topology
open scoped QuadraticAlgebra
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx re_half_of_RH)

local notation "ζ" => riemannZeta

/-- The Euler-Maclaurin approximant of `ζ(s)` with `N = 10` and the Bernoulli terms `B₂`, `B₄`:
`Σ_{n<10} n^{-s} + 10^{1-s}/(s-1) + 10^{-s}/2 + s 10^{-s-1}/12 - s(s+1)(s+2) 10^{-s-3}/720`. -/
noncomputable def EM10 (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Ico (1 : ℕ) 10, ((n : ℕ) : ℂ) ^ (-s)) + (10 : ℂ) ^ (1 - s) / (s - 1) + (10 : ℂ) ^ (-s) / 2
    + s * (10 : ℂ) ^ (-s - 1) / 12 - s * (s + 1) * (s + 2) * (10 : ℂ) ^ (-s - 3) / 720

/-- LEAF. Unit U-1551. Edwards 1974, section 6.4, Euler-Maclaurin summation for `ζ` with
`N = 10` and `m = 2`: the remainder `-s(s+1)(s+2)(s+3)/4! ∫_N^∞ B̃₄(x) x^{-s-4} dx`, with
`|B̃₄| ≤ 1/30`, satisfies `|ζ(s) - EM10(s)| ≤ |s(s+1)(s+2)(s+3)| 10^{-σ-3} / (720 (σ+3))`
for `σ = Re s > 0`, `s ≠ 1`. The lab's port `PNTPort/StrongPNT/EulerMaclaurin.lean` has the
first-order summation formula. -/
theorem em10_remainder (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖ζ s - EM10 s‖ ≤
      ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (10 : ℝ) ^ (-(s.re + 3)) / (720 * (s.re + 3)) := by
  have hstep (u v : ℝ → ℂ) (C D : ℝ) (hu : Continuous u)
      (hv : AEStronglyMeasurable v) (hbu : ∀ x, ‖u x‖ ≤ C) (hbv : ∀ x, ‖v x‖ ≤ D)
      (hd : ∀ x ∉ Set.range (fun n : ℤ => (n : ℝ)), HasDerivAt u (v x) x)
      (w : ℂ) (hw : w.re < -1) :
      (∫ x in Set.Ioi (10 : ℝ), v x * (x : ℂ) ^ w) =
        -u 10 * (10 : ℂ) ^ w - w *
          (∫ x in Set.Ioi (10 : ℝ), u x * (x : ℂ) ^ (w - 1)) := by
    have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
    have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ w) (Ioi 10) :=
      integrableOn_Ioi_cpow_of_lt hw (by norm_num)
    have hi' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1)) (Ioi 10) :=
      integrableOn_Ioi_cpow_of_lt (by simp only [sub_re, one_re]; linarith) (by norm_num)
    have hiv : IntegrableOn (fun x : ℝ => v x * (x : ℂ) ^ w) (Ioi 10) :=
      hi.bdd_mul (hv.mono_measure Measure.restrict_le_self) (ae_of_all _ hbv)
    have hiu : IntegrableOn (fun x : ℝ => u x * (x : ℂ) ^ (w - 1)) (Ioi 10) :=
      hi'.bdd_mul hu.aestronglyMeasurable (ae_of_all _ hbu)
    let F : ℝ → ℂ := fun x => u x * (x : ℂ) ^ w
    let F' : ℝ → ℂ := fun x => v x * (x : ℂ) ^ w + w * (u x * (x : ℂ) ^ (w - 1))
    have hFi : IntegrableOn F' (Ioi 10) := hiv.add (hiu.const_mul w)
    have hF (b : ℝ) (hb : 10 ≤ b) : (∫ x in (10 : ℝ)..b, F' x) = F b - F 10 := by
      apply integral_eq_of_hasDerivAt_off_countable_of_le F F' hb
        (Set.countable_range (fun n : ℤ => (n : ℝ)))
      · apply hu.continuousOn.mul
        intro x hx
        exact (hasDerivAt_ofReal_cpow_const (by linarith [hx.1] : x ≠ 0) hw0).continuousAt.continuousWithinAt
      · intro x hx
        convert (hd x hx.2).mul (hasDerivAt_ofReal_cpow_const
          (by linarith [hx.1.1] : x ≠ 0) hw0) using 1
        dsimp [F, F']
        ring
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
        exact hFi.mono_set Ioc_subset_Ioi_self
    have hlim : Tendsto F atTop (𝓝 0) := by
      have hpow : Tendsto (fun x : ℝ => C * x ^ w.re) atTop (𝓝 0) := by
        convert (tendsto_rpow_neg_atTop (by linarith : 0 < -w.re)).const_mul C using 1 <;> simp
      apply squeeze_zero_norm' ?_ hpow
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      dsimp [F]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      exact mul_le_mul_of_nonneg_right (hbu x) (Real.rpow_nonneg hx.le _)
    have hlimint := intervalIntegral_tendsto_integral_Ioi 10 hFi tendsto_id
    have hlimend := hlim.sub (tendsto_const_nhds (x := F 10))
    have hid : (∫ x in Set.Ioi (10 : ℝ), F' x) = -F 10 := by
      have hlimint' : Tendsto (fun b : ℝ => F b - F 10) atTop
          (𝓝 (∫ x in Set.Ioi (10 : ℝ), F' x)) := by
        apply hlimint.congr'
        filter_upwards [eventually_ge_atTop (10 : ℝ)] with b hb
        exact hF b hb
      simpa using tendsto_nhds_unique hlimint' hlimend
    dsimp [F', F] at hid
    rw [integral_add hiv (hiu.const_mul w), integral_const_mul] at hid
    linear_combination hid
  have hfract (x : ℝ) (hx : x ∉ Set.range (fun n : ℤ => (n : ℝ))) :
      HasDerivAt Int.fract 1 x := by
    have hx' : (⌊x⌋ : ℝ) < x := by
      refine lt_of_le_of_ne (Int.floor_le x) ?_
      intro h
      exact hx ⟨⌊x⌋, h⟩
    have he : Int.fract =ᶠ[𝓝 x] (fun y : ℝ => y - (⌊x⌋ : ℝ)) := by
      filter_upwards [Ioo_mem_nhds hx' (Int.lt_floor_add_one x)] with y hy
      change y - (⌊y⌋ : ℝ) = y - (⌊x⌋ : ℝ)
      have hf : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
      rw [hf]
    exact ((hasDerivAt_id x).sub_const (⌊x⌋ : ℝ)).congr_of_eventuallyEq he
  let B1 : ℝ → ℝ := fun y => y - 1 / 2
  let B2 : ℝ → ℝ := fun y => y ^ 2 / 2 - y / 2 + 1 / 12
  let B3 : ℝ → ℝ := fun y => y ^ 3 / 6 - y ^ 2 / 4 + y / 12
  let B4 : ℝ → ℝ := fun y => y ^ 4 / 24 - y ^ 3 / 12 + y ^ 2 / 24 - 1 / 720
  have hc2 : Continuous (fun x : ℝ => (B2 (Int.fract x) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((show ContinuousOn B2 (Icc 0 1) from by dsimp [B2]; fun_prop).comp_fract'' (by norm_num [B2]))
  have hc3 : Continuous (fun x : ℝ => (B3 (Int.fract x) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((show ContinuousOn B3 (Icc 0 1) from by dsimp [B3]; fun_prop).comp_fract'' (by norm_num [B3]))
  have hc4 : Continuous (fun x : ℝ => (B4 (Int.fract x) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((show ContinuousOn B4 (Icc 0 1) from by dsimp [B4]; fun_prop).comp_fract'' (by norm_num [B4]))
  have hb1 (x : ℝ) : ‖(B1 (Int.fract x) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp [B1]
    constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]
  have hb2 (x : ℝ) : ‖(B2 (Int.fract x) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h0 := Int.fract_nonneg x
    have h1 := (Int.fract_lt_one x).le
    have h2 := pow_le_one₀ h0 h1 (n := 2)
    dsimp [B2]
    constructor <;> nlinarith [sq_nonneg (Int.fract x)]
  have hb3 (x : ℝ) : ‖(B3 (Int.fract x) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h0 := Int.fract_nonneg x
    have h1 := (Int.fract_lt_one x).le
    have h2 := pow_le_one₀ h0 h1 (n := 2)
    have h3 := pow_le_one₀ h0 h1 (n := 3)
    dsimp [B3]
    constructor <;> nlinarith [pow_nonneg h0 3, sq_nonneg (Int.fract x)]
  have hb4 (x : ℝ) : ‖(B4 (Int.fract x) : ℂ)‖ ≤ 1 / 720 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h0 := Int.fract_nonneg x
    have h1 := (Int.fract_lt_one x).le
    have hp0 : 0 ≤ Int.fract x * (1 - Int.fract x) := mul_nonneg h0 (by linarith)
    have hp1 : Int.fract x * (1 - Int.fract x) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
    have hp2 : (Int.fract x * (1 - Int.fract x)) ^ 2 ≤ 1 / 16 := by
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
    dsimp [B4]
    constructor <;> nlinarith [sq_nonneg (Int.fract x * (1 - Int.fract x))]
  have hd2 (x : ℝ) (hx : x ∉ Set.range (fun n : ℤ => (n : ℝ))) :
      HasDerivAt (fun x : ℝ => (B2 (Int.fract x) : ℂ)) (B1 (Int.fract x)) x := by
    convert ((((hfract x hx).pow 2).div_const 2).sub ((hfract x hx).div_const 2)).add_const (1 / 12) |>.ofReal_comp using 1
    dsimp [B1, B2]
    push_cast
    ring
  have hd3 (x : ℝ) (hx : x ∉ Set.range (fun n : ℤ => (n : ℝ))) :
      HasDerivAt (fun x : ℝ => (B3 (Int.fract x) : ℂ)) (B2 (Int.fract x)) x := by
    convert ((((hfract x hx).pow 3).div_const 6).sub (((hfract x hx).pow 2).div_const 4)).add ((hfract x hx).div_const 12) |>.ofReal_comp using 1
    dsimp [B2, B3]
    push_cast
    ring
  have hd4 (x : ℝ) (hx : x ∉ Set.range (fun n : ℤ => (n : ℝ))) :
      HasDerivAt (fun x : ℝ => (B4 (Int.fract x) : ℂ)) (B3 (Int.fract x)) x := by
    convert (((((hfract x hx).pow 4).div_const 24).sub (((hfract x hx).pow 3).div_const 12)).add (((hfract x hx).pow 2).div_const 24)).sub_const (1 / 720) |>.ofReal_comp using 1
    dsimp [B3, B4]
    push_cast
    ring
  have hm1 : AEStronglyMeasurable (fun x : ℝ => (B1 (Int.fract x) : ℂ)) := by
    dsimp [B1]
    fun_prop
  have hstep2 := hstep _ _ 1 1 hc2 hm1 hb2 hb1 hd2 (-s - 1) (by simp; linarith)
  have hstep3 := hstep _ _ 1 1 hc3 hc2.aestronglyMeasurable hb3 hb2 hd3 (-s - 2) (by simp; linarith)
  have hstep4 := hstep _ _ (1 / 720) 1 hc4 hc3.aestronglyMeasurable hb4 hb3 hd4 (-s - 3) (by simp; linarith)
  norm_num only [Int.fract_ofNat, B2, B3, B4, zero_pow, Nat.cast_zero, zero_div, sub_zero, zero_sub,
    zero_add, add_zero, ofReal_zero, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, neg_zero, zero_mul] at hstep2 hstep3 hstep4
  let I1 : ℂ := ∫ x in Ioi (10 : ℝ), (B1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 1)
  let I2 : ℂ := ∫ x in Ioi (10 : ℝ), (B2 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 2)
  let I3 : ℂ := ∫ x in Ioi (10 : ℝ), (B3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)
  let I4 : ℂ := ∫ x in Ioi (10 : ℝ), (B4 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 4)
  have e2 : I1 = -(10 : ℂ) ^ (-s - 1) / 12 + (s + 1) * I2 := by
    have he : -s - 1 - 1 = -s - 2 := by ring
    rw [he] at hstep2
    linear_combination hstep2
  have e3 : I2 = (s + 2) * I3 := by
    have he : -s - 2 - 1 = -s - 3 := by ring
    rw [he] at hstep3
    linear_combination hstep3
  have e4 : I3 = (10 : ℂ) ^ (-s - 3) / 720 + (s + 3) * I4 := by
    have he : -s - 3 - 1 = -s - 4 := by ring
    rw [he] at hstep4
    linear_combination hstep4
  have hz0 := Zeta0EqZeta (N := 10) (by norm_num) hs hs1
  rw [riemannZeta0_apply] at hz0
  norm_num only [Nat.cast_ofNat] at hz0
  have hz : riemannZeta s =
      (∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-s)) +
      (10 : ℂ) ^ (1 - s) / (s - 1) + (10 : ℂ) ^ (-s) / 2 - s * I1 := by
    have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have hsum : (∑ n ∈ Finset.range (10 + 1), 1 / (n : ℂ) ^ s) =
        (∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-s)) + (10 : ℂ) ^ (-s) := by
      simp_rw [one_div_cpow_eq_cpow_neg]
      rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ (by norm_num : 0 < 10)]
      norm_num [hs0]
    rw [hsum] at hz0
    have hint : (∫ x in Ioi (10 : ℝ), (↑⌊x⌋ + 1 / 2 - x : ℂ) * (x : ℂ) ^ (-(s + 1))) = -I1 := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp [B1]
      push_cast
      rw [show -(s + 1) = -s - 1 by ring]
      rw [Int.fract]
      push_cast
      ring
    rw [hint] at hz0
    have hden : 1 - s = -(s - 1) := by ring
    simp only [hden, div_neg, neg_div, neg_neg] at hz0
    rw [show -(s - 1) = 1 - s by ring] at hz0
    linear_combination -hz0
  have hid : riemannZeta s - EM10 s = -(s * (s + 1) * (s + 2) * (s + 3)) * I4 := by
    rw [hz, e2, e3, e4]
    dsimp [EM10]
    ring
  have hi_major : IntegrableOn (fun x : ℝ => (1 / 720 : ℝ) * x ^ (-s.re - 4)) (Ioi 10) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 4 < -1) (by norm_num)).const_mul _
  have hbound : ‖I4‖ ≤ (∫ x in Ioi (10 : ℝ), (1 / 720 : ℝ) * x ^ (-s.re - 4)) := by
    apply norm_integral_le_of_norm_le hi_major
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by exact lt_trans (by norm_num : (0 : ℝ) < 10) hx : 0 < x)]
    simp only [sub_re, neg_re, re_ofNat]
    exact mul_le_mul_of_nonneg_right (hb4 x) (Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 10) hx.le) _)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 4 < -1) (by norm_num)] at hbound
  have he : -s.re - 4 + 1 = -(s.re + 3) := by ring
  rw [he] at hbound
  have hbound' : ‖I4‖ ≤ (10 : ℝ) ^ (-(s.re + 3)) / (720 * (s.re + 3)) := by
    convert hbound using 1
    field_simp [show s.re + 3 ≠ 0 by linarith]
  rw [hid, norm_mul, norm_neg]
  convert mul_le_mul_of_nonneg_left hbound' (norm_nonneg (s * (s + 1) * (s + 2) * (s + 3))) using 1
  ring

/-- LEAF. Unit U-1551. Arithmetic for the remainder of `em10_remainder` on the half line
segment: for `s = 1/2 + it`, `0 ≤ t ≤ 14`,
`|s(s+1)(s+2)(s+3)| 10^{-7/2} / (720 · 7/2) ≤ 1/100`; at `t = 14` the left side is `0.0051`. -/
theorem rem_small (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    ‖((1 / 2 : ℂ) + t * I) * ((1 / 2 : ℂ) + t * I + 1) * ((1 / 2 : ℂ) + t * I + 2) *
        ((1 / 2 : ℂ) + t * I + 3)‖ * (10 : ℝ) ^ (-((1 / 2 : ℝ) + 3)) / (720 * ((1 / 2 : ℝ) + 3))
      ≤ 1 / 100 := by
  have hnorm (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 7 / 2) :
      ‖(a : ℂ) + t * I‖ ≤ 15 := by
    have hsq : ‖(a : ℂ) + t * I‖ ^ 2 = a ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [pow_two]
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha),
      mul_nonneg ht0 (sub_nonneg.mpr ht), norm_nonneg ((a : ℂ) + t * I)]
  have h0 : ‖(1 / 2 : ℂ) + t * I‖ ≤ 15 := by
    simpa using hnorm (1 / 2) (by norm_num) (by norm_num)
  have h1 : ‖(1 / 2 : ℂ) + t * I + 1‖ ≤ 15 := by
    convert hnorm (3 / 2) (by norm_num) (by norm_num) using 1
    congr 1
    push_cast
    ring
  have h2 : ‖(1 / 2 : ℂ) + t * I + 2‖ ≤ 15 := by
    convert hnorm (5 / 2) (by norm_num) (by norm_num) using 1
    congr 1
    push_cast
    ring
  have h3 : ‖(1 / 2 : ℂ) + t * I + 3‖ ≤ 15 := by
    convert hnorm (7 / 2) (by norm_num) (by norm_num) using 1
    congr 1
    push_cast
    ring
  have hprod :
      ‖((1 / 2 : ℂ) + t * I) * ((1 / 2 : ℂ) + t * I + 1) *
        ((1 / 2 : ℂ) + t * I + 2) * ((1 / 2 : ℂ) + t * I + 3)‖ ≤ 50625 := by
    simp only [norm_mul]
    calc
      ‖(1 / 2 : ℂ) + t * I‖ * ‖(1 / 2 : ℂ) + t * I + 1‖ *
          ‖(1 / 2 : ℂ) + t * I + 2‖ * ‖(1 / 2 : ℂ) + t * I + 3‖
          ≤ 15 * 15 * 15 * 15 := by gcongr
      _ = 50625 := by norm_num
  have hsqrt : 3 ≤ Real.sqrt 10 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have hp : (10 : ℝ) ^ ((1 / 2 : ℝ) + 3) = 1000 * Real.sqrt 10 := by
    rw [Real.rpow_add (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
    ring
  have hpow : (10 : ℝ) ^ (-((1 / 2 : ℝ) + 3)) ≤ 1 / 3000 := by
    rw [Real.rpow_neg (by norm_num), hp, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 720 * (1 / 2 + 3))).2
  have hmul := mul_le_mul hprod hpow (by positivity) (by norm_num : (0 : ℝ) ≤ 50625)
  norm_num at hmul ⊢
  linarith

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 200000 in
/-- LEAF. Unit U-1551. Finite certified computation, first piece: `|EM10(1/2 + it)| ≥ 1/20`
for `0 ≤ t ≤ 7`; float minimum `0.526`. A grid with a Lipschitz bound for `EM10` suffices. -/
theorem em10_lower_a (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 7) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  let qr : ℕ → ℚ := fun n =>
    match n with
    | 1 => 0
    | 2 => 693147 / 1000000
    | 3 => 1098612 / 1000000
    | 4 => 1386294 / 1000000
    | 5 => 1609437 / 1000000
    | 6 => 1791759 / 1000000
    | 7 => 1945910 / 1000000
    | 8 => 2079441 / 1000000
    | 9 => 2197224 / 1000000
    | 10 => 2302585 / 1000000
    | _ => 0
  let q : ℕ → ℝ := fun n => (qr n : ℝ)
  have hlog7 : |Real.log 7 - q 7| ≤ 1 / 1000000 := by
    have hh := Real.abs_log_sub_add_sum_range_le (x := 1 / 8) (by norm_num) 10
    have he : Real.log (1 - (1 / 8 : ℝ)) = Real.log 7 - 3 * Real.log 2 := by
      rw [show (1 - (1 / 8 : ℝ)) = 7 / 8 by norm_num,
        Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
      have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [he8]
    rw [he] at hh
    norm_num [Finset.sum_range_succ, q, qr] at hh ⊢
    rw [abs_le] at hh ⊢
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  norm_num only [q, qr] at hlog7
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by norm_num [← Real.log_mul]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogs (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) :
      |Real.log n - q n| ≤ 1 / 1000000 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, hlog4, hlog6, hlog8, hlog9, Real.log_ten_eq, qr]
    all_goals rw [abs_le]
    all_goals constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9,
      (abs_le.mp hlog7).1, (abs_le.mp hlog7).2]
  let s : ℝ → ℂ := fun v => (1 / 2 : ℂ) + v * I
  let T : ℕ → ℝ → ℝ → ℂ := fun n a v =>
    ∑ k ∈ Finset.range 128, ((((a : ℂ) - s v) * (q n : ℂ)) ^ k / (k.factorial : ℂ))
  have hq (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) : 0 ≤ q n ∧ q n ≤ 5 / 2 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, qr]
  have hfac (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) : ‖(a : ℂ) - (s v)‖ ≤ 15 := by
    have hsq : ‖(a : ℂ) - (s v)‖ ^ 2 = (a - 1 / 2) ^ 2 + v ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num [s]
      ring
    have ha2 : a ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg (show 0 ≤ a + 3 by linarith) (show 0 ≤ 3 - a by linarith)]
    nlinarith [norm_nonneg ((a : ℂ) - (s v)), mul_nonneg hv0 (sub_nonneg.mpr hv)]
  have hp (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - (s v))‖ ≤ 4 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    norm_num [s]
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ ≤ (10 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn10) (by norm_num)
      _ ≤ 4 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have happ (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - (s v)) - T n a v‖ ≤ 1 / 8000 := by
    let z : ℂ := ((a : ℂ) - (s v)) * (Real.log n : ℂ)
    let w : ℂ := ((a : ℂ) - (s v)) * (q n : ℂ)
    have hez : Complex.exp z = (n : ℂ) ^ ((a : ℂ) - (s v)) := by
      have hn0 : (n : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
      rw [Complex.cpow_def_of_ne_zero hn0]
      dsimp [z]
      rw [← Complex.natCast_log]
      congr 1
      ring
    have hz : ‖Complex.exp z‖ ≤ 4 := by rw [hez]; exact hp v hv0 hv n hn a ha1
    have hzw : ‖w - z‖ ≤ 15 / 1000000 := by
      have he : w - z = ((a : ℂ) - (s v)) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      calc
        _ ≤ 15 * (1 / 1000000) := mul_le_mul (hfac v hv0 hv a ha ha1) (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    have hw : ‖w‖ ≤ 40 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq n hn).1]
      calc
        _ ≤ 15 * (5 / 2) := mul_le_mul (hfac v hv0 hv a ha ha1) (hq n hn).2 (hq n hn).1 (by norm_num)
        _ ≤ _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 8 * (15 / 1000000) := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 1
        ring
      rw [norm_sub_rev, he, norm_mul]
      have hh := Complex.norm_exp_sub_one_le (x := w - z) (by linarith : ‖w - z‖ ≤ 1)
      have hhd : ‖Complex.exp (w - z) - 1‖ ≤ 2 * (15 / 1000000) :=
        hh.trans (mul_le_mul_of_nonneg_left hzw (by norm_num))
      calc
        ‖Complex.exp z‖ * ‖Complex.exp (w - z) - 1‖ ≤ 4 * (2 * (15 / 1000000)) := by gcongr
        _ = 8 * (15 / 1000000) := by norm_num
    have hTaylor : ‖Complex.exp w - T n a v‖ ≤ 1 / 10000000 := by
      have hh := Complex.exp_bound' (x := w) (n := 128) (by norm_num; linarith)
      apply hh.trans
      calc
        _ ≤ (40 : ℝ) ^ 128 / (128 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    rw [← hez]
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - T n a v)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - T n a v‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  let Off : ℕ → ℝ → ℂ := fun n u => ∑ k ∈ Finset.range 12,
    (((-I) * (q n : ℂ)) ^ k / (k.factorial : ℂ)) * (u : ℂ) ^ k
  have hOff (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (u : ℝ) (hu : |u| ≤ 1 / 2) :
      ‖Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ)) - Off n u‖ ≤ 1 / 500000 := by
    let z : ℂ := -I * (u : ℂ) * (Real.log n : ℂ)
    let w : ℂ := -I * (u : ℂ) * (q n : ℂ)
    have hz : ‖Complex.exp z‖ = 1 := by rw [Complex.norm_exp]; simp only [z, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, sub_self, add_zero, zero_add, neg_zero, Real.exp_zero]
    have hzw : ‖w - z‖ ≤ 1 / 2000000 := by
      have he : w - z = -I * (u : ℂ) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]; push_cast; ring
      rw [he, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
      calc
        |u| * |Real.log n - q n| ≤ (1 / 2) * (1 / 1000000) :=
          mul_le_mul hu (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hw : ‖w‖ ≤ 5 / 4 := by
      dsimp [w]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hq n hn).1]
      calc
        |u| * q n ≤ (1 / 2) * (5 / 2) := mul_le_mul hu (hq n hn).2 (hq n hn).1 (by norm_num)
        _ = _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 1 / 1000000 := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; ring
      rw [norm_sub_rev, he, norm_mul, hz, one_mul]
      exact (Complex.norm_exp_sub_one_le (by linarith : ‖w - z‖ ≤ 1)).trans
        (by linarith)
    have hTaylor : ‖Complex.exp w - ∑ k ∈ Finset.range 12, w ^ k / (k.factorial : ℂ)‖ ≤ 1 / 1000000 := by
      apply (Complex.exp_bound' (x := w) (n := 12) (by norm_num; linarith)).trans
      calc
        ‖w‖ ^ 12 / (12 : ℕ).factorial * 2 ≤ (5 / 4 : ℝ) ^ 12 / (12 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    have hpoly : (∑ k ∈ Finset.range 12, w ^ k / (k.factorial : ℂ)) = Off n u := by
      dsimp only [Off]
      apply Finset.sum_congr rfl
      intro k hk
      have he : w = ((-I) * (q n : ℂ)) * (u : ℂ) := by dsimp [w]; ring
      rw [he, mul_pow]
      ring
    rw [hpoly] at hTaylor
    change ‖Complex.exp z - Off n u‖ ≤ _
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - Off n u)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - Off n u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hOffnorm (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (u : ℝ) (hu : |u| ≤ 1 / 2) :
      ‖Off n u‖ ≤ 2 := by
    have hz : ‖Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, sub_self, add_zero, zero_add, neg_zero, Real.exp_zero]
    have hh := norm_sub_norm_le (Off n u) (Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ)))
    rw [norm_sub_rev, hz] at hh
    have ho := hOff n hn u hu
    linarith
  let A : ℕ → ℝ → ℝ → ℝ → ℂ := fun n a v u => T n a v * Off n u
  have hA (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (u : ℝ) (hu : |u| ≤ 1 / 2)
      (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - s (v + u)) - A n a v u‖ ≤ 1 / 3000 := by
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
    let z : ℂ := -I * (u : ℂ) * (Real.log n : ℂ)
    have he : (n : ℂ) ^ ((a : ℂ) - s (v + u)) =
        (n : ℂ) ^ ((a : ℂ) - s v) * Complex.exp z := by
      rw [show (a : ℂ) - s (v + u) = ((a : ℂ) - s v) + (-I * (u : ℂ)) by dsimp [s]; push_cast; ring,
        Complex.cpow_add _ _ hn0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
      dsimp [z]
      congr 1
      ring
    rw [he]
    dsimp only [A]
    have hc := happ v hv0 hv n hn a ha ha1
    have hcNorm := hp v hv0 hv n hn a ha1
    have ho := hOff n hn u hu
    have hoNorm := hOffnorm n hn u hu
    calc
      _ = ‖(n : ℂ) ^ ((a : ℂ) - s v) * (Complex.exp z - Off n u) +
          ((n : ℂ) ^ ((a : ℂ) - s v) - T n a v) * Off n u‖ := by congr 1; ring
      _ ≤ ‖(n : ℂ) ^ ((a : ℂ) - s v)‖ * ‖Complex.exp z - Off n u‖ +
          ‖(n : ℂ) ^ ((a : ℂ) - s v) - T n a v‖ * ‖Off n u‖ := by
        grw [norm_add_le]; simp only [norm_mul]; exact le_rfl
      _ ≤ 4 * (1 / 500000) + (1 / 8000) * 2 := by gcongr
      _ ≤ _ := by norm_num
  let W : QuadraticAlgebra ℚ (-1) 0 := ⟨0, 1⟩
  let K : ℕ → QuadraticAlgebra ℚ (-1) 0 := fun j => if j ≤ 4 then W else if j ≤ 13 then 1 else -W
  let v : ℕ → ℚ := fun j => if j < 16 then (2 * (j : ℚ) + 1) / 16 else (2 * ((j : ℚ) - 16) + 9) / 4
  let R : ℕ → ℚ := fun j => if j < 16 then 1 / 16 else 1 / 4
  let U : ℕ → ℚ := fun j => (v j + R j) ^ 2 + 1 / 4
  let S : ℕ → QuadraticAlgebra ℚ (-1) 0 := fun j => ⟨1 / 2, v j⟩
  let E : ℕ → ℚ → ℕ → QuadraticAlgebra ℚ (-1) 0 := fun n a j =>
    ∑ k ∈ Finset.range 128, ((k.factorial : ℚ)⁻¹) •
      (((QuadraticAlgebra.C a) - S j) * QuadraticAlgebra.C (qr n)) ^ k
  let V : ℕ → ℕ → QuadraticAlgebra ℚ (-1) 0 := fun n k =>
    ((k.factorial : ℚ)⁻¹) • ((-W) * QuadraticAlgebra.C (qr n)) ^ k
  let B0 := fun j k => (∑ n ∈ Finset.Ico (1 : ℕ) 10, E n 0 j * V n k) +
    (1 / 2 : ℚ) • (E 10 0 j * V 10 k)
  let B1 := fun j k => (1 / 12 : ℚ) • (E 10 (-1) j * V 10 k)
  let B3 := fun j k => -(1 / 720 : ℚ) • (E 10 (-3) j * V 10 k)
  let BT := fun j k => E 10 1 j * V 10 k
  let H := fun j k r =>
    let sj := S j
    match r with
    | 0 => B0 j k + sj * B1 j k + sj * (sj + 1) * (sj + 2) * B3 j k
    | 1 => W * B1 j k + W * (3 * sj ^ 2 + 6 * sj + 2) * B3 j k
    | 2 => -(3 * sj + 3) * B3 j k
    | 3 => -W * B3 j k
    | _ => 0
  let C := fun j k r =>
    let d0 : QuadraticAlgebra ℚ (-1) 0 := QuadraticAlgebra.C ((v j) ^ 2 + 1 / 4)
    let d1 : QuadraticAlgebra ℚ (-1) 0 := QuadraticAlgebra.C (2 * v j)
    match r with
    | 0 => d0 * H j k 0 + (⟨-1 / 2, -v j⟩ : QuadraticAlgebra ℚ (-1) 0) * BT j k
    | 1 => d1 * H j k 0 + d0 * H j k 1 - W * BT j k
    | 2 => H j k 0 + d1 * H j k 1 + d0 * H j k 2
    | 3 => H j k 1 + d1 * H j k 2 + d0 * H j k 3
    | 4 => H j k 2 + d1 * H j k 3
    | 5 => H j k 3
    | _ => 0
  have hNum (j : ℕ) (hj : j ≤ 25) : (K j * C j 0 0).im +
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
        if k + r = 0 then 0 else |(K j * C j k r).im| * (R j) ^ (k + r)) ≤ -(U j) / 10 := by
    interval_cases j <;> decide +kernel
  have hcoeff (F : ℕ → ℕ → ℂ) (rr u : ℝ) (hu : |u| ≤ rr) :
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, F k r * (u : ℂ) ^ (k + r)).im ≤
        (F 0 0).im + ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          if k + r = 0 then 0 else |(F k r).im| * rr ^ (k + r) := by
    have hterm (k r : ℕ) : (F k r * (u : ℂ) ^ (k + r)).im = (F k r).im * u ^ (k + r) := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
    simp only [Complex.im_sum, hterm]
    have hdelta : (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
        if k + r = 0 then (F 0 0).im else 0) = (F 0 0).im := by
      norm_num [Finset.sum_range_succ]
    calc
      _ ≤ ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          ((if k + r = 0 then (F 0 0).im else 0) +
            (if k + r = 0 then 0 else |(F k r).im| * rr ^ (k + r))) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : k + r = 0
        · have hk0 : k = 0 := by omega
          have hr0 : r = 0 := by omega
          subst k; subst r
          simp
        · simp only [h, ite_false, zero_add]
          calc
            (F k r).im * u ^ (k + r) ≤ |(F k r).im * u ^ (k + r)| := le_abs_self _
            _ = |(F k r).im| * |u| ^ (k + r) := by rw [abs_mul, abs_pow]
            _ ≤ _ := by gcongr
      _ = _ := by simp only [Finset.sum_add_distrib, hdelta]
  let e : QuadraticAlgebra ℚ (-1) 0 →ₐ[ℚ] ℂ :=
    QuadraticAlgebra.lift ⟨I, by norm_num [smul_eq_mul]⟩
  have he_im (x : QuadraticAlgebra ℚ (-1) 0) : (e x).im = (x.im : ℝ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_C (a : ℚ) : e (QuadraticAlgebra.C a) = (a : ℂ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_W : e W = I := by norm_num [e, W, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_K_norm (j : ℕ) : ‖e (K j)‖ = 1 := by
    dsimp only [K]
    split_ifs <;> simp [map_neg, he_W]
  have he_S (j : ℕ) : e (S j) = s (v j : ℝ) := by
    norm_num [e, QuadraticAlgebra.lift, S, s, Algebra.smul_def]
  have he_mk (a b : ℚ) : e (⟨a, b⟩ : QuadraticAlgebra ℚ (-1) 0) = (a : ℂ) + b * I := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_E (n : ℕ) (a : ℚ) (j : ℕ) : e (E n a j) = T n (a : ℝ) (v j : ℝ) := by
    simp only [E, T, map_sum, map_smul, map_pow, map_mul, map_sub, he_S, he_C]
    apply Finset.sum_congr rfl
    intro k hk
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_V (n k : ℕ) : e (V n k) = ((-I) * (q n : ℂ)) ^ k / (k.factorial : ℂ) := by
    simp only [V, map_smul, map_pow, map_mul, map_neg, he_W, he_C]
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_A (n : ℕ) (a : ℚ) (j : ℕ) (u : ℝ) :
      A n (a : ℝ) (v j : ℝ) u =
        ∑ k ∈ Finset.range 12, e (E n a j * V n k) * (u : ℂ) ^ k := by
    dsimp only [A, Off]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul, he_E, he_V]
    ring
  let F : ℕ → ℝ → ℂ := fun j u =>
    ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ (k + r)
  have hRot (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, e (K j * C j k r) * (u : ℂ) ^ (k + r)) =
        e (K j) * F j u := by
    simp only [F, map_mul, Finset.mul_sum, mul_assoc]
  have hFim (j : ℕ) (hj : j ≤ 25) (u : ℝ) (hu : |u| ≤ (R j : ℝ)) : (e (K j) * F j u).im ≤ -(U j : ℝ) / 10 := by
    have hh := hcoeff (fun k r => e (K j * C j k r)) (R j : ℝ) u hu
    rw [hRot] at hh
    simp only [he_im] at hh
    apply hh.trans
    have hc : (((K j * C j 0 0).im +
        (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          if k + r = 0 then 0 else |(K j * C j k r).im| * (R j) ^ (k + r)) : ℚ) : ℝ) ≤ ((-(U j) / 10 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (hNum j hj)
    push_cast at hc
    simp only [apply_ite] at hc
    push_cast at hc
    exact hc
  have hinner (j k : ℕ) (u : ℝ) :
      (∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ r) =
        (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) *
          (e (B0 j k) + s ((v j : ℝ) + u) * e (B1 j k) +
            s ((v j : ℝ) + u) * (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) * e (B3 j k)) +
        star (s ((v j : ℝ) + u) - 1) * e (BT j k) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, C, H]
    generalize B0 j k = b0
    generalize B1 j k = b1
    generalize B3 j k = b3
    generalize BT j k = bt
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_ofNat, he_C, he_S, he_W, he_mk]
    apply Complex.ext <;>
      norm_num [s, S, W, e, QuadraticAlgebra.lift, Algebra.smul_def, pow_succ, Complex.mul_re, Complex.mul_im] <;>
      push_cast <;> ring
  have hB0c (j k : ℕ) : e (B0 j k) =
      (∑ n ∈ Finset.Ico (1 : ℕ) 10, e (E n 0 j * V n k)) + e (E 10 0 j * V 10 k) / 2 := by
    simp only [B0, map_add, map_sum, map_smul]
    simp only [Algebra.smul_def]
    norm_num
    ring
  have hB1c (j k : ℕ) : e (B1 j k) = e (E 10 (-1) j * V 10 k) / 12 := by
    simp [B1, Algebra.smul_def, div_eq_mul_inv]
    ring
  have hB3c (j k : ℕ) : e (B3 j k) = -e (E 10 (-3) j * V 10 k) / 720 := by
    simp [B3, Algebra.smul_def, div_eq_mul_inv]
    ring
  have hBTc (j k : ℕ) : e (BT j k) = e (E 10 1 j * V 10 k) := rfl
  have hB0sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B0 j k) * (u : ℂ) ^ k) =
        (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) + A 10 0 (v j : ℝ) u / 2 := by
    simp_rw [hB0c, add_mul, Finset.sum_add_distrib, Finset.sum_mul, div_mul_eq_mul_div]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [← he_A]
    norm_num
  have hB1sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B1 j k) * (u : ℂ) ^ k) = A 10 (-1) (v j : ℝ) u / 12 := by
    simp_rw [hB1c, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← he_A]
    norm_num
  have hB3sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B3 j k) * (u : ℂ) ^ k) = -A 10 (-3) (v j : ℝ) u / 720 := by
    simp_rw [hB3c, div_mul_eq_mul_div, neg_mul]
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← he_A]
    norm_num
  have hBTsum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (BT j k) * (u : ℂ) ^ k) = A 10 1 (v j : ℝ) u := by
    simp_rw [hBTc]
    rw [← he_A]
    norm_num
  have hfactor (j : ℕ) (u : ℝ) : F j u =
      ∑ k ∈ Finset.range 12, (∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ r) * (u : ℂ) ^ k := by
    dsimp only [F]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_add]
    ring
  have hFsums (j : ℕ) (u : ℝ) : F j u =
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * (∑ k ∈ Finset.range 12, e (B0 j k) * (u : ℂ) ^ k) +
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * s ((v j : ℝ) + u) *
        (∑ k ∈ Finset.range 12, e (B1 j k) * (u : ℂ) ^ k) +
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * s ((v j : ℝ) + u) *
        (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) *
        (∑ k ∈ Finset.range 12, e (B3 j k) * (u : ℂ) ^ k) +
      star (s ((v j : ℝ) + u) - 1) * (∑ k ∈ Finset.range 12, e (BT j k) * (u : ℂ) ^ k) := by
    rw [hfactor]
    simp_rw [hinner]
    simp only [Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    generalize e (B0 j k) = b0
    generalize e (B1 j k) = b1
    generalize e (B3 j k) = b3
    generalize e (BT j k) = bt
    ring
  let EMA : ℕ → ℝ → ℂ := fun j u =>
    (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) +
      A 10 1 (v j : ℝ) u / (s ((v j : ℝ) + u) - 1) + A 10 0 (v j : ℝ) u / 2 +
      s ((v j : ℝ) + u) * A 10 (-1) (v j : ℝ) u / 12 -
      s ((v j : ℝ) + u) * (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) * A 10 (-3) (v j : ℝ) u / 720
  have hscaled (j : ℕ) (u : ℝ) : F j u =
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * EMA j u := by
    rw [hFsums, hB0sum, hB1sum, hB3sum, hBTsum]
    have hne : s ((v j : ℝ) + u) - 1 ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      norm_num [s] at hr
    have hd : ((((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) : ℂ) =
        (s ((v j : ℝ) + u) - 1) * star (s ((v j : ℝ) + u) - 1) := by
      change _ = (s ((v j : ℝ) + u) - 1) * (starRingEnd ℂ) (s ((v j : ℝ) + u) - 1)
      rw [Complex.mul_conj]
      congr 1
      norm_num [Complex.normSq_apply, s]
      ring
    dsimp only [EMA]
    generalize (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) = az
    generalize A 10 1 (v j : ℝ) u = a1
    generalize A 10 0 (v j : ℝ) u = a0
    generalize A 10 (-1) (v j : ℝ) u = am1
    generalize A 10 (-3) (v j : ℝ) u = am3
    rw [hd]
    field_simp [hne]
    ring
  have hcover : ∃ j : ℕ, j ≤ 25 ∧ |t - (v j : ℝ)| ≤ (R j : ℝ) := by
    by_cases h0 : t ≤ (1 / 8 : ℝ)
    · refine ⟨0, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h1 : t ≤ (1 / 4 : ℝ)
    · refine ⟨1, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h2 : t ≤ (3 / 8 : ℝ)
    · refine ⟨2, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h3 : t ≤ (1 / 2 : ℝ)
    · refine ⟨3, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h4 : t ≤ (5 / 8 : ℝ)
    · refine ⟨4, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h5 : t ≤ (3 / 4 : ℝ)
    · refine ⟨5, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h6 : t ≤ (7 / 8 : ℝ)
    · refine ⟨6, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h7 : t ≤ (1 / 1 : ℝ)
    · refine ⟨7, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h8 : t ≤ (9 / 8 : ℝ)
    · refine ⟨8, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h9 : t ≤ (5 / 4 : ℝ)
    · refine ⟨9, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h10 : t ≤ (11 / 8 : ℝ)
    · refine ⟨10, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h11 : t ≤ (3 / 2 : ℝ)
    · refine ⟨11, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h12 : t ≤ (13 / 8 : ℝ)
    · refine ⟨12, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h13 : t ≤ (7 / 4 : ℝ)
    · refine ⟨13, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h14 : t ≤ (15 / 8 : ℝ)
    · refine ⟨14, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h15 : t ≤ (2 / 1 : ℝ)
    · refine ⟨15, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h16 : t ≤ (5 / 2 : ℝ)
    · refine ⟨16, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h17 : t ≤ (3 / 1 : ℝ)
    · refine ⟨17, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h18 : t ≤ (7 / 2 : ℝ)
    · refine ⟨18, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h19 : t ≤ (4 / 1 : ℝ)
    · refine ⟨19, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h20 : t ≤ (9 / 2 : ℝ)
    · refine ⟨20, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h21 : t ≤ (5 / 1 : ℝ)
    · refine ⟨21, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h22 : t ≤ (11 / 2 : ℝ)
    · refine ⟨22, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h23 : t ≤ (6 / 1 : ℝ)
    · refine ⟨23, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    by_cases h24 : t ≤ (13 / 2 : ℝ)
    · refine ⟨24, by norm_num, ?_⟩
      rw [abs_le]
      norm_num [v, R]
      constructor <;> linarith
    refine ⟨25, by norm_num, ?_⟩
    rw [abs_le]
    norm_num [v, R]
    constructor <;> linarith
  obtain ⟨j, hj, hu0⟩ := hcover
  let u : ℝ := t - (v j : ℝ)
  have huR : |u| ≤ (R j : ℝ) := hu0
  have hR : (R j : ℝ) ≤ 1 / 2 := by
    dsimp [R]
    split_ifs <;> norm_num
  have hu : |u| ≤ 1 / 2 := huR.trans hR
  have htu : (v j : ℝ) + u = t := by dsimp [u]; ring
  have hv0 : 0 ≤ (v j : ℝ) := by
    interval_cases j <;> norm_num [v]
  have hv14 : (v j : ℝ) ≤ 14 := by
    interval_cases j <;> norm_num [v]
  have ht0p : 0 ≤ t := ht0
  have hthigh : t ≤ 14 := by linarith
  have hsplus (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 2) : ‖s t + a‖ ≤ 20 := by
    have hh := hfac t ht0p hthigh (-a) (by linarith) (by linarith)
    simp only [ofReal_neg] at hh
    rw [show -(a : ℂ) - s t = -(s t + a) by ring, norm_neg] at hh
    linarith
  have hs0 : ‖s t‖ ≤ 20 := by simpa using hsplus 0 (by norm_num) (by norm_num)
  have hs1 : ‖s t + 1‖ ≤ 20 := by simpa using hsplus 1 (by norm_num) (by norm_num)
  have hs2 : ‖s t + 2‖ ≤ 20 := by simpa using hsplus 2 (by norm_num) (by norm_num)
  have hP : ‖s t * (s t + 1) * (s t + 2)‖ ≤ 8000 := by
    simp only [norm_mul]
    calc
      ‖s t‖ * ‖s t + 1‖ * ‖s t + 2‖ ≤ 20 * 20 * 20 := by gcongr
      _ = _ := by norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖s t - 1‖ := by
    have hh := Complex.abs_re_le_norm (s t - 1)
    norm_num [s] at hh
    exact hh
  have hinv : ‖(s t - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num [one_div] at hh
    exact hh
  have h10a := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) 1 (by norm_num) (by norm_num)
  have h10b := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) 0 (by norm_num) (by norm_num)
  have h10c := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) (-1) (by norm_num) (by norm_num)
  have h10d := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) (-3) (by norm_num) (by norm_num)
  rw [htu] at h10a h10b h10c h10d
  norm_num only [ofReal_one, ofReal_zero, ofReal_neg, zero_sub, ofReal_ofNat] at h10a h10b h10c h10d
  rw [show (-1 : ℂ) - s t = -s t - 1 by ring] at h10c
  rw [show (-3 : ℂ) - s t = -(s t) - 3 by ring] at h10d
  let AA : ℂ := (∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-(s t))) - ∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u
  have hnA : ‖AA‖ ≤ 9 / 3000 := by
    dsimp [AA]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, ‖(n : ℂ) ^ (-(s t)) - A n 0 (v j : ℝ) u‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, (1 / 3000 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : n ∈ Finset.Icc (1 : ℕ) 10 := by
          simp only [Finset.mem_Icc, Finset.mem_Ico] at *
          omega
        simpa only [ofReal_zero, zero_sub, htu] using hA (v j : ℝ) hv0 hv14 u hu n hn' 0 (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hnB : ‖((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1)‖ ≤ 2 / 3000 := by
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖(10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u‖ * ‖(s t - 1)⁻¹‖ ≤ (1 / 3000) * 2 := by gcongr
      _ = _ := by norm_num
  have hnC : ‖((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2‖ ≤ 1 / 6000 := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    linarith
  have hnD : ‖s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12‖ ≤ 2 / 3000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s t‖ * ‖(10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u‖ / 12 ≤ 20 * (1 / 3000) / 12 := by gcongr
      _ ≤ _ := by norm_num
  have hnE : ‖s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720‖ ≤ 12 / 3000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s t * (s t + 1) * (s t + 2)‖ * ‖(10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u‖ / 720 ≤ 8000 * (1 / 3000) / 720 := by gcongr
      _ ≤ _ := by norm_num
  have hErr : ‖EM10 (s t) - EMA j u‖ ≤ 1 / 100 := by
    have he : EM10 (s t) - EMA j u = AA + ((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1) +
        ((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2 + s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12 -
        s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720 := by
      dsimp only [EM10, EMA, AA]
      rw [htu]
      generalize (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) = az
      generalize A 10 1 (v j : ℝ) u = a1
      generalize A 10 0 (v j : ℝ) u = a0
      generalize A 10 (-1) (v j : ℝ) u = am1
      generalize A 10 (-3) (v j : ℝ) u = am3
      ring
    rw [he]
    calc
      _ ≤ ‖AA‖ + ‖((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1)‖ + ‖((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2‖ +
          ‖s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12‖ +
          ‖s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720‖ := by
        grw [norm_sub_le, norm_add_le, norm_add_le, norm_add_le]
      _ ≤ 9 / 3000 + 2 / 3000 + 1 / 6000 + 2 / 3000 + 12 / 3000 := by gcongr
      _ ≤ _ := by norm_num
  let D : ℝ := t ^ 2 + 1 / 4
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDmax : D ≤ (U j : ℝ) := by
    have hh := (abs_le.mp hu0).2
    have hRv : 0 ≤ (v j : ℝ) + (R j : ℝ) := by
      have hr : 0 ≤ (R j : ℝ) := by dsimp [R]; split_ifs <;> norm_num
      linarith
    dsimp [D, U]
    push_cast
    nlinarith
  have hUpos : 0 < (U j : ℝ) := by
    dsimp [U]
    push_cast
    positivity
  have hscale : F j u = (D : ℂ) * EMA j u := by
    simpa only [htu, D] using hscaled j u
  have hscaleErr : ‖(D : ℂ) * EM10 (s t) - F j u‖ ≤ D / 100 := by
    rw [hscale, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD0]
    have hh := mul_le_mul_of_nonneg_left hErr hD0
    convert hh using 1
    ring
  have herrid : e (K j) * ((D : ℂ) * EM10 (s t) - F j u) =
      (D : ℂ) * (e (K j) * EM10 (s t)) - e (K j) * F j u := by
    rw [mul_sub]
    congr 1
    ac_rfl
  have hRotErr : ‖e (K j) * ((D : ℂ) * EM10 (s t) - F j u)‖ ≤ D / 100 := by
    rw [norm_mul, he_K_norm, one_mul]
    exact hscaleErr
  have him := (le_abs_self ((e (K j) * ((D : ℂ) * EM10 (s t) - F j u)).im)).trans
    ((Complex.abs_im_le_norm (e (K j) * ((D : ℂ) * EM10 (s t) - F j u))).trans hRotErr)
  rw [herrid] at him
  rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero] at him
  have hn := (neg_le_abs ((e (K j) * EM10 (s t)).im)).trans (Complex.abs_im_le_norm (e (K j) * EM10 (s t)))
  rw [norm_mul, he_K_norm, one_mul] at hn
  have hmult := mul_le_mul_of_nonneg_left hn hD0
  have hLB : (U j : ℝ) / 10 ≤ D * (‖EM10 (s t)‖ + 1 / 100) := by
    have hf := hFim j hj u huR
    nlinarith
  change 1 / 20 ≤ ‖EM10 (s t)‖
  by_contra hlt
  have hsmall : ‖EM10 (s t)‖ < 1 / 20 := lt_of_not_ge hlt
  have hU := mul_le_mul_of_nonneg_left (show ‖EM10 (s t)‖ + 1 / 100 ≤ 3 / 50 by linarith) hD0
  have hfinal := le_trans hU (mul_le_mul_of_nonneg_right hDmax (by norm_num : (0 : ℝ) ≤ 3 / 50))
  nlinarith

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 200000 in
/-- LEAF. Unit U-1551. Finite certified computation, second piece: `|EM10(1/2 + it)| ≥ 1/20`
for `7 ≤ t ≤ 12`; float minimum `1.0956`. -/
theorem em10_lower_b (t : ℝ) (ht0 : 7 ≤ t) (ht : t ≤ 12) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  let qr : ℕ → ℚ := fun n =>
    match n with
    | 1 => 0
    | 2 => 693147 / 1000000
    | 3 => 1098612 / 1000000
    | 4 => 1386294 / 1000000
    | 5 => 1609437 / 1000000
    | 6 => 1791759 / 1000000
    | 7 => 1945910 / 1000000
    | 8 => 2079441 / 1000000
    | 9 => 2197224 / 1000000
    | 10 => 2302585 / 1000000
    | _ => 0
  let q : ℕ → ℝ := fun n => (qr n : ℝ)
  have hlog7 : |Real.log 7 - q 7| ≤ 1 / 1000000 := by
    have hh := Real.abs_log_sub_add_sum_range_le (x := 1 / 8) (by norm_num) 10
    have he : Real.log (1 - (1 / 8 : ℝ)) = Real.log 7 - 3 * Real.log 2 := by
      rw [show (1 - (1 / 8 : ℝ)) = 7 / 8 by norm_num,
        Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
      have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [he8]
    rw [he] at hh
    norm_num [Finset.sum_range_succ, q, qr] at hh ⊢
    rw [abs_le] at hh ⊢
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  norm_num only [q, qr] at hlog7
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by norm_num [← Real.log_mul]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogs (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) :
      |Real.log n - q n| ≤ 1 / 1000000 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, hlog4, hlog6, hlog8, hlog9, Real.log_ten_eq, qr]
    all_goals rw [abs_le]
    all_goals constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9,
      (abs_le.mp hlog7).1, (abs_le.mp hlog7).2]
  let s : ℝ → ℂ := fun v => (1 / 2 : ℂ) + v * I
  let T : ℕ → ℝ → ℝ → ℂ := fun n a v =>
    ∑ k ∈ Finset.range 128, ((((a : ℂ) - s v) * (q n : ℂ)) ^ k / (k.factorial : ℂ))
  have hq (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) : 0 ≤ q n ∧ q n ≤ 5 / 2 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, qr]
  have hfac (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) : ‖(a : ℂ) - (s v)‖ ≤ 15 := by
    have hsq : ‖(a : ℂ) - (s v)‖ ^ 2 = (a - 1 / 2) ^ 2 + v ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num [s]
      ring
    have ha2 : a ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg (show 0 ≤ a + 3 by linarith) (show 0 ≤ 3 - a by linarith)]
    nlinarith [norm_nonneg ((a : ℂ) - (s v)), mul_nonneg hv0 (sub_nonneg.mpr hv)]
  have hp (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - (s v))‖ ≤ 4 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    norm_num [s]
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ ≤ (10 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn10) (by norm_num)
      _ ≤ 4 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have happ (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - (s v)) - T n a v‖ ≤ 1 / 8000 := by
    let z : ℂ := ((a : ℂ) - (s v)) * (Real.log n : ℂ)
    let w : ℂ := ((a : ℂ) - (s v)) * (q n : ℂ)
    have hez : Complex.exp z = (n : ℂ) ^ ((a : ℂ) - (s v)) := by
      have hn0 : (n : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
      rw [Complex.cpow_def_of_ne_zero hn0]
      dsimp [z]
      rw [← Complex.natCast_log]
      congr 1
      ring
    have hz : ‖Complex.exp z‖ ≤ 4 := by rw [hez]; exact hp v hv0 hv n hn a ha1
    have hzw : ‖w - z‖ ≤ 15 / 1000000 := by
      have he : w - z = ((a : ℂ) - (s v)) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      calc
        _ ≤ 15 * (1 / 1000000) := mul_le_mul (hfac v hv0 hv a ha ha1) (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    have hw : ‖w‖ ≤ 40 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq n hn).1]
      calc
        _ ≤ 15 * (5 / 2) := mul_le_mul (hfac v hv0 hv a ha ha1) (hq n hn).2 (hq n hn).1 (by norm_num)
        _ ≤ _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 8 * (15 / 1000000) := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 1
        ring
      rw [norm_sub_rev, he, norm_mul]
      have hh := Complex.norm_exp_sub_one_le (x := w - z) (by linarith : ‖w - z‖ ≤ 1)
      have hhd : ‖Complex.exp (w - z) - 1‖ ≤ 2 * (15 / 1000000) :=
        hh.trans (mul_le_mul_of_nonneg_left hzw (by norm_num))
      calc
        ‖Complex.exp z‖ * ‖Complex.exp (w - z) - 1‖ ≤ 4 * (2 * (15 / 1000000)) := by gcongr
        _ = 8 * (15 / 1000000) := by norm_num
    have hTaylor : ‖Complex.exp w - T n a v‖ ≤ 1 / 10000000 := by
      have hh := Complex.exp_bound' (x := w) (n := 128) (by norm_num; linarith)
      apply hh.trans
      calc
        _ ≤ (40 : ℝ) ^ 128 / (128 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    rw [← hez]
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - T n a v)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - T n a v‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  let Off : ℕ → ℝ → ℂ := fun n u => ∑ k ∈ Finset.range 12,
    (((-I) * (q n : ℂ)) ^ k / (k.factorial : ℂ)) * (u : ℂ) ^ k
  have hOff (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (u : ℝ) (hu : |u| ≤ 1 / 2) :
      ‖Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ)) - Off n u‖ ≤ 1 / 500000 := by
    let z : ℂ := -I * (u : ℂ) * (Real.log n : ℂ)
    let w : ℂ := -I * (u : ℂ) * (q n : ℂ)
    have hz : ‖Complex.exp z‖ = 1 := by rw [Complex.norm_exp]; simp only [z, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, sub_self, add_zero, zero_add, neg_zero, Real.exp_zero]
    have hzw : ‖w - z‖ ≤ 1 / 2000000 := by
      have he : w - z = -I * (u : ℂ) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]; push_cast; ring
      rw [he, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
      calc
        |u| * |Real.log n - q n| ≤ (1 / 2) * (1 / 1000000) :=
          mul_le_mul hu (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hw : ‖w‖ ≤ 5 / 4 := by
      dsimp [w]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hq n hn).1]
      calc
        |u| * q n ≤ (1 / 2) * (5 / 2) := mul_le_mul hu (hq n hn).2 (hq n hn).1 (by norm_num)
        _ = _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 1 / 1000000 := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; ring
      rw [norm_sub_rev, he, norm_mul, hz, one_mul]
      exact (Complex.norm_exp_sub_one_le (by linarith : ‖w - z‖ ≤ 1)).trans
        (by linarith)
    have hTaylor : ‖Complex.exp w - ∑ k ∈ Finset.range 12, w ^ k / (k.factorial : ℂ)‖ ≤ 1 / 1000000 := by
      apply (Complex.exp_bound' (x := w) (n := 12) (by norm_num; linarith)).trans
      calc
        ‖w‖ ^ 12 / (12 : ℕ).factorial * 2 ≤ (5 / 4 : ℝ) ^ 12 / (12 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    have hpoly : (∑ k ∈ Finset.range 12, w ^ k / (k.factorial : ℂ)) = Off n u := by
      dsimp only [Off]
      apply Finset.sum_congr rfl
      intro k hk
      have he : w = ((-I) * (q n : ℂ)) * (u : ℂ) := by dsimp [w]; ring
      rw [he, mul_pow]
      ring
    rw [hpoly] at hTaylor
    change ‖Complex.exp z - Off n u‖ ≤ _
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - Off n u)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - Off n u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hOffnorm (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (u : ℝ) (hu : |u| ≤ 1 / 2) :
      ‖Off n u‖ ≤ 2 := by
    have hz : ‖Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, sub_self, add_zero, zero_add, neg_zero, Real.exp_zero]
    have hh := norm_sub_norm_le (Off n u) (Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ)))
    rw [norm_sub_rev, hz] at hh
    have ho := hOff n hn u hu
    linarith
  let A : ℕ → ℝ → ℝ → ℝ → ℂ := fun n a v u => T n a v * Off n u
  have hA (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (u : ℝ) (hu : |u| ≤ 1 / 2)
      (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - s (v + u)) - A n a v u‖ ≤ 1 / 3000 := by
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
    let z : ℂ := -I * (u : ℂ) * (Real.log n : ℂ)
    have he : (n : ℂ) ^ ((a : ℂ) - s (v + u)) =
        (n : ℂ) ^ ((a : ℂ) - s v) * Complex.exp z := by
      rw [show (a : ℂ) - s (v + u) = ((a : ℂ) - s v) + (-I * (u : ℂ)) by dsimp [s]; push_cast; ring,
        Complex.cpow_add _ _ hn0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
      dsimp [z]
      congr 1
      ring
    rw [he]
    dsimp only [A]
    have hc := happ v hv0 hv n hn a ha ha1
    have hcNorm := hp v hv0 hv n hn a ha1
    have ho := hOff n hn u hu
    have hoNorm := hOffnorm n hn u hu
    calc
      _ = ‖(n : ℂ) ^ ((a : ℂ) - s v) * (Complex.exp z - Off n u) +
          ((n : ℂ) ^ ((a : ℂ) - s v) - T n a v) * Off n u‖ := by congr 1; ring
      _ ≤ ‖(n : ℂ) ^ ((a : ℂ) - s v)‖ * ‖Complex.exp z - Off n u‖ +
          ‖(n : ℂ) ^ ((a : ℂ) - s v) - T n a v‖ * ‖Off n u‖ := by
        grw [norm_add_le]; simp only [norm_mul]; exact le_rfl
      _ ≤ 4 * (1 / 500000) + (1 / 8000) * 2 := by gcongr
      _ ≤ _ := by norm_num
  let W : QuadraticAlgebra ℚ (-1) 0 := ⟨0, 1⟩
  let K : QuadraticAlgebra ℚ (-1) 0 := -W
  let v : ℕ → ℚ := fun j => (15 + 2 * j) / 2
  let S : ℕ → QuadraticAlgebra ℚ (-1) 0 := fun j => ⟨1 / 2, v j⟩
  let E : ℕ → ℚ → ℕ → QuadraticAlgebra ℚ (-1) 0 := fun n a j =>
    ∑ k ∈ Finset.range 128, ((k.factorial : ℚ)⁻¹) •
      (((QuadraticAlgebra.C a) - S j) * QuadraticAlgebra.C (qr n)) ^ k
  let V : ℕ → ℕ → QuadraticAlgebra ℚ (-1) 0 := fun n k =>
    ((k.factorial : ℚ)⁻¹) • ((-W) * QuadraticAlgebra.C (qr n)) ^ k
  let B0 := fun j k => (∑ n ∈ Finset.Ico (1 : ℕ) 10, E n 0 j * V n k) +
    (1 / 2 : ℚ) • (E 10 0 j * V 10 k)
  let B1 := fun j k => (1 / 12 : ℚ) • (E 10 (-1) j * V 10 k)
  let B3 := fun j k => -(1 / 720 : ℚ) • (E 10 (-3) j * V 10 k)
  let BT := fun j k => E 10 1 j * V 10 k
  let H := fun j k r =>
    let sj := S j
    match r with
    | 0 => B0 j k + sj * B1 j k + sj * (sj + 1) * (sj + 2) * B3 j k
    | 1 => W * B1 j k + W * (3 * sj ^ 2 + 6 * sj + 2) * B3 j k
    | 2 => -(3 * sj + 3) * B3 j k
    | 3 => -W * B3 j k
    | _ => 0
  let C := fun j k r =>
    let d0 : QuadraticAlgebra ℚ (-1) 0 := QuadraticAlgebra.C ((v j) ^ 2 + 1 / 4)
    let d1 : QuadraticAlgebra ℚ (-1) 0 := QuadraticAlgebra.C (2 * v j)
    match r with
    | 0 => d0 * H j k 0 + (⟨-1 / 2, -v j⟩ : QuadraticAlgebra ℚ (-1) 0) * BT j k
    | 1 => d1 * H j k 0 + d0 * H j k 1 - W * BT j k
    | 2 => H j k 0 + d1 * H j k 1 + d0 * H j k 2
    | 3 => H j k 1 + d1 * H j k 2 + d0 * H j k 3
    | 4 => H j k 2 + d1 * H j k 3
    | 5 => H j k 3
    | _ => 0
  have hNum (j : ℕ) (hj : j ≤ 4) : (K * C j 0 0).im +
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
        if k + r = 0 then 0 else |(K * C j k r).im| * (1 / 2 : ℚ) ^ (k + r)) ≤ -15 := by
    interval_cases j <;> decide +kernel
  have hcoeff (F : ℕ → ℕ → ℂ) (u : ℝ) (hu : |u| ≤ 1 / 2) :
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, F k r * (u : ℂ) ^ (k + r)).im ≤
        (F 0 0).im + ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          if k + r = 0 then 0 else |(F k r).im| * (1 / 2 : ℝ) ^ (k + r) := by
    have hterm (k r : ℕ) : (F k r * (u : ℂ) ^ (k + r)).im = (F k r).im * u ^ (k + r) := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
    simp only [Complex.im_sum, hterm]
    have hdelta : (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
        if k + r = 0 then (F 0 0).im else 0) = (F 0 0).im := by
      norm_num [Finset.sum_range_succ]
    calc
      _ ≤ ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          ((if k + r = 0 then (F 0 0).im else 0) +
            (if k + r = 0 then 0 else |(F k r).im| * (1 / 2 : ℝ) ^ (k + r))) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : k + r = 0
        · have hk0 : k = 0 := by omega
          have hr0 : r = 0 := by omega
          subst k; subst r
          simp
        · simp only [h, ite_false, zero_add]
          calc
            (F k r).im * u ^ (k + r) ≤ |(F k r).im * u ^ (k + r)| := le_abs_self _
            _ = |(F k r).im| * |u| ^ (k + r) := by rw [abs_mul, abs_pow]
            _ ≤ _ := by gcongr
      _ = _ := by simp only [Finset.sum_add_distrib, hdelta]
  let e : QuadraticAlgebra ℚ (-1) 0 →ₐ[ℚ] ℂ :=
    QuadraticAlgebra.lift ⟨I, by norm_num [smul_eq_mul]⟩
  have he_im (x : QuadraticAlgebra ℚ (-1) 0) : (e x).im = (x.im : ℝ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_C (a : ℚ) : e (QuadraticAlgebra.C a) = (a : ℂ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_W : e W = I := by norm_num [e, W, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_K : e K = -I := by simpa only [K, map_neg] using congrArg Neg.neg he_W
  have he_S (j : ℕ) : e (S j) = s (v j : ℝ) := by
    norm_num [e, QuadraticAlgebra.lift, S, s, Algebra.smul_def]
  have he_mk (a b : ℚ) : e (⟨a, b⟩ : QuadraticAlgebra ℚ (-1) 0) = (a : ℂ) + b * I := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_E (n : ℕ) (a : ℚ) (j : ℕ) : e (E n a j) = T n (a : ℝ) (v j : ℝ) := by
    simp only [E, T, map_sum, map_smul, map_pow, map_mul, map_sub, he_S, he_C]
    apply Finset.sum_congr rfl
    intro k hk
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_V (n k : ℕ) : e (V n k) = ((-I) * (q n : ℂ)) ^ k / (k.factorial : ℂ) := by
    simp only [V, map_smul, map_pow, map_mul, map_neg, he_W, he_C]
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_A (n : ℕ) (a : ℚ) (j : ℕ) (u : ℝ) :
      A n (a : ℝ) (v j : ℝ) u =
        ∑ k ∈ Finset.range 12, e (E n a j * V n k) * (u : ℂ) ^ k := by
    dsimp only [A, Off]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul, he_E, he_V]
    ring
  let F : ℕ → ℝ → ℂ := fun j u =>
    ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ (k + r)
  have hRot (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, e (K * C j k r) * (u : ℂ) ^ (k + r)) =
        (-I) * F j u := by
    simp only [F, map_mul, Finset.mul_sum, mul_assoc, he_K]
  have hFim (j : ℕ) (hj : j ≤ 4) (u : ℝ) (hu : |u| ≤ 1 / 2) : ((-I) * F j u).im ≤ -15 := by
    have hh := hcoeff (fun k r => e (K * C j k r)) u hu
    rw [hRot] at hh
    simp only [he_im] at hh
    apply hh.trans
    have hc : (((K * C j 0 0).im +
        (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          if k + r = 0 then 0 else |(K * C j k r).im| * (1 / 2 : ℚ) ^ (k + r)) : ℚ) : ℝ) ≤ ((-15 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (hNum j hj)
    push_cast at hc
    simp only [apply_ite] at hc
    push_cast at hc
    exact hc
  have hinner (j k : ℕ) (u : ℝ) :
      (∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ r) =
        (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) *
          (e (B0 j k) + s ((v j : ℝ) + u) * e (B1 j k) +
            s ((v j : ℝ) + u) * (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) * e (B3 j k)) +
        star (s ((v j : ℝ) + u) - 1) * e (BT j k) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, C, H]
    generalize B0 j k = b0
    generalize B1 j k = b1
    generalize B3 j k = b3
    generalize BT j k = bt
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_ofNat, he_C, he_S, he_W, he_mk]
    apply Complex.ext <;>
      norm_num [s, S, W, e, QuadraticAlgebra.lift, Algebra.smul_def, pow_succ, Complex.mul_re, Complex.mul_im] <;>
      push_cast <;> ring
  have hB0c (j k : ℕ) : e (B0 j k) =
      (∑ n ∈ Finset.Ico (1 : ℕ) 10, e (E n 0 j * V n k)) + e (E 10 0 j * V 10 k) / 2 := by
    simp only [B0, map_add, map_sum, map_smul]
    simp only [Algebra.smul_def]
    norm_num
    ring
  have hB1c (j k : ℕ) : e (B1 j k) = e (E 10 (-1) j * V 10 k) / 12 := by
    simp [B1, Algebra.smul_def, div_eq_mul_inv]
    ring
  have hB3c (j k : ℕ) : e (B3 j k) = -e (E 10 (-3) j * V 10 k) / 720 := by
    simp [B3, Algebra.smul_def, div_eq_mul_inv]
    ring
  have hBTc (j k : ℕ) : e (BT j k) = e (E 10 1 j * V 10 k) := rfl
  have hB0sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B0 j k) * (u : ℂ) ^ k) =
        (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) + A 10 0 (v j : ℝ) u / 2 := by
    simp_rw [hB0c, add_mul, Finset.sum_add_distrib, Finset.sum_mul, div_mul_eq_mul_div]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [← he_A]
    norm_num
  have hB1sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B1 j k) * (u : ℂ) ^ k) = A 10 (-1) (v j : ℝ) u / 12 := by
    simp_rw [hB1c, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← he_A]
    norm_num
  have hB3sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B3 j k) * (u : ℂ) ^ k) = -A 10 (-3) (v j : ℝ) u / 720 := by
    simp_rw [hB3c, div_mul_eq_mul_div, neg_mul]
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← he_A]
    norm_num
  have hBTsum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (BT j k) * (u : ℂ) ^ k) = A 10 1 (v j : ℝ) u := by
    simp_rw [hBTc]
    rw [← he_A]
    norm_num
  have hfactor (j : ℕ) (u : ℝ) : F j u =
      ∑ k ∈ Finset.range 12, (∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ r) * (u : ℂ) ^ k := by
    dsimp only [F]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_add]
    ring
  have hFsums (j : ℕ) (u : ℝ) : F j u =
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * (∑ k ∈ Finset.range 12, e (B0 j k) * (u : ℂ) ^ k) +
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * s ((v j : ℝ) + u) *
        (∑ k ∈ Finset.range 12, e (B1 j k) * (u : ℂ) ^ k) +
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * s ((v j : ℝ) + u) *
        (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) *
        (∑ k ∈ Finset.range 12, e (B3 j k) * (u : ℂ) ^ k) +
      star (s ((v j : ℝ) + u) - 1) * (∑ k ∈ Finset.range 12, e (BT j k) * (u : ℂ) ^ k) := by
    rw [hfactor]
    simp_rw [hinner]
    simp only [Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    generalize e (B0 j k) = b0
    generalize e (B1 j k) = b1
    generalize e (B3 j k) = b3
    generalize e (BT j k) = bt
    ring
  let EMA : ℕ → ℝ → ℂ := fun j u =>
    (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) +
      A 10 1 (v j : ℝ) u / (s ((v j : ℝ) + u) - 1) + A 10 0 (v j : ℝ) u / 2 +
      s ((v j : ℝ) + u) * A 10 (-1) (v j : ℝ) u / 12 -
      s ((v j : ℝ) + u) * (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) * A 10 (-3) (v j : ℝ) u / 720
  have hscaled (j : ℕ) (u : ℝ) : F j u =
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * EMA j u := by
    rw [hFsums, hB0sum, hB1sum, hB3sum, hBTsum]
    have hne : s ((v j : ℝ) + u) - 1 ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      norm_num [s] at hr
    have hd : ((((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) : ℂ) =
        (s ((v j : ℝ) + u) - 1) * star (s ((v j : ℝ) + u) - 1) := by
      change _ = (s ((v j : ℝ) + u) - 1) * (starRingEnd ℂ) (s ((v j : ℝ) + u) - 1)
      rw [Complex.mul_conj]
      congr 1
      norm_num [Complex.normSq_apply, s]
      ring
    dsimp only [EMA]
    generalize (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) = az
    generalize A 10 1 (v j : ℝ) u = a1
    generalize A 10 0 (v j : ℝ) u = a0
    generalize A 10 (-1) (v j : ℝ) u = am1
    generalize A 10 (-3) (v j : ℝ) u = am3
    rw [hd]
    field_simp [hne]
    ring
  have hcover : ∃ j : ℕ, j ≤ 4 ∧ |t - (v j : ℝ)| ≤ 1 / 2 := by
    by_cases h0 : t ≤ 8
    · refine ⟨0, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    by_cases h1 : t ≤ 9
    · refine ⟨1, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    by_cases h2 : t ≤ 10
    · refine ⟨2, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    by_cases h3 : t ≤ 11
    · refine ⟨3, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    · refine ⟨4, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
  obtain ⟨j, hj, hu0⟩ := hcover
  let u : ℝ := t - (v j : ℝ)
  have hu : |u| ≤ 1 / 2 := hu0
  have htu : (v j : ℝ) + u = t := by dsimp [u]; ring
  have hjR : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  have hv0 : 0 ≤ (v j : ℝ) := by norm_num [v]; positivity
  have hv14 : (v j : ℝ) ≤ 14 := by norm_num [v]; linarith
  have ht0p : 0 ≤ t := by linarith
  have hthigh : t ≤ 14 := by linarith
  have hsplus (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 2) : ‖s t + a‖ ≤ 20 := by
    have hh := hfac t ht0p hthigh (-a) (by linarith) (by linarith)
    simp only [ofReal_neg] at hh
    rw [show -(a : ℂ) - s t = -(s t + a) by ring, norm_neg] at hh
    linarith
  have hs0 : ‖s t‖ ≤ 20 := by simpa using hsplus 0 (by norm_num) (by norm_num)
  have hs1 : ‖s t + 1‖ ≤ 20 := by simpa using hsplus 1 (by norm_num) (by norm_num)
  have hs2 : ‖s t + 2‖ ≤ 20 := by simpa using hsplus 2 (by norm_num) (by norm_num)
  have hP : ‖s t * (s t + 1) * (s t + 2)‖ ≤ 8000 := by
    simp only [norm_mul]
    calc
      ‖s t‖ * ‖s t + 1‖ * ‖s t + 2‖ ≤ 20 * 20 * 20 := by gcongr
      _ = _ := by norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖s t - 1‖ := by
    have hh := Complex.abs_re_le_norm (s t - 1)
    norm_num [s] at hh
    exact hh
  have hinv : ‖(s t - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num [one_div] at hh
    exact hh
  have h10a := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) 1 (by norm_num) (by norm_num)
  have h10b := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) 0 (by norm_num) (by norm_num)
  have h10c := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) (-1) (by norm_num) (by norm_num)
  have h10d := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) (-3) (by norm_num) (by norm_num)
  rw [htu] at h10a h10b h10c h10d
  norm_num only [ofReal_one, ofReal_zero, ofReal_neg, zero_sub, ofReal_ofNat] at h10a h10b h10c h10d
  rw [show (-1 : ℂ) - s t = -s t - 1 by ring] at h10c
  rw [show (-3 : ℂ) - s t = -(s t) - 3 by ring] at h10d
  let AA : ℂ := (∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-(s t))) - ∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u
  have hnA : ‖AA‖ ≤ 9 / 3000 := by
    dsimp [AA]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, ‖(n : ℂ) ^ (-(s t)) - A n 0 (v j : ℝ) u‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, (1 / 3000 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : n ∈ Finset.Icc (1 : ℕ) 10 := by
          simp only [Finset.mem_Icc, Finset.mem_Ico] at *
          omega
        simpa only [ofReal_zero, zero_sub, htu] using hA (v j : ℝ) hv0 hv14 u hu n hn' 0 (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hnB : ‖((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1)‖ ≤ 2 / 3000 := by
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖(10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u‖ * ‖(s t - 1)⁻¹‖ ≤ (1 / 3000) * 2 := by gcongr
      _ = _ := by norm_num
  have hnC : ‖((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2‖ ≤ 1 / 6000 := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    linarith
  have hnD : ‖s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12‖ ≤ 2 / 3000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s t‖ * ‖(10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u‖ / 12 ≤ 20 * (1 / 3000) / 12 := by gcongr
      _ ≤ _ := by norm_num
  have hnE : ‖s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720‖ ≤ 12 / 3000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s t * (s t + 1) * (s t + 2)‖ * ‖(10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u‖ / 720 ≤ 8000 * (1 / 3000) / 720 := by gcongr
      _ ≤ _ := by norm_num
  have hErr : ‖EM10 (s t) - EMA j u‖ ≤ 1 / 100 := by
    have he : EM10 (s t) - EMA j u = AA + ((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1) +
        ((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2 + s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12 -
        s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720 := by
      dsimp only [EM10, EMA, AA]
      rw [htu]
      generalize (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) = az
      generalize A 10 1 (v j : ℝ) u = a1
      generalize A 10 0 (v j : ℝ) u = a0
      generalize A 10 (-1) (v j : ℝ) u = am1
      generalize A 10 (-3) (v j : ℝ) u = am3
      ring
    rw [he]
    calc
      _ ≤ ‖AA‖ + ‖((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1)‖ + ‖((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2‖ +
          ‖s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12‖ +
          ‖s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720‖ := by
        grw [norm_sub_le, norm_add_le, norm_add_le, norm_add_le]
      _ ≤ 9 / 3000 + 2 / 3000 + 1 / 6000 + 2 / 3000 + 12 / 3000 := by gcongr
      _ ≤ _ := by norm_num
  let D : ℝ := t ^ 2 + 1 / 4
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDmax : D ≤ 785 / 4 := by
    dsimp [D]
    nlinarith [mul_nonneg ht0p (sub_nonneg.mpr hthigh)]
  have hscale : F j u = (D : ℂ) * EMA j u := by
    simpa only [htu, D] using hscaled j u
  have hscaleErr : ‖(D : ℂ) * EM10 (s t) - F j u‖ ≤ D / 100 := by
    rw [hscale, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD0]
    have hh := mul_le_mul_of_nonneg_left hErr hD0
    convert hh using 1
    ring
  have herrid : (-I) * ((D : ℂ) * EM10 (s t) - F j u) =
      (D : ℂ) * ((-I) * EM10 (s t)) - (-I) * F j u := by
    rw [mul_sub]
    congr 1
    ac_rfl
  have hRotErr : ‖(-I) * ((D : ℂ) * EM10 (s t) - F j u)‖ ≤ D / 100 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact hscaleErr
  have him := (le_abs_self (((-I) * ((D : ℂ) * EM10 (s t) - F j u)).im)).trans
    ((Complex.abs_im_le_norm ((-I) * ((D : ℂ) * EM10 (s t) - F j u))).trans hRotErr)
  rw [herrid] at him
  rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero] at him
  have hn := (neg_le_abs (((-I) * EM10 (s t)).im)).trans (Complex.abs_im_le_norm ((-I) * EM10 (s t)))
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at hn
  have hmult := mul_le_mul_of_nonneg_left hn hD0
  have hLB : 15 ≤ D * (‖EM10 (s t)‖ + 1 / 100) := by
    have hf := hFim j hj u hu
    nlinarith
  change 1 / 20 ≤ ‖EM10 (s t)‖
  by_contra hlt
  have hsmall : ‖EM10 (s t)‖ < 1 / 20 := lt_of_not_ge hlt
  have hU := mul_le_mul_of_nonneg_left (show ‖EM10 (s t)‖ + 1 / 100 ≤ 3 / 50 by linarith) hD0
  nlinarith

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 200000 in
/-- LEAF. Unit U-1551. Finite certified computation, third piece: `|EM10(1/2 + it)| ≥ 1/20`
for `12 ≤ t ≤ 14`; float minimum `0.1056` at `t = 14`, where `|ζ(1/2 + 14i)| = 0.1056`; the
first zero is at `t = 14.1347`. -/
theorem em10_lower_c (t : ℝ) (ht0 : 12 ≤ t) (ht : t ≤ 14) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  let qr : ℕ → ℚ := fun n =>
    match n with
    | 1 => 0
    | 2 => 693147 / 1000000
    | 3 => 1098612 / 1000000
    | 4 => 1386294 / 1000000
    | 5 => 1609437 / 1000000
    | 6 => 1791759 / 1000000
    | 7 => 1945910 / 1000000
    | 8 => 2079441 / 1000000
    | 9 => 2197224 / 1000000
    | 10 => 2302585 / 1000000
    | _ => 0
  let q : ℕ → ℝ := fun n => (qr n : ℝ)
  have hlog7 : |Real.log 7 - q 7| ≤ 1 / 1000000 := by
    have hh := Real.abs_log_sub_add_sum_range_le (x := 1 / 8) (by norm_num) 10
    have he : Real.log (1 - (1 / 8 : ℝ)) = Real.log 7 - 3 * Real.log 2 := by
      rw [show (1 - (1 / 8 : ℝ)) = 7 / 8 by norm_num,
        Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
      have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [he8]
    rw [he] at hh
    norm_num [Finset.sum_range_succ, q, qr] at hh ⊢
    rw [abs_le] at hh ⊢
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  norm_num only [q, qr] at hlog7
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by norm_num [← Real.log_mul]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogs (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) :
      |Real.log n - q n| ≤ 1 / 1000000 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, hlog4, hlog6, hlog8, hlog9, Real.log_ten_eq, qr]
    all_goals rw [abs_le]
    all_goals constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9,
      (abs_le.mp hlog7).1, (abs_le.mp hlog7).2]
  let s : ℝ → ℂ := fun v => (1 / 2 : ℂ) + v * I
  let T : ℕ → ℝ → ℝ → ℂ := fun n a v =>
    ∑ k ∈ Finset.range 128, ((((a : ℂ) - s v) * (q n : ℂ)) ^ k / (k.factorial : ℂ))
  have hq (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) : 0 ≤ q n ∧ q n ≤ 5 / 2 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, qr]
  have hfac (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) : ‖(a : ℂ) - (s v)‖ ≤ 15 := by
    have hsq : ‖(a : ℂ) - (s v)‖ ^ 2 = (a - 1 / 2) ^ 2 + v ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num [s]
      ring
    have ha2 : a ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg (show 0 ≤ a + 3 by linarith) (show 0 ≤ 3 - a by linarith)]
    nlinarith [norm_nonneg ((a : ℂ) - (s v)), mul_nonneg hv0 (sub_nonneg.mpr hv)]
  have hp (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - (s v))‖ ≤ 4 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    norm_num [s]
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ ≤ (10 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn10) (by norm_num)
      _ ≤ 4 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have happ (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - (s v)) - T n a v‖ ≤ 1 / 8000 := by
    let z : ℂ := ((a : ℂ) - (s v)) * (Real.log n : ℂ)
    let w : ℂ := ((a : ℂ) - (s v)) * (q n : ℂ)
    have hez : Complex.exp z = (n : ℂ) ^ ((a : ℂ) - (s v)) := by
      have hn0 : (n : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
      rw [Complex.cpow_def_of_ne_zero hn0]
      dsimp [z]
      rw [← Complex.natCast_log]
      congr 1
      ring
    have hz : ‖Complex.exp z‖ ≤ 4 := by rw [hez]; exact hp v hv0 hv n hn a ha1
    have hzw : ‖w - z‖ ≤ 15 / 1000000 := by
      have he : w - z = ((a : ℂ) - (s v)) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      calc
        _ ≤ 15 * (1 / 1000000) := mul_le_mul (hfac v hv0 hv a ha ha1) (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    have hw : ‖w‖ ≤ 40 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq n hn).1]
      calc
        _ ≤ 15 * (5 / 2) := mul_le_mul (hfac v hv0 hv a ha ha1) (hq n hn).2 (hq n hn).1 (by norm_num)
        _ ≤ _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 8 * (15 / 1000000) := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 1
        ring
      rw [norm_sub_rev, he, norm_mul]
      have hh := Complex.norm_exp_sub_one_le (x := w - z) (by linarith : ‖w - z‖ ≤ 1)
      have hhd : ‖Complex.exp (w - z) - 1‖ ≤ 2 * (15 / 1000000) :=
        hh.trans (mul_le_mul_of_nonneg_left hzw (by norm_num))
      calc
        ‖Complex.exp z‖ * ‖Complex.exp (w - z) - 1‖ ≤ 4 * (2 * (15 / 1000000)) := by gcongr
        _ = 8 * (15 / 1000000) := by norm_num
    have hTaylor : ‖Complex.exp w - T n a v‖ ≤ 1 / 10000000 := by
      have hh := Complex.exp_bound' (x := w) (n := 128) (by norm_num; linarith)
      apply hh.trans
      calc
        _ ≤ (40 : ℝ) ^ 128 / (128 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    rw [← hez]
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - T n a v)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - T n a v‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  let Off : ℕ → ℝ → ℂ := fun n u => ∑ k ∈ Finset.range 12,
    (((-I) * (q n : ℂ)) ^ k / (k.factorial : ℂ)) * (u : ℂ) ^ k
  have hOff (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (u : ℝ) (hu : |u| ≤ 1 / 4) :
      ‖Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ)) - Off n u‖ ≤ 1 / 1000000 := by
    let z : ℂ := -I * (u : ℂ) * (Real.log n : ℂ)
    let w : ℂ := -I * (u : ℂ) * (q n : ℂ)
    have hz : ‖Complex.exp z‖ = 1 := by rw [Complex.norm_exp]; simp only [z, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, sub_self, add_zero, zero_add, neg_zero, Real.exp_zero]
    have hzw : ‖w - z‖ ≤ 1 / 4000000 := by
      have he : w - z = -I * (u : ℂ) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]; push_cast; ring
      rw [he, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
      calc
        |u| * |Real.log n - q n| ≤ (1 / 4) * (1 / 1000000) :=
          mul_le_mul hu (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hw : ‖w‖ ≤ 5 / 8 := by
      dsimp [w]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hq n hn).1]
      calc
        |u| * q n ≤ (1 / 4) * (5 / 2) := mul_le_mul hu (hq n hn).2 (hq n hn).1 (by norm_num)
        _ = _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 1 / 2000000 := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; ring
      rw [norm_sub_rev, he, norm_mul, hz, one_mul]
      exact (Complex.norm_exp_sub_one_le (by linarith : ‖w - z‖ ≤ 1)).trans
        (by linarith)
    have hTaylor : ‖Complex.exp w - ∑ k ∈ Finset.range 12, w ^ k / (k.factorial : ℂ)‖ ≤ 1 / 2000000 := by
      apply (Complex.exp_bound' (x := w) (n := 12) (by norm_num; linarith)).trans
      calc
        ‖w‖ ^ 12 / (12 : ℕ).factorial * 2 ≤ (5 / 8 : ℝ) ^ 12 / (12 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    have hpoly : (∑ k ∈ Finset.range 12, w ^ k / (k.factorial : ℂ)) = Off n u := by
      dsimp only [Off]
      apply Finset.sum_congr rfl
      intro k hk
      have he : w = ((-I) * (q n : ℂ)) * (u : ℂ) := by dsimp [w]; ring
      rw [he, mul_pow]
      ring
    rw [hpoly] at hTaylor
    change ‖Complex.exp z - Off n u‖ ≤ _
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - Off n u)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - Off n u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hOffnorm (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (u : ℝ) (hu : |u| ≤ 1 / 4) :
      ‖Off n u‖ ≤ 2 := by
    have hz : ‖Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, sub_self, add_zero, zero_add, neg_zero, Real.exp_zero]
    have hh := norm_sub_norm_le (Off n u) (Complex.exp (-I * (u : ℂ) * (Real.log n : ℂ)))
    rw [norm_sub_rev, hz] at hh
    have ho := hOff n hn u hu
    linarith
  let A : ℕ → ℝ → ℝ → ℝ → ℂ := fun n a v u => T n a v * Off n u
  have hA (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 14) (u : ℝ) (hu : |u| ≤ 1 / 4)
      (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - s (v + u)) - A n a v u‖ ≤ 1 / 3000 := by
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
    let z : ℂ := -I * (u : ℂ) * (Real.log n : ℂ)
    have he : (n : ℂ) ^ ((a : ℂ) - s (v + u)) =
        (n : ℂ) ^ ((a : ℂ) - s v) * Complex.exp z := by
      rw [show (a : ℂ) - s (v + u) = ((a : ℂ) - s v) + (-I * (u : ℂ)) by dsimp [s]; push_cast; ring,
        Complex.cpow_add _ _ hn0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
      dsimp [z]
      congr 1
      ring
    rw [he]
    dsimp only [A]
    have hc := happ v hv0 hv n hn a ha ha1
    have hcNorm := hp v hv0 hv n hn a ha1
    have ho := hOff n hn u hu
    have hoNorm := hOffnorm n hn u hu
    calc
      _ = ‖(n : ℂ) ^ ((a : ℂ) - s v) * (Complex.exp z - Off n u) +
          ((n : ℂ) ^ ((a : ℂ) - s v) - T n a v) * Off n u‖ := by congr 1; ring
      _ ≤ ‖(n : ℂ) ^ ((a : ℂ) - s v)‖ * ‖Complex.exp z - Off n u‖ +
          ‖(n : ℂ) ^ ((a : ℂ) - s v) - T n a v‖ * ‖Off n u‖ := by
        grw [norm_add_le]; simp only [norm_mul]; exact le_rfl
      _ ≤ 4 * (1 / 1000000) + (1 / 8000) * 2 := by gcongr
      _ ≤ _ := by norm_num
  let W : QuadraticAlgebra ℚ (-1) 0 := ⟨0, 1⟩
  let v : ℕ → ℚ := fun j => (49 + 2 * j) / 4
  let S : ℕ → QuadraticAlgebra ℚ (-1) 0 := fun j => ⟨1 / 2, v j⟩
  let E : ℕ → ℚ → ℕ → QuadraticAlgebra ℚ (-1) 0 := fun n a j =>
    ∑ k ∈ Finset.range 128, ((k.factorial : ℚ)⁻¹) •
      (((QuadraticAlgebra.C a) - S j) * QuadraticAlgebra.C (qr n)) ^ k
  let V : ℕ → ℕ → QuadraticAlgebra ℚ (-1) 0 := fun n k =>
    ((k.factorial : ℚ)⁻¹) • ((-W) * QuadraticAlgebra.C (qr n)) ^ k
  let B0 := fun j k => (∑ n ∈ Finset.Ico (1 : ℕ) 10, E n 0 j * V n k) +
    (1 / 2 : ℚ) • (E 10 0 j * V 10 k)
  let B1 := fun j k => (1 / 12 : ℚ) • (E 10 (-1) j * V 10 k)
  let B3 := fun j k => -(1 / 720 : ℚ) • (E 10 (-3) j * V 10 k)
  let BT := fun j k => E 10 1 j * V 10 k
  let H := fun j k r =>
    let sj := S j
    match r with
    | 0 => B0 j k + sj * B1 j k + sj * (sj + 1) * (sj + 2) * B3 j k
    | 1 => W * B1 j k + W * (3 * sj ^ 2 + 6 * sj + 2) * B3 j k
    | 2 => -(3 * sj + 3) * B3 j k
    | 3 => -W * B3 j k
    | _ => 0
  let C := fun j k r =>
    let d0 : QuadraticAlgebra ℚ (-1) 0 := QuadraticAlgebra.C ((v j) ^ 2 + 1 / 4)
    let d1 : QuadraticAlgebra ℚ (-1) 0 := QuadraticAlgebra.C (2 * v j)
    match r with
    | 0 => d0 * H j k 0 + (⟨-1 / 2, -v j⟩ : QuadraticAlgebra ℚ (-1) 0) * BT j k
    | 1 => d1 * H j k 0 + d0 * H j k 1 - W * BT j k
    | 2 => H j k 0 + d1 * H j k 1 + d0 * H j k 2
    | 3 => H j k 1 + d1 * H j k 2 + d0 * H j k 3
    | 4 => H j k 2 + d1 * H j k 3
    | 5 => H j k 3
    | _ => 0
  have hNum (j : ℕ) (hj : j ≤ 3) : (C j 0 0).im +
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
        if k + r = 0 then 0 else |(C j k r).im| * (1 / 4 : ℚ) ^ (k + r)) ≤ -15 := by
    interval_cases j <;> decide +kernel
  have hcoeff (F : ℕ → ℕ → ℂ) (u : ℝ) (hu : |u| ≤ 1 / 4) :
      (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, F k r * (u : ℂ) ^ (k + r)).im ≤
        (F 0 0).im + ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          if k + r = 0 then 0 else |(F k r).im| * (1 / 4 : ℝ) ^ (k + r) := by
    have hterm (k r : ℕ) : (F k r * (u : ℂ) ^ (k + r)).im = (F k r).im * u ^ (k + r) := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
    simp only [Complex.im_sum, hterm]
    have hdelta : (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
        if k + r = 0 then (F 0 0).im else 0) = (F 0 0).im := by
      norm_num [Finset.sum_range_succ]
    calc
      _ ≤ ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          ((if k + r = 0 then (F 0 0).im else 0) +
            (if k + r = 0 then 0 else |(F k r).im| * (1 / 4 : ℝ) ^ (k + r))) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : k + r = 0
        · have hk0 : k = 0 := by omega
          have hr0 : r = 0 := by omega
          subst k; subst r
          simp
        · simp only [h, ite_false, zero_add]
          calc
            (F k r).im * u ^ (k + r) ≤ |(F k r).im * u ^ (k + r)| := le_abs_self _
            _ = |(F k r).im| * |u| ^ (k + r) := by rw [abs_mul, abs_pow]
            _ ≤ _ := by gcongr
      _ = _ := by simp only [Finset.sum_add_distrib, hdelta]
  let e : QuadraticAlgebra ℚ (-1) 0 →ₐ[ℚ] ℂ :=
    QuadraticAlgebra.lift ⟨I, by norm_num [smul_eq_mul]⟩
  have he_im (x : QuadraticAlgebra ℚ (-1) 0) : (e x).im = (x.im : ℝ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_C (a : ℚ) : e (QuadraticAlgebra.C a) = (a : ℂ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_W : e W = I := by norm_num [e, W, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_S (j : ℕ) : e (S j) = s (v j : ℝ) := by
    norm_num [e, QuadraticAlgebra.lift, S, s, Algebra.smul_def]
  have he_mk (a b : ℚ) : e (⟨a, b⟩ : QuadraticAlgebra ℚ (-1) 0) = (a : ℂ) + b * I := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_E (n : ℕ) (a : ℚ) (j : ℕ) : e (E n a j) = T n (a : ℝ) (v j : ℝ) := by
    simp only [E, T, map_sum, map_smul, map_pow, map_mul, map_sub, he_S, he_C]
    apply Finset.sum_congr rfl
    intro k hk
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_V (n k : ℕ) : e (V n k) = ((-I) * (q n : ℂ)) ^ k / (k.factorial : ℂ) := by
    simp only [V, map_smul, map_pow, map_mul, map_neg, he_W, he_C]
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_A (n : ℕ) (a : ℚ) (j : ℕ) (u : ℝ) :
      A n (a : ℝ) (v j : ℝ) u =
        ∑ k ∈ Finset.range 12, e (E n a j * V n k) * (u : ℂ) ^ k := by
    dsimp only [A, Off]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul, he_E, he_V]
    ring
  let F : ℕ → ℝ → ℂ := fun j u =>
    ∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ (k + r)
  have hFim (j : ℕ) (hj : j ≤ 3) (u : ℝ) (hu : |u| ≤ 1 / 4) : (F j u).im ≤ -15 := by
    have hh := hcoeff (fun k r => e (C j k r)) u hu
    simp only [he_im] at hh
    apply hh.trans
    have hc : (((C j 0 0).im +
        (∑ k ∈ Finset.range 12, ∑ r ∈ Finset.range 6,
          if k + r = 0 then 0 else |(C j k r).im| * (1 / 4 : ℚ) ^ (k + r)) : ℚ) : ℝ) ≤ ((-15 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (hNum j hj)
    push_cast at hc
    simp only [apply_ite] at hc
    push_cast at hc
    exact hc
  have hinner (j k : ℕ) (u : ℝ) :
      (∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ r) =
        (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) *
          (e (B0 j k) + s ((v j : ℝ) + u) * e (B1 j k) +
            s ((v j : ℝ) + u) * (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) * e (B3 j k)) +
        star (s ((v j : ℝ) + u) - 1) * e (BT j k) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, C, H]
    generalize B0 j k = b0
    generalize B1 j k = b1
    generalize B3 j k = b3
    generalize BT j k = bt
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_ofNat, he_C, he_S, he_W, he_mk]
    apply Complex.ext <;>
      norm_num [s, S, W, e, QuadraticAlgebra.lift, Algebra.smul_def, pow_succ, Complex.mul_re, Complex.mul_im] <;>
      push_cast <;> ring
  have hB0c (j k : ℕ) : e (B0 j k) =
      (∑ n ∈ Finset.Ico (1 : ℕ) 10, e (E n 0 j * V n k)) + e (E 10 0 j * V 10 k) / 2 := by
    simp only [B0, map_add, map_sum, map_smul]
    simp only [Algebra.smul_def]
    norm_num
    ring
  have hB1c (j k : ℕ) : e (B1 j k) = e (E 10 (-1) j * V 10 k) / 12 := by
    simp [B1, Algebra.smul_def, div_eq_mul_inv]
    ring
  have hB3c (j k : ℕ) : e (B3 j k) = -e (E 10 (-3) j * V 10 k) / 720 := by
    simp [B3, Algebra.smul_def, div_eq_mul_inv]
    ring
  have hBTc (j k : ℕ) : e (BT j k) = e (E 10 1 j * V 10 k) := rfl
  have hB0sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B0 j k) * (u : ℂ) ^ k) =
        (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) + A 10 0 (v j : ℝ) u / 2 := by
    simp_rw [hB0c, add_mul, Finset.sum_add_distrib, Finset.sum_mul, div_mul_eq_mul_div]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [← he_A]
    norm_num
  have hB1sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B1 j k) * (u : ℂ) ^ k) = A 10 (-1) (v j : ℝ) u / 12 := by
    simp_rw [hB1c, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← he_A]
    norm_num
  have hB3sum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (B3 j k) * (u : ℂ) ^ k) = -A 10 (-3) (v j : ℝ) u / 720 := by
    simp_rw [hB3c, div_mul_eq_mul_div, neg_mul]
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← he_A]
    norm_num
  have hBTsum (j : ℕ) (u : ℝ) :
      (∑ k ∈ Finset.range 12, e (BT j k) * (u : ℂ) ^ k) = A 10 1 (v j : ℝ) u := by
    simp_rw [hBTc]
    rw [← he_A]
    norm_num
  have hfactor (j : ℕ) (u : ℝ) : F j u =
      ∑ k ∈ Finset.range 12, (∑ r ∈ Finset.range 6, e (C j k r) * (u : ℂ) ^ r) * (u : ℂ) ^ k := by
    dsimp only [F]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_add]
    ring
  have hFsums (j : ℕ) (u : ℝ) : F j u =
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * (∑ k ∈ Finset.range 12, e (B0 j k) * (u : ℂ) ^ k) +
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * s ((v j : ℝ) + u) *
        (∑ k ∈ Finset.range 12, e (B1 j k) * (u : ℂ) ^ k) +
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * s ((v j : ℝ) + u) *
        (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) *
        (∑ k ∈ Finset.range 12, e (B3 j k) * (u : ℂ) ^ k) +
      star (s ((v j : ℝ) + u) - 1) * (∑ k ∈ Finset.range 12, e (BT j k) * (u : ℂ) ^ k) := by
    rw [hfactor]
    simp_rw [hinner]
    simp only [Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    generalize e (B0 j k) = b0
    generalize e (B1 j k) = b1
    generalize e (B3 j k) = b3
    generalize e (BT j k) = bt
    ring
  let EMA : ℕ → ℝ → ℂ := fun j u =>
    (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) +
      A 10 1 (v j : ℝ) u / (s ((v j : ℝ) + u) - 1) + A 10 0 (v j : ℝ) u / 2 +
      s ((v j : ℝ) + u) * A 10 (-1) (v j : ℝ) u / 12 -
      s ((v j : ℝ) + u) * (s ((v j : ℝ) + u) + 1) * (s ((v j : ℝ) + u) + 2) * A 10 (-3) (v j : ℝ) u / 720
  have hscaled (j : ℕ) (u : ℝ) : F j u =
      (((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) * EMA j u := by
    rw [hFsums, hB0sum, hB1sum, hB3sum, hBTsum]
    have hne : s ((v j : ℝ) + u) - 1 ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      norm_num [s] at hr
    have hd : ((((v j : ℝ) + u) ^ 2 + 1 / 4 : ℝ) : ℂ) =
        (s ((v j : ℝ) + u) - 1) * star (s ((v j : ℝ) + u) - 1) := by
      change _ = (s ((v j : ℝ) + u) - 1) * (starRingEnd ℂ) (s ((v j : ℝ) + u) - 1)
      rw [Complex.mul_conj]
      congr 1
      norm_num [Complex.normSq_apply, s]
      ring
    dsimp only [EMA]
    generalize (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) = az
    generalize A 10 1 (v j : ℝ) u = a1
    generalize A 10 0 (v j : ℝ) u = a0
    generalize A 10 (-1) (v j : ℝ) u = am1
    generalize A 10 (-3) (v j : ℝ) u = am3
    rw [hd]
    field_simp [hne]
    ring
  have hcover : ∃ j : ℕ, j ≤ 3 ∧ |t - (v j : ℝ)| ≤ 1 / 4 := by
    by_cases h0 : t ≤ 25 / 2
    · refine ⟨0, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    by_cases h1 : t ≤ 13
    · refine ⟨1, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    by_cases h2 : t ≤ 27 / 2
    · refine ⟨2, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
    · refine ⟨3, by norm_num, ?_⟩
      norm_num [v]
      rw [abs_le]
      constructor <;> linarith
  obtain ⟨j, hj, hu0⟩ := hcover
  let u : ℝ := t - (v j : ℝ)
  have hu : |u| ≤ 1 / 4 := hu0
  have htu : (v j : ℝ) + u = t := by dsimp [u]; ring
  have hjR : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  have hv0 : 0 ≤ (v j : ℝ) := by norm_num [v]; positivity
  have hv14 : (v j : ℝ) ≤ 14 := by norm_num [v]; linarith
  have ht0p : 0 ≤ t := by linarith
  have hsplus (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 2) : ‖s t + a‖ ≤ 20 := by
    have hh := hfac t ht0p ht (-a) (by linarith) (by linarith)
    simp only [ofReal_neg] at hh
    rw [show -(a : ℂ) - s t = -(s t + a) by ring, norm_neg] at hh
    linarith
  have hs0 : ‖s t‖ ≤ 20 := by simpa using hsplus 0 (by norm_num) (by norm_num)
  have hs1 : ‖s t + 1‖ ≤ 20 := by simpa using hsplus 1 (by norm_num) (by norm_num)
  have hs2 : ‖s t + 2‖ ≤ 20 := by simpa using hsplus 2 (by norm_num) (by norm_num)
  have hP : ‖s t * (s t + 1) * (s t + 2)‖ ≤ 8000 := by
    simp only [norm_mul]
    calc
      ‖s t‖ * ‖s t + 1‖ * ‖s t + 2‖ ≤ 20 * 20 * 20 := by gcongr
      _ = _ := by norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖s t - 1‖ := by
    have hh := Complex.abs_re_le_norm (s t - 1)
    norm_num [s] at hh
    exact hh
  have hinv : ‖(s t - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num [one_div] at hh
    exact hh
  have h10a := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) 1 (by norm_num) (by norm_num)
  have h10b := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) 0 (by norm_num) (by norm_num)
  have h10c := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) (-1) (by norm_num) (by norm_num)
  have h10d := hA (v j : ℝ) hv0 hv14 u hu 10 (by norm_num) (-3) (by norm_num) (by norm_num)
  rw [htu] at h10a h10b h10c h10d
  norm_num only [ofReal_one, ofReal_zero, ofReal_neg, zero_sub, ofReal_ofNat] at h10a h10b h10c h10d
  rw [show (-1 : ℂ) - s t = -s t - 1 by ring] at h10c
  rw [show (-3 : ℂ) - s t = -(s t) - 3 by ring] at h10d
  let AA : ℂ := (∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-(s t))) - ∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u
  have hnA : ‖AA‖ ≤ 9 / 3000 := by
    dsimp [AA]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, ‖(n : ℂ) ^ (-(s t)) - A n 0 (v j : ℝ) u‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, (1 / 3000 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : n ∈ Finset.Icc (1 : ℕ) 10 := by
          simp only [Finset.mem_Icc, Finset.mem_Ico] at *
          omega
        simpa only [ofReal_zero, zero_sub, htu] using hA (v j : ℝ) hv0 hv14 u hu n hn' 0 (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hnB : ‖((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1)‖ ≤ 2 / 3000 := by
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖(10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u‖ * ‖(s t - 1)⁻¹‖ ≤ (1 / 3000) * 2 := by gcongr
      _ = _ := by norm_num
  have hnC : ‖((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2‖ ≤ 1 / 6000 := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    linarith
  have hnD : ‖s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12‖ ≤ 2 / 3000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s t‖ * ‖(10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u‖ / 12 ≤ 20 * (1 / 3000) / 12 := by gcongr
      _ ≤ _ := by norm_num
  have hnE : ‖s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720‖ ≤ 12 / 3000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s t * (s t + 1) * (s t + 2)‖ * ‖(10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u‖ / 720 ≤ 8000 * (1 / 3000) / 720 := by gcongr
      _ ≤ _ := by norm_num
  have hErr : ‖EM10 (s t) - EMA j u‖ ≤ 1 / 100 := by
    have he : EM10 (s t) - EMA j u = AA + ((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1) +
        ((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2 + s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12 -
        s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720 := by
      dsimp only [EM10, EMA, AA]
      rw [htu]
      generalize (∑ n ∈ Finset.Ico (1 : ℕ) 10, A n 0 (v j : ℝ) u) = az
      generalize A 10 1 (v j : ℝ) u = a1
      generalize A 10 0 (v j : ℝ) u = a0
      generalize A 10 (-1) (v j : ℝ) u = am1
      generalize A 10 (-3) (v j : ℝ) u = am3
      ring
    rw [he]
    calc
      _ ≤ ‖AA‖ + ‖((10 : ℂ) ^ (1 - s t) - A 10 1 (v j : ℝ) u) / (s t - 1)‖ + ‖((10 : ℂ) ^ (-(s t)) - A 10 0 (v j : ℝ) u) / 2‖ +
          ‖s t * ((10 : ℂ) ^ (-s t - 1) - A 10 (-1) (v j : ℝ) u) / 12‖ +
          ‖s t * (s t + 1) * (s t + 2) * ((10 : ℂ) ^ (-(s t) - 3) - A 10 (-3) (v j : ℝ) u) / 720‖ := by
        grw [norm_sub_le, norm_add_le, norm_add_le, norm_add_le]
      _ ≤ 9 / 3000 + 2 / 3000 + 1 / 6000 + 2 / 3000 + 12 / 3000 := by gcongr
      _ ≤ _ := by norm_num
  let D : ℝ := t ^ 2 + 1 / 4
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDmax : D ≤ 785 / 4 := by
    dsimp [D]
    nlinarith [mul_nonneg ht0p (sub_nonneg.mpr ht)]
  have hscale : F j u = (D : ℂ) * EMA j u := by
    simpa only [htu, D] using hscaled j u
  have hscaleErr : ‖(D : ℂ) * EM10 (s t) - F j u‖ ≤ D / 100 := by
    rw [hscale, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD0]
    have hh := mul_le_mul_of_nonneg_left hErr hD0
    convert hh using 1
    ring
  have him := (le_abs_self (((D : ℂ) * EM10 (s t) - F j u).im)).trans
    ((Complex.abs_im_le_norm ((D : ℂ) * EM10 (s t) - F j u)).trans hscaleErr)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_add] at him
  have hn := (neg_le_abs (EM10 (s t)).im).trans (Complex.abs_im_le_norm (EM10 (s t)))
  have hmult := mul_le_mul_of_nonneg_left hn hD0
  have hLB : 15 ≤ D * (‖EM10 (s t)‖ + 1 / 100) := by
    have hf := hFim j hj u hu
    nlinarith
  change 1 / 20 ≤ ‖EM10 (s t)‖
  by_contra hlt
  have hsmall : ‖EM10 (s t)‖ < 1 / 20 := lt_of_not_ge hlt
  have hU := mul_le_mul_of_nonneg_left (show ‖EM10 (s t)‖ + 1 / 100 ≤ 3 / 50 by linarith) hD0
  nlinarith

/-- `ζ(1/2 + it) ≠ 0` for `0 ≤ t ≤ 14`, CONDITIONAL ON the five leaves. -/
theorem zeta_half_ne_zero (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    ζ ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hR := em10_remainder s (by rw [hre]; norm_num) hs1
  rw [hre] at hR
  have hR2 := rem_small t ht0 ht
  have hL : 1 / 20 ≤ ‖EM10 s‖ := by
    rcases le_total t 7 with h7 | h7
    · exact em10_lower_a t ht0 h7
    rcases le_total t 12 with h12 | h12
    · exact em10_lower_b t h7 h12
    · exact em10_lower_c t h12 ht
  intro h0
  rw [h0, zero_sub, norm_neg] at hR
  have : ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (10 : ℝ) ^ (-((1 / 2 : ℝ) + 3)) /
      (720 * ((1 / 2 : ℝ) + 3)) ≤ 1 / 100 := by simpa [hsdef] using hR2
  linarith

/-- ASSEMBLY. Under RH, every ordinate `gZ i` of a nontrivial zero of ζ has `|gZ i| ≥ 14`.
CONDITIONAL ON the leaves `em10_remainder`, `rem_small`, `em10_lower_a`, `em10_lower_b`,
`em10_lower_c`. -/
theorem ordinates14_gZ_of_RH (hRH : RiemannHypothesis) :
    LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ := by
  intro i
  by_contra hlt
  rw [not_le] at hlt
  have hz : ζ (i.1 : ℂ) = 0 := i.1.2.1
  have hre : ((i.1 : ℂ)).re = 1 / 2 := re_half_of_RH hRH i.1
  set g := gZ i with hg
  have hgim : ((i.1 : ℂ)).im = g := rfl
  have hrho : (i.1 : ℂ) = (1 / 2 : ℂ) + g * I := by
    apply Complex.ext <;> simp [hre, hgim]
  rcases le_total 0 g with h0 | h0
  · apply zeta_half_ne_zero g h0 (by rw [abs_of_nonneg h0] at hlt; linarith)
    rw [← hrho]; exact hz
  · apply zeta_half_ne_zero (-g) (by linarith) (by rw [abs_of_nonpos h0] at hlt; linarith)
    have hc : (1 / 2 : ℂ) + ((-g : ℝ) : ℂ) * I = (starRingEnd ℂ) (i.1 : ℂ) := by
      rw [hrho]; apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj, hz, map_zero]

/-- An absolute reverse triangle estimate from the leading term is negative even before
including the other summands. This records a limitation of that numerical proof strategy. -/
theorem em10_triangle_obstruction (t : ℝ) :
    1 - ‖(2 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ -
      ‖(3 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ < 0 := by
  have h2 : ‖(2 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ = (Real.sqrt 2)⁻¹ := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 2 by norm_num)
      (-((1 / 2 : ℂ) + t * I))
    norm_num at hh
    have hn : ‖(2 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      convert hh using 1
      congr 2
      ring
    rw [hn, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have h3 : ‖(3 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ = (Real.sqrt 3)⁻¹ := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 3 by norm_num)
      (-((1 / 2 : ℂ) + t * I))
    norm_num at hh
    have hn : ‖(3 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ = (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      convert hh using 1
      congr 2
      ring
    rw [hn, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  rw [h2, h3]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hi2 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Real.sqrt 2) hs2
  have hi3 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Real.sqrt 3) hs3
  norm_num [one_div] at hi2 hi3
  linarith

/-- Exact real axis calibration for the numerical lower bound leaves. -/
theorem em10_lower_zero : 1 / 5 ≤ ‖EM10 (1 / 2 : ℂ)‖ := by
  let S : ℝ := ∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℝ) ^ (-(1 / 2 : ℝ))
  let R : ℝ := S - 2 * (10 : ℝ) ^ (1 / 2 : ℝ) + (10 : ℝ) ^ (-(1 / 2 : ℝ)) / 2 +
    (10 : ℝ) ^ (-(3 / 2 : ℝ)) / 24 - (10 : ℝ) ^ (-(7 / 2 : ℝ)) / 384
  have hn (n : ℕ) : (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
    convert Complex.ofReal_cpow (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (-(1 / 2 : ℝ)) using 1
    norm_num
  have hsum : (S : ℂ) = ∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
    dsimp [S]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => hn n)
  have hp (a : ℝ) : (((10 : ℝ) ^ a : ℝ) : ℂ) = (10 : ℂ) ^ (a : ℂ) := by
    simpa using Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 10) a
  have he : EM10 (1 / 2 : ℂ) = (R : ℂ) := by
    dsimp [R, EM10]
    push_cast
    rw [hsum]
    simp only [hp]
    norm_num
    ring
  have hsqrt : 3 ≤ Real.sqrt 10 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have hsqrt2 : 4 / 3 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hpow2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, ← one_div]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 3) hsqrt2
    norm_num at h
    simpa only [one_div] using h
  have hpow4 : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  have hS : S ≤ 11 / 2 := by
    dsimp [S]
    norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
    have h3 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have h5 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 5) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have h6 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 6) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have h7 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 7) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have h8 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 8) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have h9 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 9) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    linarith
  have hpneg : (10 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
    calc
      _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
      _ = _ := hpow4
  have hpneg3 : (10 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 / 10 := by
    calc
      _ ≤ (10 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hR : R ≤ -(1 / 5 : ℝ) := by
    dsimp [R]
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 10 by norm_num) (-(7 / 2 : ℝ))]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  have hab := neg_le_abs R
  linarith

/-- Uniform derivative control for certified grids in the three numerical leaves. -/
theorem em10_deriv_half_bound (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    DifferentiableAt ℂ EM10 ((1 / 2 : ℂ) + t * I) ∧
      ‖deriv EM10 ((1 / 2 : ℂ) + t * I)‖ ≤ 100 := by
  let s : ℂ := (1 / 2 : ℂ) + t * I
  let L : ℂ := Complex.log 10
  have hre : s.re = 1 / 2 := by simp [s]
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hlog10 : Real.log 10 ≤ 3 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlog : ‖L‖ ≤ 3 := by
    have he : L = (Real.log 10 : ℂ) := by
      simp [L]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by norm_num))]
    exact hlog10
  have hnormpow (a : ℝ) : ‖(10 : ℂ) ^ ((a : ℂ) - s)‖ = (10 : ℝ) ^ (a - 1 / 2) := by
    convert Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 10) ((a : ℂ) - s) using 1
    all_goals norm_num [hre]
  have hp1 : ‖(10 : ℂ) ^ (1 - s)‖ ≤ 4 := by
    have he := hnormpow 1
    norm_num at he
    rw [he, ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have hp0 : ‖(10 : ℂ) ^ (-s)‖ ≤ 1 := by
    have he := hnormpow 0
    norm_num at he
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hpm1 : ‖(10 : ℂ) ^ (-s - 1)‖ ≤ 1 / 10 := by
    have he := hnormpow (-1)
    norm_num at he
    rw [show -s - 1 = (-1 : ℂ) - s by ring, he]
    calc
      _ ≤ (10 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hpm3 : ‖(10 : ℂ) ^ (-s - 3)‖ ≤ 1 / 1000 := by
    have he := hnormpow (-3)
    norm_num at he
    rw [show -s - 3 = (-3 : ℂ) - s by ring, he]
    calc
      _ ≤ (10 : ℝ) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hs_norm : ‖s‖ ≤ 15 := by
    have hs_sq : ‖s‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [s]
      ring
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht), norm_nonneg s]
  have hs0 : ‖s‖ ≤ 20 := by linarith
  have hsplus (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 3) : ‖s + a‖ ≤ 20 := by
    calc
      _ ≤ ‖s‖ + ‖(a : ℂ)‖ := norm_add_le _ _
      _ ≤ 15 + 3 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]; linarith
      _ ≤ _ := by norm_num
  have hsplus1 : ‖s + 1‖ ≤ 20 := by simpa using hsplus 1 (by norm_num) (by norm_num)
  have hsplus2 : ‖s + 2‖ ≤ 20 := by simpa using hsplus 2 (by norm_num) (by norm_num)
  have hden : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have hh := Complex.abs_re_le_norm (s - 1)
    norm_num [hre] at hh
    exact hh
  have hinvnorm : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num [one_div] at hh
    exact hh
  have hdInvnorm : ‖(-1 : ℂ) / (s - 1) ^ 2‖ ≤ 4 := by
    rw [norm_div, norm_neg, norm_one, norm_pow]
    have hsq : (1 / 4 : ℝ) ≤ ‖s - 1‖ ^ 2 := by nlinarith [norm_nonneg (s - 1)]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hsq
    norm_num at hh
    simpa only [one_div] using hh
  have hpow (a : ℂ) : HasDerivAt (fun z : ℂ => (10 : ℂ) ^ (a - z))
      (-L * (10 : ℂ) ^ (a - s)) s := by
    convert ((hasDerivAt_id s).const_sub a).const_cpow (Or.inl (by norm_num : (10 : ℂ) ≠ 0)) using 1
    all_goals simp only [L, id_eq]
    all_goals ring
  have hterm (n : ℕ) (hn : n ∈ Finset.Ico (1 : ℕ) 10) :
      HasDerivAt (fun z : ℂ => (n : ℂ) ^ (-z))
        (-(Complex.log n) * (n : ℂ) ^ (-s)) s := by
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Finset.mem_Ico.mp hn).1)
    convert (hasDerivAt_neg s).const_cpow (Or.inl hn0) using 1
    ring
  let A : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 10, -(Complex.log n) * (n : ℂ) ^ (-s)
  have hA : HasDerivAt (fun z : ℂ => ∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-z)) A s :=
    HasDerivAt.fun_sum hterm
  have hnA : ‖A‖ ≤ 27 := by
    dsimp [A]
    calc
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, ‖-(Complex.log n) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, (3 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, hn10⟩ := Finset.mem_Ico.mp hn
        have hn0 : 0 < n := by omega
        have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hnlog : ‖Complex.log (n : ℂ)‖ ≤ 3 := by
          rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.log_nonneg hnreal)]
          exact (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn10.le)).trans hlog10
        have hnpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
          rw [Complex.norm_natCast_cpow_of_pos hn0]
          simp only [neg_re, hre]
          exact Real.rpow_le_one_of_one_le_of_nonpos hnreal (by norm_num)
        rw [norm_mul, norm_neg]
        calc
          _ ≤ 3 * 1 := mul_le_mul hnlog hnpow (norm_nonneg _) (by norm_num)
          _ = _ := by norm_num
      _ = 27 := by norm_num
  let P : ℂ := s * (s + 1) * (s + 2)
  let Q : ℂ := (s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)
  have hP : HasDerivAt (fun z : ℂ => z * (z + 1) * (z + 2)) Q s := by
    convert ((hasDerivAt_id s).mul ((hasDerivAt_id s).add_const 1)).mul ((hasDerivAt_id s).add_const 2) using 1
    · funext z
      simp only [Pi.mul_apply, id_eq]
    · dsimp [Q]
      ring
  have hnP : ‖P‖ ≤ 8000 := by
    dsimp [P]
    rw [norm_mul, norm_mul]
    calc
      ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ 20 * 20 * 20 := by gcongr
      _ = _ := by norm_num
  have hnQ : ‖Q‖ ≤ 1200 := by
    dsimp [Q]
    calc
      _ ≤ ‖(s + 1) * (s + 2)‖ + ‖s * (s + 2)‖ + ‖s * (s + 1)‖ := by grw [norm_add_le, norm_add_le]
      _ ≤ 20 * 20 + 20 * 20 + 20 * 20 := by simp only [norm_mul]; gcongr
      _ = _ := by norm_num
  let B : ℂ := (-L * (10 : ℂ) ^ (1 - s)) * (s - 1)⁻¹ + (10 : ℂ) ^ (1 - s) * (-1 / (s - 1) ^ 2)
  let C : ℂ := (-L * (10 : ℂ) ^ (-s)) / 2
  let D : ℂ := ((10 : ℂ) ^ (-s - 1) + s * (-L * (10 : ℂ) ^ (-s - 1))) / 12
  let E : ℂ := (Q * (10 : ℂ) ^ (-s - 3) + P * (-L * (10 : ℂ) ^ (-s - 3))) / 720
  have H : HasDerivAt EM10 (A + B + C + D - E) s := by
    have hInv := ((hasDerivAt_id s).sub_const 1).inv (sub_ne_zero.mpr hs1)
    have HH := (((hA.add ((hpow 1).mul hInv)).add ((hpow 0).div_const 2)).add
      (((hasDerivAt_id s).mul (hpow (-1))).div_const 12)).sub ((hP.mul (hpow (-3))).div_const 720)
    convert HH using 1
    · funext z
      simp only [EM10, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.inv_apply, id_eq, zero_sub, show (-1 : ℂ) - z = -z - 1 by ring,
        show (-3 : ℂ) - z = -z - 3 by ring, div_eq_mul_inv]
    · dsimp [B, C, D, E, P]
      simp only [zero_sub, show (-1 : ℂ) - s = -s - 1 by ring,
        show (-3 : ℂ) - s = -s - 3 by ring]
      ring
  have hnB : ‖B‖ ≤ 40 := by
    dsimp [B]
    calc
      _ ≤ ‖-L * (10 : ℂ) ^ (1 - s)‖ * ‖(s - 1)⁻¹‖ + ‖(10 : ℂ) ^ (1 - s)‖ * ‖(-1 : ℂ) / (s - 1) ^ 2‖ := by grw [norm_add_le]; simp only [norm_mul]; exact le_rfl
      _ ≤ 3 * 4 * 2 + 4 * 4 := by rw [norm_mul, norm_neg]; gcongr
      _ = _ := by norm_num
  have hnC : ‖C‖ ≤ 2 := by
    dsimp [C]
    rw [norm_div, norm_mul, norm_neg]
    norm_num only [norm_ofNat]
    calc
      ‖L‖ * ‖(10 : ℂ) ^ (-s)‖ / 2 ≤ 3 * 1 / 2 := by gcongr
      _ ≤ _ := by norm_num
  have hnD : ‖D‖ ≤ 1 := by
    dsimp [D]
    rw [norm_div]
    norm_num only [norm_ofNat]
    calc
      _ ≤ (‖(10 : ℂ) ^ (-s - 1)‖ + ‖s * (-L * (10 : ℂ) ^ (-s - 1))‖) / 12 := by gcongr; exact norm_add_le _ _
      _ ≤ (1 / 10 + 20 * (3 * (1 / 10))) / 12 := by simp only [norm_mul, norm_neg]; gcongr
      _ ≤ _ := by norm_num
  have hnE : ‖E‖ ≤ 1 := by
    dsimp [E]
    rw [norm_div]
    norm_num only [norm_ofNat]
    calc
      _ ≤ (‖Q * (10 : ℂ) ^ (-s - 3)‖ + ‖P * (-L * (10 : ℂ) ^ (-s - 3))‖) / 720 := by gcongr; exact norm_add_le _ _
      _ ≤ (1200 * (1 / 1000) + 8000 * (3 * (1 / 1000))) / 720 := by simp only [norm_mul, norm_neg]; gcongr
      _ ≤ _ := by norm_num
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.deriv]
  calc
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by grw [norm_sub_le, norm_add_le, norm_add_le, norm_add_le]
    _ ≤ 27 + 40 + 2 + 1 + 1 := by gcongr
    _ ≤ 100 := by norm_num

/-- The derivative estimate supplies uniform Lipschitz control on the half line segment. -/
theorem em10_half_lipschitz (u v : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 14) (hv0 : 0 ≤ v) (hv : v ≤ 14) :
    ‖EM10 ((1 / 2 : ℂ) + u * I) - EM10 ((1 / 2 : ℂ) + v * I)‖ ≤ 100 * |u - v| := by
  have hD := em10_deriv_half_bound
  have hdf (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 14) :
      HasDerivAt (fun y : ℝ => EM10 ((1 / 2 : ℂ) + y * I))
        (deriv EM10 ((1 / 2 : ℂ) + x * I) * I) x := by
    have hc := (hD x hx.1 hx.2).1.hasDerivAt
    have hh := hc.comp (x : ℂ) (((hasDerivAt_id (x : ℂ)).mul_const I).const_add (1 / 2))
    simpa only [one_mul, Function.comp_apply, id_eq] using hh.comp_ofReal
  have hn (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 14) :
      ‖deriv EM10 ((1 / 2 : ℂ) + x * I) * I‖ ≤ 100 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    exact (hD x hx.1 hx.2).2
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hdf x hx).hasDerivWithinAt) hn (convex_Icc (0 : ℝ) 14)
    (show v ∈ Set.Icc (0 : ℝ) 14 from ⟨hv0, hv⟩)
    (show u ∈ Set.Icc (0 : ℝ) 14 from ⟨hu0, hu⟩)
  simpa only [Real.norm_eq_abs] using hh

/-- An initial subinterval of the first numerical leaf is certified exactly. -/
theorem em10_lower_initial (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 1000) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  have hL := em10_half_lipschitz
  have ht14 : t ≤ 14 := le_trans ht (by norm_num)
  have hh := hL 0 t (by norm_num) (by norm_num) ht0 ht14
  norm_num only [ofReal_zero, zero_mul, add_zero, zero_sub, abs_neg, abs_of_nonneg ht0] at hh
  have hn := norm_sub_norm_le (EM10 (1 / 2 : ℂ)) (EM10 ((1 / 2 : ℂ) + t * I))
  have hz := em10_lower_zero
  linarith

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- An exact rational Taylor certificate at the tight endpoint of the third numerical leaf. -/
theorem em10_lower_fourteen : 7 / 100 ≤ ‖EM10 ((1 / 2 : ℂ) + (14 : ℝ) * I)‖ := by
  let qr : ℕ → ℚ := fun n =>
    match n with
    | 1 => 0
    | 2 => 693147 / 1000000
    | 3 => 1098612 / 1000000
    | 4 => 1386294 / 1000000
    | 5 => 1609437 / 1000000
    | 6 => 1791759 / 1000000
    | 7 => 1945910 / 1000000
    | 8 => 2079441 / 1000000
    | 9 => 2197224 / 1000000
    | 10 => 2302585 / 1000000
    | _ => 0
  let q : ℕ → ℝ := fun n => (qr n : ℝ)
  have hlog7 : |Real.log 7 - q 7| ≤ 1 / 1000000 := by
    have hh := Real.abs_log_sub_add_sum_range_le (x := 1 / 8) (by norm_num) 10
    have he : Real.log (1 - (1 / 8 : ℝ)) = Real.log 7 - 3 * Real.log 2 := by
      rw [show (1 - (1 / 8 : ℝ)) = 7 / 8 by norm_num,
        Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
      have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [he8]
    rw [he] at hh
    norm_num [Finset.sum_range_succ, q, qr] at hh ⊢
    rw [abs_le] at hh ⊢
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  norm_num only [q, qr] at hlog7
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by norm_num [← Real.log_mul]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogs (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) :
      |Real.log n - q n| ≤ 1 / 1000000 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, hlog4, hlog6, hlog8, hlog9, Real.log_ten_eq, qr]
    all_goals rw [abs_le]
    all_goals constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9,
      (abs_le.mp hlog7).1, (abs_le.mp hlog7).2]
  let s : ℂ := (1 / 2 : ℂ) + (14 : ℝ) * I
  let T : ℕ → ℝ → ℂ := fun n a =>
    ∑ k ∈ Finset.range 128, ((((a : ℂ) - s) * (q n : ℂ)) ^ k / (k.factorial : ℂ))
  have hq (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) : 0 ≤ q n ∧ q n ≤ 5 / 2 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [q, qr]
  have hfac (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) : ‖(a : ℂ) - s‖ ≤ 15 := by
    have hsq : ‖(a : ℂ) - s‖ ^ 2 = (a - 1 / 2) ^ 2 + 196 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num [s]
      ring
    have ha2 : a ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg (show 0 ≤ a + 3 by linarith) (show 0 ≤ 3 - a by linarith)]
    nlinarith [norm_nonneg ((a : ℂ) - s)]
  have hp (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - s)‖ ≤ 4 := by
    obtain ⟨hn1, hn10⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    norm_num [s]
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ ≤ (10 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn10) (by norm_num)
      _ ≤ 4 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg (10 : ℝ)]
  have happ (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 10) (a : ℝ) (ha : -3 ≤ a) (ha1 : a ≤ 1) :
      ‖(n : ℂ) ^ ((a : ℂ) - s) - T n a‖ ≤ 1 / 1000 := by
    let z : ℂ := ((a : ℂ) - s) * (Real.log n : ℂ)
    let w : ℂ := ((a : ℂ) - s) * (q n : ℂ)
    have hez : Complex.exp z = (n : ℂ) ^ ((a : ℂ) - s) := by
      have hn0 : (n : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
      rw [Complex.cpow_def_of_ne_zero hn0]
      dsimp [z]
      rw [← Complex.natCast_log]
      congr 1
      ring
    have hz : ‖Complex.exp z‖ ≤ 4 := by rw [hez]; exact hp n hn a ha1
    have hzw : ‖w - z‖ ≤ 1 / 10000 := by
      have he : w - z = ((a : ℂ) - s) * ((q n - Real.log n : ℝ) : ℂ) := by
        dsimp [w, z]
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      calc
        _ ≤ 15 * (1 / 1000000) := mul_le_mul (hfac a ha ha1) (hlogs n hn) (abs_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    have hw : ‖w‖ ≤ 40 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq n hn).1]
      calc
        _ ≤ 15 * (5 / 2) := mul_le_mul (hfac a ha ha1) (hq n hn).2 (hq n hn).1 (by norm_num)
        _ ≤ _ := by norm_num
    have hnear : ‖Complex.exp z - Complex.exp w‖ ≤ 8 / 10000 := by
      have he : Complex.exp w - Complex.exp z = Complex.exp z * (Complex.exp (w - z) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 1
        ring
      rw [norm_sub_rev, he, norm_mul]
      have hh := Complex.norm_exp_sub_one_le (x := w - z) (by linarith : ‖w - z‖ ≤ 1)
      have hhd : ‖Complex.exp (w - z) - 1‖ ≤ 2 * (1 / 10000) :=
        hh.trans (mul_le_mul_of_nonneg_left hzw (by norm_num))
      calc
        ‖Complex.exp z‖ * ‖Complex.exp (w - z) - 1‖ ≤ 4 * (2 * (1 / 10000)) := by gcongr
        _ = 8 / 10000 := by norm_num
    have hTaylor : ‖Complex.exp w - T n a‖ ≤ 1 / 1000000 := by
      have hh := Complex.exp_bound' (x := w) (n := 128) (by norm_num; linarith)
      apply hh.trans
      calc
        _ ≤ (40 : ℝ) ^ 128 / (128 : ℕ).factorial * 2 := by gcongr
        _ ≤ _ := by norm_num
    rw [← hez]
    calc
      _ = ‖(Complex.exp z - Complex.exp w) + (Complex.exp w - T n a)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp z - Complex.exp w‖ + ‖Complex.exp w - T n a‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  let C : ℂ := (∑ n ∈ Finset.Ico (1 : ℕ) 10, T n 0) + T 10 1 / (s - 1) + T 10 0 / 2 +
    s * T 10 (-1) / 12 - s * (s + 1) * (s + 2) * T 10 (-3) / 720
  let S : QuadraticAlgebra ℚ (-1) 0 := ⟨1 / 2, 14⟩
  let Tq : ℕ → ℚ → QuadraticAlgebra ℚ (-1) 0 := fun n a =>
    ∑ k ∈ Finset.range 128, ((k.factorial : ℚ)⁻¹) •
      (((QuadraticAlgebra.C a) - S) * QuadraticAlgebra.C (qr n)) ^ k
  let Cq : QuadraticAlgebra ℚ (-1) 0 := (∑ n ∈ Finset.Ico (1 : ℕ) 10, Tq n 0) +
    Tq 10 1 * ⟨-2 / 785, -56 / 785⟩ + (1 / 2 : ℚ) • Tq 10 0 +
    (1 / 12 : ℚ) • (S * Tq 10 (-1)) -
    (1 / 720 : ℚ) • (S * (S + 1) * (S + 2) * Tq 10 (-3))
  let e : QuadraticAlgebra ℚ (-1) 0 →ₐ[ℚ] ℂ :=
    QuadraticAlgebra.lift ⟨Complex.I, by norm_num [smul_eq_mul]⟩
  have he_im (x : QuadraticAlgebra ℚ (-1) 0) : (e x).im = (x.im : ℝ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_S : e S = s := by
    norm_num [e, QuadraticAlgebra.lift, S, s, Algebra.smul_def]
  have he_C (a : ℚ) : e (QuadraticAlgebra.C a) = (a : ℂ) := by
    simp [e, QuadraticAlgebra.lift, Algebra.smul_def]
  have he_T (n : ℕ) (a : ℚ) : e (Tq n a) = T n (a : ℝ) := by
    simp only [Tq, T, map_sum, map_smul, map_pow, map_mul, map_sub, he_S, he_C]
    apply Finset.sum_congr rfl
    intro k hk
    simp [q, Algebra.smul_def, div_eq_mul_inv]
    ring
  have he_inv : e (⟨-2 / 785, -56 / 785⟩ : QuadraticAlgebra ℚ (-1) 0) =
      (s - 1)⁻¹ := by
    apply Complex.ext <;> norm_num [e, QuadraticAlgebra.lift, Algebra.smul_def, s,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  have hNum : Cq.im ≤ -(1 / 10 : ℚ) := by
    decide +kernel
  have he_Cq : e Cq = C := by
    dsimp only [Cq, C]
    simp only [map_sub, map_add, map_mul, map_sum, map_smul, he_T, he_S, he_inv, map_one, map_ofNat]
    norm_num [Algebra.smul_def, div_eq_mul_inv]
    ring
  have hCim : C.im ≤ -1 / 10 := by
    rw [← he_Cq, he_im]
    have hh : ((Cq.im : ℚ) : ℝ) ≤ ((-(1 / 10 : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hNum
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    simpa only [neg_div] using hh
  have hsplus (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 2) : ‖s + a‖ ≤ 20 := by
    have hh := hfac (-a) (by linarith) (by linarith)
    simp only [ofReal_neg] at hh
    rw [show -(a : ℂ) - s = -(s + a) by ring, norm_neg] at hh
    linarith
  have hs0 : ‖s‖ ≤ 20 := by simpa using hsplus 0 (by norm_num) (by norm_num)
  have hs1 : ‖s + 1‖ ≤ 20 := by simpa using hsplus 1 (by norm_num) (by norm_num)
  have hs2 : ‖s + 2‖ ≤ 20 := by simpa using hsplus 2 (by norm_num) (by norm_num)
  have hP : ‖s * (s + 1) * (s + 2)‖ ≤ 8000 := by
    simp only [norm_mul]
    calc
      ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ 20 * 20 * 20 := by gcongr
      _ = _ := by norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have hh := Complex.abs_re_le_norm (s - 1)
    norm_num [s] at hh
    exact hh
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num [one_div] at hh
    exact hh
  have h10a := happ 10 (by norm_num) 1 (by norm_num) (by norm_num)
  have h10b := happ 10 (by norm_num) 0 (by norm_num) (by norm_num)
  have h10c := happ 10 (by norm_num) (-1) (by norm_num) (by norm_num)
  have h10d := happ 10 (by norm_num) (-3) (by norm_num) (by norm_num)
  norm_num only [ofReal_one, ofReal_zero, ofReal_neg, zero_sub, ofReal_ofNat] at h10a h10b h10c h10d
  rw [show (-1 : ℂ) - s = -s - 1 by ring] at h10c
  rw [show (-3 : ℂ) - s = -s - 3 by ring] at h10d
  let A : ℂ := (∑ n ∈ Finset.Ico (1 : ℕ) 10, (n : ℂ) ^ (-s)) - ∑ n ∈ Finset.Ico (1 : ℕ) 10, T n 0
  have hnA : ‖A‖ ≤ 9 / 1000 := by
    dsimp [A]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, ‖(n : ℂ) ^ (-s) - T n 0‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico (1 : ℕ) 10, (1 / 1000 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : n ∈ Finset.Icc (1 : ℕ) 10 := by
          simp only [Finset.mem_Icc, Finset.mem_Ico] at *
          omega
        simpa only [ofReal_zero, zero_sub] using happ n hn' 0 (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hnB : ‖((10 : ℂ) ^ (1 - s) - T 10 1) / (s - 1)‖ ≤ 2 / 1000 := by
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖(10 : ℂ) ^ (1 - s) - T 10 1‖ * ‖(s - 1)⁻¹‖ ≤ (1 / 1000) * 2 := by gcongr
      _ = _ := by norm_num
  have hnC : ‖((10 : ℂ) ^ (-s) - T 10 0) / 2‖ ≤ 1 / 2000 := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    linarith
  have hnD : ‖s * ((10 : ℂ) ^ (-s - 1) - T 10 (-1)) / 12‖ ≤ 2 / 1000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s‖ * ‖(10 : ℂ) ^ (-s - 1) - T 10 (-1)‖ / 12 ≤ 20 * (1 / 1000) / 12 := by gcongr
      _ ≤ _ := by norm_num
  have hnE : ‖s * (s + 1) * (s + 2) * ((10 : ℂ) ^ (-s - 3) - T 10 (-3)) / 720‖ ≤ 12 / 1000 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s * (s + 1) * (s + 2)‖ * ‖(10 : ℂ) ^ (-s - 3) - T 10 (-3)‖ / 720 ≤ 8000 * (1 / 1000) / 720 := by gcongr
      _ ≤ _ := by norm_num
  have hErr : ‖EM10 s - C‖ ≤ 3 / 100 := by
    have he : EM10 s - C = A + ((10 : ℂ) ^ (1 - s) - T 10 1) / (s - 1) +
        ((10 : ℂ) ^ (-s) - T 10 0) / 2 + s * ((10 : ℂ) ^ (-s - 1) - T 10 (-1)) / 12 -
        s * (s + 1) * (s + 2) * ((10 : ℂ) ^ (-s - 3) - T 10 (-3)) / 720 := by
      dsimp [EM10, C, A]
      ring
    rw [he]
    calc
      _ ≤ ‖A‖ + ‖((10 : ℂ) ^ (1 - s) - T 10 1) / (s - 1)‖ + ‖((10 : ℂ) ^ (-s) - T 10 0) / 2‖ +
          ‖s * ((10 : ℂ) ^ (-s - 1) - T 10 (-1)) / 12‖ +
          ‖s * (s + 1) * (s + 2) * ((10 : ℂ) ^ (-s - 3) - T 10 (-3)) / 720‖ := by
        grw [norm_sub_le, norm_add_le, norm_add_le, norm_add_le]
      _ ≤ 9 / 1000 + 2 / 1000 + 1 / 2000 + 2 / 1000 + 12 / 1000 := by gcongr
      _ ≤ _ := by norm_num
  have hdiff := (Complex.abs_im_le_norm (EM10 s - C)).trans hErr
  have hdiffup := (le_abs_self ((EM10 s - C).im)).trans hdiff
  simp only [Complex.sub_im] at hdiffup
  have hnorm := (neg_le_abs (EM10 s).im).trans (Complex.abs_im_le_norm (EM10 s))
  linarith

end LeanLab.Routes.Decomp1551c
