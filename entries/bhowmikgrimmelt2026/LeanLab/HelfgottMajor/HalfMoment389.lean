module

public import Mathlib

/-!
The scalar half moment of P0014 page 43, display 4.42.
The finite Taylor majorant and the tail majorant give a rational certificate.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.HalfMoment389
open Real MeasureTheory Set Filter
open scoped Topology

/-- Taylor's even polynomial bounds the exponential on the negative half line.
This is an elementary prerequisite for the numerical inequality in display 4.42 on page 43.
-/
theorem exp_neg_le_even_sum (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    exp (-x) ≤ ∑ k ∈ Finset.range (2 * n + 1), (-x) ^ k / (k.factorial : ℝ) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [Finset.sum_range_succ']
  have hne : (0 : ℝ) ≠ -x := by linarith
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := exp) (n := 2 * n) hne (contDiff_exp.contDiffOn)
  have hid (k : ℕ) : iteratedDeriv k exp = exp := by
    rw [iteratedDeriv_eq_iterate, iter_deriv_exp]
  have ht : taylorWithinEval exp (2 * n) (uIcc 0 (-x)) 0 (-x) =
      ∑ k ∈ Finset.range (2 * n + 1), (-x) ^ k / (k.factorial : ℝ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      contDiff_exp.contDiffAt (left_mem_uIcc), hid]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [ht, hid] at he
  simp only [sub_zero] at he
  have hp : (-x) ^ (2 * n + 1) ≤ 0 := by
    rw [pow_add, pow_mul]
    have : 0 ≤ ((-x) ^ 2) ^ n := pow_nonneg (sq_nonneg _) _
    nlinarith
  have hr : exp y * (-x) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le hp)
      (Nat.cast_nonneg _)
  linarith

/-- Integrate the even Taylor majorant on the finite part of the quartic substitution.
Source display 4.42 on page 43, with t equal to u squared and u at most 2.
-/
theorem quartic_core_bound (n : ℕ) :
    (∫ u in (0 : ℝ)..2, exp (-u ^ 4 / 2)) ≤
      2 * ∑ k ∈ Finset.range (2 * n + 1),
        (-8 : ℝ) ^ k / ((k.factorial : ℝ) * (4 * k + 1)) := by
  let p : ℝ → ℝ := fun u => ∑ k ∈ Finset.range (2 * n + 1),
    ((-1 / 2 : ℝ) ^ k / (k.factorial : ℝ)) * u ^ (4 * k)
  have hp : Continuous p := by unfold p; fun_prop
  have hmaj : ∀ u : ℝ, exp (-u ^ 4 / 2) ≤ p u := by
    intro u
    have h := exp_neg_le_even_sum (u ^ 4 / 2) (by positivity) n
    rw [neg_div]
    refine h.trans_eq ?_
    symm
    apply Finset.sum_congr rfl
    intro k hk
    rw [show -(u ^ 4 / 2) = (-1 / 2 : ℝ) * u ^ 4 by ring, mul_pow, ← pow_mul]
    ring
  calc
    _ ≤ ∫ u in (0 : ℝ)..2, p u :=
      intervalIntegral.integral_mono_on (by norm_num)
        ((by fun_prop : Continuous (fun u : ℝ => exp (-u ^ 4 / 2))).intervalIntegrable _ _)
        (hp.intervalIntegrable _ _) (fun u _ => hmaj u)
    _ = _ := by
      unfold p
      rw [intervalIntegral.integral_finsetSum]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
        have hpow : (2 : ℝ) ^ (4 * k + 1) = 2 * 16 ^ k := by
          rw [pow_add, pow_mul]
          norm_num
          ring
        rw [hpow]
        have hneg : (-1 / 2 : ℝ) ^ k * 16 ^ k = (-8 : ℝ) ^ k := by
          rw [← mul_pow]; norm_num
        push_cast
        rw [div_mul_div_comm]
        rw [show (-1 / 2 : ℝ) ^ k * (2 * 16 ^ k) = 2 * (-8 : ℝ) ^ k by
          calc
            _ = 2 * ((-1 / 2 : ℝ) ^ k * 16 ^ k) := by ring
            _ = _ := by rw [hneg]]
        ring
      · intro k hk
        exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _

/-- A first derivative tail majorant after the quartic substitution in display 4.42.
On u at least 2, u cubed divided by 8 is at least 1.
-/
theorem quartic_tail_bound :
    (∫ u in Ioi (2 : ℝ), exp (-u ^ 4 / 2)) ≤ exp (-8) / 16 := by
  let g : ℝ → ℝ := fun u => -(exp (-u ^ 4 / 2) / 16)
  let g' : ℝ → ℝ := fun u => u ^ 3 / 8 * exp (-u ^ 4 / 2)
  have hd (u : ℝ) : HasDerivAt g (g' u) u := by
    have hh := (((hasDerivAt_id u).pow 4).neg.div_const 2).exp.div_const 16
    convert hh.neg using 1
    · ext t; rfl
    · dsimp [g']; norm_num; ring
  have hc : ContinuousWithinAt g (Ici 2) 2 := by unfold g; fun_prop
  have hl : Tendsto g atTop (nhds 0) := by
    have hh : Tendsto (fun u : ℝ => u ^ 4 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
    have he := (tendsto_exp_neg_atTop_nhds_zero.comp hh).div_const 16 |>.neg
    simpa [g, neg_div] using he
  have hpos : ∀ u ∈ Ioi (2 : ℝ), 0 ≤ g' u := by
    intro u hu
    change 2 < u at hu
    exact mul_nonneg (div_nonneg (pow_nonneg (by linarith [hu] : 0 ≤ u) _) (by norm_num))
      (exp_pos _).le
  have hg : IntegrableOn g' (Ioi 2) :=
    integrableOn_Ioi_deriv_of_nonneg hc (fun u _ => hd u) hpos hl
  have hbound : ∀ u ∈ Ioi (2 : ℝ), exp (-u ^ 4 / 2) ≤ g' u := by
    intro u hu
    change 2 < u at hu
    have hcube : (8 : ℝ) ≤ u ^ 3 := by
      calc
        (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ u ^ 3 := by gcongr
    dsimp [g']
    have he := exp_pos (-u ^ 4 / 2)
    nlinarith
  have hf : IntegrableOn (fun u : ℝ => exp (-u ^ 4 / 2)) (Ioi 2) := by
    apply hg.mono' (by fun_prop : Continuous (fun u : ℝ => exp (-u ^ 4 / 2))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _)] using hbound u hu
  calc
    _ ≤ ∫ u in Ioi (2 : ℝ), g' u := integral_mono_ae hf hg <|
      (ae_restrict_mem measurableSet_Ioi).mono (fun u hu => hbound u hu)
    _ = _ := by
      rw [integral_Ioi_of_hasDerivAt_of_nonneg hc (fun u _ => hd u) hpos hl]
      norm_num [g]

/-- The rational certificate for the finite part and tail of display 4.42 on page 43. -/
theorem quartic_integral_bound :
    (∫ u in Ioi (0 : ℝ), exp (-u ^ 4 / 2)) ≤ 1.077902 := by
  have hi : IntegrableOn (fun u : ℝ => exp (-u ^ 4 / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (0 : ℝ)) (p := (4 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    norm_num only [rpow_zero, one_mul, rpow_ofNat]
    congr 1
    ring
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)))
  have hc := quartic_core_bound 16
  have hcert : (2 : ℝ) * ∑ k ∈ Finset.range 33,
      (-8 : ℝ) ^ k / ((k.factorial : ℝ) * (4 * k + 1)) ≤ 1.077881 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he : exp (-8) ≤ (0.000336 : ℝ) := by
    have heq : exp (-8) = exp (-1) ^ 8 := by
      rw [← exp_nat_mul]
      norm_num
    rw [heq]
    calc
      _ ≤ (0.3678794412 : ℝ) ^ 8 := by gcongr; exact exp_neg_one_lt_d9.le
      _ ≤ _ := by norm_num
  have ht := quartic_tail_bound
  norm_num only [show 2 * (16 : ℕ) + 1 = 33 by norm_num] at hc
  linarith

/-- The scalar Gaussian half moment bound in display 4.42 on page 43.
The proof uses a finite Taylor integral and an exponential tail, with no cited numerical input.
-/
theorem gaussian_half_moment_bound :
    (∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2)) ≤
      2.15581 := by
  have hs := integral_comp_rpow_Ioi_of_pos
    (g := fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2))
    (p := (2 : ℝ)) (by norm_num)
  have he : (∫ u in Ioi (0 : ℝ),
      (2 * u ^ ((2 : ℝ) - 1)) •
        ((u ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) - 1) * exp (-(u ^ (2 : ℝ)) ^ 2 / 2))) =
      2 * ∫ u in Ioi (0 : ℝ), exp (-u ^ 4 / 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change 0 < u at hu
    dsimp only
    have hp : u * (u ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) - 1) = 1 := by
      rw [← rpow_mul hu.le]
      norm_num
      simpa only [rpow_neg_one] using mul_inv_cancel₀ hu.ne'
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, smul_eq_mul]
    rw [show 2 * u * ((u ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) - 1) *
      exp (-(u ^ (2 : ℝ)) ^ 2 / 2)) =
      2 * (u * (u ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) - 1)) *
        exp (-(u ^ (2 : ℝ)) ^ 2 / 2) by ring, hp]
    norm_num only [rpow_two, mul_one]
    congr 2
    ring
  rw [he] at hs
  have h := quartic_integral_bound
  linarith

end LeanLab.HelfgottMajor.HalfMoment389
