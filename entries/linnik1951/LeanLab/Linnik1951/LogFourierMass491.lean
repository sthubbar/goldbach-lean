module

public import LeanLab.Linnik1951.Base491b

/-!
P0093 pages 159 and 161. The square mass of the model series S one, the analogue
for S one of the trivial estimate of page 159 before equation 5.3.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- Parseval over a full period for an absolutely summable series in the
negative natural frequencies. -/
private theorem series_square_mass491 (a : ℕ → ℂ) (ha : Summable a) :
    (∫ α in (0 : ℝ)..1, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) =
        ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hf : Continuous (fun α : ℝ => ∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) := by
    apply continuous_tsum (u := fun n => ‖a n‖)
    · intro n
      fun_prop
    · exact ha.norm
    · intro n α
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have hs : IntervalIntegrable (fun α : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) volume 0 1 :=
    (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => ∑' n : ℕ, a n *
          Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) i‖ ^ 2 := by
      simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm
    _ = _ := negative_modes_sum111_up111 _ _ (negative_series_coefficient_proved357_up111 a ha)

private theorem logFourier_continuous_mass491 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m => ‖logCoefficient520 N m‖) ?_
    (logCoefficient_summable520 N hN).norm ?_
  · intro m
    fun_prop
  · intro m z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem logFourier_periodic_mass491 (N : ℕ) :
    Function.Periodic (logFourier520 N) 1 := by
  intro z
  unfold logFourier520
  apply tsum_congr
  intro m
  congr 1
  have h : ((-(2 * Real.pi * (z + 1) * m) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * z * m) : ℝ) : ℂ) * Complex.I +
        ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Weights three at frequency two and one from three on have prefix sums
at most the length. -/
private theorem weight_prefix_mass491 (n : ℕ) :
    ∑ i ∈ range n, (if i = 2 then (3 : ℝ) else if 3 ≤ i then 1 else 0) ≤ 1 * (n : ℝ) := by
  have h : ∑ i ∈ range n, (if i = 2 then (3 : ℝ) else if 3 ≤ i then 1 else 0) =
      if n ≤ 2 then 0 else (n : ℝ) := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h2 : k = 2
      · subst h2; norm_num
      · by_cases h3 : 3 ≤ k
        · rw [if_neg (by omega), if_neg h2, if_pos h3, if_neg (by omega)]
          push_cast; ring
        · rw [if_pos (by omega), if_neg h2, if_neg h3, if_pos (by omega)]
          ring
  rw [h]
  split_ifs <;> simp

private theorem coefficient_sq_mass491 (N m : ℕ) :
    ‖logCoefficient520 N m‖ ^ 2 ≤
      (if m = 2 then (3 : ℝ) else if 3 ≤ m then 1 else 0) *
        Real.exp (-2 * (m : ℝ) / N) := by
  have heq : Real.exp (-(m : ℝ) / N) ^ 2 = Real.exp (-2 * (m : ℝ) / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold logCoefficient520
  by_cases hm : 2 ≤ m
  · rw [if_pos hm, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, heq]
    have hE := Real.exp_pos (-2 * (m : ℝ) / N)
    by_cases h2 : m = 2
    · subst h2
      rw [if_pos rfl]
      have hl := Real.log_two_gt_d9
      have hl2 : (1 : ℝ) ≤ 3 * Real.log 2 ^ 2 := by nlinarith
      push_cast
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · have h3 : 3 ≤ m := by omega
      rw [if_neg h2, if_pos h3, one_mul]
      have hl : (1 : ℝ) ≤ Real.log m := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have h3r : (3 : ℝ) ≤ m := by exact_mod_cast h3
        have := Real.exp_one_lt_d9
        linarith
      rw [div_le_iff₀ (by positivity)]
      have hl2 : (1 : ℝ) ≤ Real.log m ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 hE.le]
  · rw [if_neg hm, if_neg (by omega), if_neg (by omega)]
    simp

private theorem logFourier_full_mass491 (N : ℕ) (hN : 1 ≤ N) :
    (∫ z in (0 : ℝ)..1, ‖logFourier520 N z‖ ^ 2) ≤ 2 * (N : ℝ) := by
  unfold logFourier520
  rw [series_square_mass491 _ (logCoefficient_summable520 N hN)]
  have hh := laplace_bound111_up111
    (fun i : ℕ => if i = 2 then (3 : ℝ) else if 3 ≤ i then 1 else 0) 1 N hN (by norm_num)
    (fun i => by split_ifs <;> norm_num) weight_prefix_mass491
  have hg : Summable (fun n : ℕ => Real.exp (-2 * (n : ℝ) / N)) := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hr : ‖Real.exp (-2 / (N : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hNp)
    have hs := summable_geometric_of_norm_lt_one hr
    convert hs using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hw : Summable (fun n : ℕ =>
      (if n = 2 then (3 : ℝ) else if 3 ≤ n then 1 else 0) * Real.exp (-2 * (n : ℝ) / N)) := by
    apply Summable.of_nonneg_of_le _ _ (hg.mul_left 3)
    · intro n
      have := Real.exp_pos (-2 * (n : ℝ) / N)
      split_ifs <;> positivity
    · intro n
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      split_ifs <;> norm_num
  calc
    _ ≤ ∑' n : ℕ, (if n = 2 then (3 : ℝ) else if 3 ≤ n then 1 else 0) *
        Real.exp (-2 * (n : ℝ) / N) :=
      (Summable.of_nonneg_of_le (fun n => sq_nonneg _) (coefficient_sq_mass491 N) hw).tsum_le_tsum
        (coefficient_sq_mass491 N) hw
    _ ≤ _ := by simpa using hh

/-- P0093 page 159, the trivial estimate before equation 5.3, for the
model series S one of equation 6.3. Its square integral over any interval of
radius at most one half is at most the full period square sum, at most 2 N. -/
theorem logFourier_mass491 (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 ≤ r)
    (hrh : r ≤ 1 / 2) : (∫ z in -r..r, ‖logFourier520 N z‖ ^ 2) ≤ 2 * (N : ℝ) := by
  have hc := (logFourier_continuous_mass491 N hN).norm.pow 2
  have hp : Function.Periodic (fun α => ‖logFourier520 N α‖ ^ 2) 1 :=
    (logFourier_periodic_mass491 N).comp (fun z => ‖z‖ ^ 2)
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hrh
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖logFourier520 N α‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
  have he := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num only at he
  exact hi.trans (he.trans_le (logFourier_full_mass491 N hN))

end LeanLab.Linnik1951
