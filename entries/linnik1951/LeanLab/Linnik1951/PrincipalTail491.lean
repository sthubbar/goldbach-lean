module

public import LeanLab.Linnik1951.LogFourierDecay491

/-!
P0093 pages 160 and 161, equations 6.2 and 6.3. Extension of the arc integral
of the squared model series S one to a full period. Steps: continuity and
periodicity of S one, the exact full period value as the damped logarithmic
convolution, the tail bound from the decay of S one, and the scale comparison.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

private theorem logFourier_continuous_tail491 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m => ‖logCoefficient520 N m‖) ?_
    (logCoefficient_summable520 N hN).norm ?_
  · intro m
    fun_prop
  · intro m z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem logFourier_periodic_tail491 (N : ℕ) :
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

private theorem phase_periodic_tail491 (n : ℤ) :
    Function.Periodic (fun z : ℝ =>
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := by
  intro z
  dsimp only
  have h : ((2 * Real.pi * (n : ℝ) * (z + 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I +
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem full_period_tail491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) := by
  have hper : Function.Periodic (fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := by
    intro z
    have h1 := logFourier_periodic_tail491 N z
    have h2 := phase_periodic_tail491 n z
    dsimp only at h2 ⊢
    rw [h1, h2]
  have hshift := hper.intervalIntegral_add_eq (-(1 / 2) : ℝ) 0
  have e1 : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e1, zero_add] at hshift
  rw [hshift]
  have hmain := logFourier_square_integral520 N hN n
  have hcongr : (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro z _
    dsimp only
    rw [show 2 * Real.pi * (n : ℝ) * z = 2 * Real.pi * z * (n : ℝ) by ring]
  rw [hcongr, hmain]
  have hconv : logConvolution520 n.toNat = logConvolution1622 n.toNat := rfl
  rw [hconv]
  by_cases hn : 0 ≤ n
  · have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [hc]
  · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [hz, logConvolution1622]

/-- The integral of the squared model series against a unimodular phase over
an interval of one sign inside the half period is at most the reciprocal of the
distance of the interval to the origin. -/
private theorem piece_bound_tail491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hside : (d ≤ a ∧ b ≤ 1 / 2) ∨ (-(1 / 2) ≤ a ∧ b ≤ -d))
    (hval : (b ^ ((-2 : ℤ) + 1) - a ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1) ≤ 1 / d) :
    ‖∫ z in a..b, logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / d := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    rcases hside with h1 | h1 <;> linarith [h.1, h.2]
  have hint := integral_zpow (a := a) (b := b) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, h0⟩)
  have hii : IntervalIntegrable (fun z : ℝ => z ^ (-2 : ℤ)) volume a b :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr h0)
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := a) (b := b)
    (f := fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))
    (g := fun z : ℝ => z ^ (-2 : ℤ)) hab ?_ hii
  · calc _ ≤ ∫ z in a..b, z ^ (-2 : ℤ) := hle
      _ = _ := hint
      _ ≤ 1 / d := by exact_mod_cast hval
  · refine Filter.Eventually.of_forall ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rcases hside with h1 | h1
      · have := hz.1; linarith
      · have := hz.2; intro h; linarith
    have hzh : |z| ≤ 1 / 2 := by
      rw [abs_le]
      rcases hside with h1 | h1 <;> constructor <;> linarith [hz.1, hz.2]
    have hdec := logFourier_decay491 N hN z hz0 hzh
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_pow]
    have hpos : 0 < |z| := abs_pos.mpr hz0
    calc ‖logFourier520 N z‖ ^ 2 ≤ (1 / |z|) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hdec 2
      _ = z ^ (-2 : ℤ) := by
          rw [zpow_neg, div_pow, one_pow, sq_abs, one_div]
          norm_cast

private theorem tail_bound_tail491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (d : ℝ)
    (hd : 0 < d) (hdh : d ≤ 1 / 2) :
    ‖(∫ z in -d..d, logFourier520 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤ 2 / d := by
  rw [← full_period_tail491 N hN n]
  have hcont : Continuous (fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    have := logFourier_continuous_tail491 N hN
    fun_prop
  have hi (a b : ℝ) : IntervalIntegrable (fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) volume a b :=
    hcont.intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1 / 2)) (-d)) (hi (-d) d)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1 / 2)) d) (hi d (1 / 2))
  have hp1 := piece_bound_tail491 N hN n (-(1 / 2)) (-d) d hd (by linarith)
    (Or.inr ⟨le_refl _, le_refl _⟩) (by
      have hdn : d ≠ 0 := hd.ne'
      have e : ((-2 : ℤ) + 1) = (-1 : ℤ) := by norm_num
      rw [e, zpow_neg_one, zpow_neg_one]
      have : ((-d)⁻¹ - (-(1 / 2 : ℝ))⁻¹) / (((-2 : ℤ) : ℝ) + 1) = 1 / d - 2 := by
        push_cast
        field_simp
        ring
      rw [this]
      linarith)
  have hp2 := piece_bound_tail491 N hN n d (1 / 2) d hd hdh
    (Or.inl ⟨le_refl _, le_refl _⟩) (by
      have hdn : d ≠ 0 := hd.ne'
      have e : ((-2 : ℤ) + 1) = (-1 : ℤ) := by norm_num
      rw [e, zpow_neg_one, zpow_neg_one]
      have : ((1 / 2 : ℝ)⁻¹ - d⁻¹) / (((-2 : ℤ) : ℝ) + 1) = 1 / d - 2 := by
        push_cast
        field_simp
        ring
      rw [this]
      linarith)
  rw [← h2, ← h1]
  have : ∀ A B D : ℂ, B - (A + B + D) = -(A + D) := by intros; ring
  rw [this, norm_neg]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 1 / d + 1 / d := add_le_add hp1 hp2
    _ = 2 / d := by ring

/-- P0093 pages 160 and 161 equations 6.2 and 6.3. The arc integral of the squared model series S one, extended to a full period, is the exactly damped logarithmic convolution, with the reciprocal length error term. The print extends the contour integral, with the bound q tau squared, and then passes to S one; here S one itself is extended, with the bound 2 q tau. -/
theorem logFourier_arc_convolution491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  refine ⟨2, by norm_num, 128, ?_⟩
  intro N hN q hq hqN n
  have hNR : (128 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  have hτ2 : (2 : ℝ) ≤ τ := by
    have h128 : ((128 : ℝ)) ^ (1 / 7 : ℝ) = 2 := by
      have : (128 : ℝ) = (2 : ℝ) ^ (7 : ℝ) := by norm_num
      rw [this, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h128]
    exact Real.rpow_le_rpow (by norm_num) hNR (by norm_num)
  have hD : (2 : ℝ) ≤ (q : ℝ) * τ := by nlinarith
  have hDpos : (0 : ℝ) < (q : ℝ) * τ := by linarith
  have hd : (0 : ℝ) < 1 / ((q : ℝ) * τ) := by positivity
  have hdh : 1 / ((q : ℝ) * τ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hD
  have ht := tail_bound_tail491 N (by omega) n (1 / ((q : ℝ) * τ)) hd hdh
  refine ht.trans ?_
  have hsq : ((q : ℝ) * τ) ^ 2 ≤ (N : ℝ) := by
    have h1 : ((q : ℝ) * τ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hqN (by positivity)
    rw [← Real.rpow_add (by linarith)] at h1
    calc ((q : ℝ) * τ) ^ 2 ≤ ((N : ℝ) ^ ((1 / 10 : ℝ) + 1 / 7)) ^ 2 :=
          pow_le_pow_left₀ hDpos.le h1 2
      _ = (N : ℝ) ^ (((1 / 10 : ℝ) + 1 / 7) * 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
          norm_num
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hlog : (1 : ℝ) ≤ Real.log N := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) h3
  have hlog13 : (1 : ℝ) ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  rw [div_le_div_iff₀ hd hDpos]
  have e : (2 : ℝ) * ((q : ℝ) * τ) = 2 * ((q : ℝ) * τ) ^ 2 * (1 / ((q : ℝ) * τ)) := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_right _ hd.le
  nlinarith [mul_le_mul hsq hlog13 zero_le_one hN0]
