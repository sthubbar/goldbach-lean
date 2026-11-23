module

public import LeanLab.Linnik1951.Data491
public import LeanLab.Linnik1951.Decomp357g
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
P0093 pages 156 and 161. Exact residue and full period Fourier steps.
The core interval is kept distinct from the full period interval.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- P0093 page 156 equation 3.4. Split the residual phase at a rational centre.
This is an exact identity and does not approximate the prime series. -/
theorem rational_phase521 (q a : ℕ) (n : ℤ) (z : ℝ) :
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0093 page 156 equation 3.4 and page 161 equation 6.4.
A residue independent model square factors into its arithmetic coefficient,
the Ramanujan sum and its remaining integral. Both endpoints remain arbitrary. -/
theorem rational_model_sum521 (q : ℕ) (n : ℤ) (hn : 0 ≤ n)
    (c : ℂ) (F : ℝ → ℂ) (l r : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z in l..r, (c * F z) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      c ^ 2 * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat *
        (∫ z in l..r, F z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  have hterm (a : ℕ) :
      (∫ z in l..r, (c * F z) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      (c ^ 2 * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        (∫ z in l..r, F z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [rational_phase521]
    ring
  simp_rw [hterm]
  rw [← sum_mul, ← mul_sum]
  congr 2
  unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum LeanLab.Perelli1996.Kernel.e
  apply sum_congr rfl
  intro a ha
  rw [hc]
  congr 1
  push_cast
  ring

/-- P0093 page 156 equation 3.4 and page 161 equations 6.2 and 6.3.
Auxiliary exact error decomposition. The first error compares a shifted
square with the rational model. The second keeps the model integral
minus its proposed coefficient D. No bound on either error is assumed. -/
theorem rational_model_error521 (q : ℕ) (n : ℤ) (hn : 0 ≤ n)
    (c : ℂ) (P F : ℝ → ℂ) (l r : ℝ) (D : ℂ) :
    ‖(∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in l..r, P ((a : ℝ) / q + z) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
      c ^ 2 * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * D‖ ≤
      ‖(∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ z in l..r, P ((a : ℝ) / q + z) ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ z in l..r, (c * F z) ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ +
      ‖c ^ 2 * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat‖ *
        ‖(∫ z in l..r, F z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - D‖ := by
  let A : ℂ := ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in l..r, P ((a : ℝ) / q + z) ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)
  let B : ℂ := ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in l..r, (c * F z) ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)
  let K : ℂ := c ^ 2 * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat
  let I : ℂ := ∫ z in l..r, F z ^ 2 *
    Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)
  change ‖A - K * D‖ ≤ ‖A - B‖ + ‖K‖ * ‖I - D‖
  have hB : B = K * I := rational_model_sum521 q n hn c F l r
  calc
    ‖A - K * D‖ ≤ ‖A - B‖ + ‖B - K * D‖ := by
      simpa only [dist_eq_norm] using dist_triangle A B (K * D)
    _ = _ := by rw [hB, ← mul_sub, norm_mul]

/-- P0093 page 161 equation 6.3. The square of an absolutely summable
negative Fourier series has the Cauchy product coefficients. -/
theorem square_series521 (a : ℕ → ℂ) (ha : Summable a) (z : ℝ) :
    (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 =
      ∑' n : ℕ, (∑ m ∈ range (n + 1), a m * a (n - m)) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) := by
  have hs : Summable (fun m : ℕ => ‖a m *
      Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)‖) := by
    simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using ha.norm
  rw [pow_two, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hs]
  apply tsum_congr
  intro n
  rw [sum_mul]
  apply sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by have := mem_range.mp hm; omega
  have hp : Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) *
      Complex.exp ((-(2 * Real.pi * z * (n - m : ℕ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast [Nat.cast_sub hmn]
    ring
  calc
    _ = (a m * a (n - m)) *
        (Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) *
          Complex.exp ((-(2 * Real.pi * z * (n - m : ℕ)) : ℝ) * Complex.I)) := by ring
    _ = _ := by rw [hp]

/-- P0093 page 161 equation 6.3. Full period extraction of the coefficient
of a squared absolutely summable negative Fourier series. -/
theorem square_series_integral521 (a : ℕ → ℂ) (ha : Summable a) (n : ℕ) :
    (∫ z in (0 : ℝ)..1,
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∑ m ∈ range (n + 1), a m * a (n - m) := by
  have hs : Summable (fun n => ∑ m ∈ range (n + 1), a m * a (n - m)) :=
    (summable_norm_sum_mul_range_of_summable_norm ha.norm ha.norm).of_norm
  have hc := negative_series_coefficient_proved357 _ hs (-(n : ℤ))
  calc
    _ = fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun z => (∑' m : ℕ, a m *
          Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2) (-(n : ℤ)) := by
      rw [coefficient_integral357]
      apply intervalIntegral.integral_congr
      intro z hz
      dsimp only
      unfold LeanLab.Perelli1996.Kernel.e
      rw [mul_comm]
      congr 1
      congr 1
      push_cast
      ring
    _ = _ := by
      simp_rw [square_series521 a ha]
      simpa using hc

/-- P0093 page 161 definition of S one after equation 6.3.
Its real coefficients vanish below two and otherwise carry reciprocal logarithms. -/
noncomputable def logCoefficient521 (N m : ℕ) : ℝ :=
  if 2 ≤ m then Real.exp (-(m : ℝ) / N) / Real.log m else 0

/-- P0093 page 161 equation 6.3. The logarithmic model has absolutely
summable coefficients at each positive damping scale. -/
theorem log_coefficients_summable521 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => (logCoefficient521 N m : ℂ)) := by
  apply Summable.of_norm_bounded ((damping_summable111 N hN).mul_left (1 / Real.log 2))
  intro m
  by_cases hm : 2 ≤ m
  · have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlog2 : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm)
    simp only [logCoefficient521, if_pos hm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.exp_pos _) hlog)]
    calc
      _ ≤ Real.exp (-(m : ℝ) / N) / Real.log 2 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.log_pos (by norm_num)) hlog2
      _ = _ := by ring
  · simp only [logCoefficient521, if_neg hm, Complex.norm_real, Real.norm_eq_abs, abs_zero]
    positivity

/-- P0093 page 161 after equation 6.3. Multiplying the logarithmic
coefficients gives the exact convolution with damping at the residual. -/
theorem log_coefficient_convolution521 (N n : ℕ) :
    (∑ m ∈ range (n + 1),
      (logCoefficient521 N m : ℂ) * (logCoefficient521 N (n - m) : ℂ)) =
      ((Real.exp (-(n : ℝ) / N) * logConvolution1622 n : ℝ) : ℂ) := by
  have heq : (∑ m ∈ range (n + 1), logCoefficient521 N m * logCoefficient521 N (n - m)) =
      Real.exp (-(n : ℝ) / N) * logConvolution1622 n := by
    have hrestrict : (∑ m ∈ range (n + 1), logCoefficient521 N m * logCoefficient521 N (n - m)) =
        ∑ m ∈ Icc 2 (n - 2), logCoefficient521 N m * logCoefficient521 N (n - m) := by
      symm
      apply sum_subset
      · intro m hm
        have := mem_Icc.mp hm
        exact mem_range.mpr (by omega)
      · intro m hm hnot
        have hmle := mem_range.mp hm
        have hnot' := mt mem_Icc.mpr hnot
        by_cases h2 : 2 ≤ m
        · have hnm : ¬ 2 ≤ n - m := by omega
          simp [logCoefficient521, hnm]
        · simp [logCoefficient521, h2]
    rw [hrestrict]
    unfold logConvolution1622
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    obtain ⟨hm2, hmn⟩ := mem_Icc.mp hm
    have hnm2 : 2 ≤ n - m := by omega
    have hmn' : m ≤ n := by omega
    simp only [logCoefficient521, if_pos hm2, if_pos hnm2]
    have hd : -(m : ℝ) / N + -((n - m : ℕ) : ℝ) / N = -(n : ℝ) / N := by
      rw [Nat.cast_sub hmn']
      ring
    rw [div_mul_div_comm, ← Real.exp_add, hd]
    ring
  exact_mod_cast heq

/-- P0093 page 161 equations 6.2 and 6.3. Extraction on any full period
has the same coefficient. The starting point is arbitrary. -/
theorem square_series_integral_shift521 (a : ℕ → ℂ) (ha : Summable a) (n : ℕ) (b : ℝ) :
    (∫ z in b..b + 1,
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∑ m ∈ range (n + 1), a m * a (n - m) := by
  have hp (j : ℤ) (z : ℝ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * (z + 1) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (j : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
    have he : (((2 * Real.pi * (j : ℝ) * (z + 1) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * (j : ℝ) * z : ℝ) : ℂ) * Complex.I) +
          (j : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hf : Function.Periodic (fun z : ℝ =>
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := by
    intro z
    dsimp only
    have hs : (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * (z + 1) * m) : ℝ) * Complex.I)) =
        ∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) := by
      apply tsum_congr
      intro m
      congr 1
      convert hp (-(m : ℤ)) z using 1 <;> push_cast <;> congr 1 <;> ring
    rw [hs]
    congr 1
    simpa only [Int.cast_natCast] using hp (n : ℤ) z
  calc
    _ = ∫ z in (0 : ℝ)..1,
        (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
      simpa using hf.intervalIntegral_add_eq b 0
    _ = _ := square_series_integral521 a ha n

/-- P0093 page 161 definition of S one after equation 6.3.
The damped reciprocal logarithm series is indexed by all natural numbers
with its first two coefficients set to zero. -/
noncomputable def logarithmicModel521 (N : ℕ) (z : ℝ) : ℂ :=
  ∑' m : ℕ, (logCoefficient521 N m : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)

/-- P0093 page 161 equation 6.3 and its following display.
The full period model square gives the exact damped convolution.
This theorem states no estimate for a truncated core interval. -/
theorem logarithmic_model_full_period521 (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ), logarithmicModel521 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
        ((Real.exp (-(n : ℝ) / N) * logConvolution1622 n : ℝ) : ℂ) := by
  have hi := square_series_integral_shift521 (fun m => (logCoefficient521 N m : ℂ))
    (log_coefficients_summable521 N hN) n (-1 / 2)
  norm_num only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at hi
  simpa only [logarithmicModel521, neg_div] using
    hi.trans (log_coefficient_convolution521 N n)

/-- P0093 page 161 equation 6.4 before the convolution asymptotic.
The full period logarithmic model with the principal rational coefficient
has exactly the singular coefficient times the Ramanujan sum times the
damped convolution. No approximation of the prime square is asserted. -/
theorem logarithmic_model_residue521 (N : ℕ) (hN : 1 ≤ N) (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ((((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) *
          logarithmicModel521 N z) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n *
        ((Real.exp (-(n : ℝ) / N) * logConvolution1622 n : ℝ) : ℂ)) := by
  have h := rational_model_sum521 q (n : ℤ) (by omega)
    ((((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ))
    (logarithmicModel521 N) (-1 / 2) (1 / 2)
  simp only [Int.cast_natCast, Int.toNat_natCast] at h
  rw [logarithmic_model_full_period521 N hN n] at h
  have hcoeff : ((((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ)) ^ 2 =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [div_pow]
  rw [hcoeff] at h
  exact h

/-- P0093 page 161 equation 6.3. Auxiliary interval diagnostic.
A single negative mode at two paired with residual four has constant
integrand one. Its core integral is two over N rather than a full period. -/
theorem core_diagonal_integral521 (N : ℕ) :
    (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
      Complex.exp ((-(2 * Real.pi * z * (2 : ℕ)) : ℝ) * Complex.I) ^ 2 *
        Complex.exp (((2 * Real.pi * (4 : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ((2 / (N : ℝ) : ℝ) : ℂ) := by
  have hp (z : ℝ) :
      Complex.exp ((-(2 * Real.pi * z * (2 : ℕ)) : ℝ) * Complex.I) ^ 2 *
        Complex.exp (((2 * Real.pi * (4 : ℝ) * z : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    have hz : ((2 : ℕ) : ℂ) * (((-(2 * Real.pi * z * (2 : ℕ)) : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * (4 : ℝ) * z : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast
      ring
    rw [hz, Complex.exp_zero]
  simp_rw [hp]
  rw [intervalIntegral.integral_const]
  simp only [Complex.real_smul, mul_one]
  congr 1
  ring

/-- P0093 page 161 equation 6.3. Auxiliary interval diagnostic.
For N at least three the core diagonal is not the full period coefficient.
This refutes an exact truncated orthogonality substitution only. -/
theorem core_diagonal_not_full_period521 (N : ℕ) (hN : 3 ≤ N) :
    (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
      Complex.exp ((-(2 * Real.pi * z * (2 : ℕ)) : ℝ) * Complex.I) ^ 2 *
        Complex.exp (((2 * Real.pi * (4 : ℝ) * z : ℝ) : ℂ) * Complex.I)) ≠ 1 := by
  rw [core_diagonal_integral521]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) < N := by exact_mod_cast (show 2 < N by omega)
  have hlt : (2 / (N : ℝ) : ℝ) < 1 := (div_lt_one hNp).mpr hN2
  exact_mod_cast ne_of_lt hlt

/-- P0093 page 161 sentence after equation 6.3. The full period logarithmic
model coefficient vanishes at every nonpositive signed residual.
The model itself has positive coefficients starting at frequency two. -/
theorem logarithmic_model_nonpositive521 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (hn : n ≤ 0) :
    (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ), logarithmicModel521 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) = 0 := by
  have hp (j : ℤ) (z : ℝ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * (z + 1) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (j : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
    have he : (((2 * Real.pi * (j : ℝ) * (z + 1) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * (j : ℝ) * z : ℝ) : ℂ) * Complex.I) +
          (j : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hS : Function.Periodic (logarithmicModel521 N) 1 := by
    intro z
    unfold logarithmicModel521
    apply tsum_congr
    intro m
    congr 1
    convert hp (-(m : ℤ)) z using 1 <;> push_cast <;> congr 1 <;> ring
  have hP : Function.Periodic (fun z : ℝ =>
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := hp n
  have hf : Function.Periodic (fun z : ℝ => logarithmicModel521 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := by
    intro z
    dsimp only
    rw [hS z, hp n z]
  have hshift :
      (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ), logarithmicModel521 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      (∫ z in (0 : ℝ)..1, logarithmicModel521 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    simpa only [zero_add, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using
      hf.intervalIntegral_add_eq (-1 / 2) 0
  let a : ℕ → ℂ := fun m => (logCoefficient521 N m : ℂ)
  let b : ℕ → ℂ := fun k => ∑ m ∈ range (k + 1), a m * a (k - m)
  have ha : Summable a := log_coefficients_summable521 N hN
  have hb : Summable b := (summable_norm_sum_mul_range_of_summable_norm ha.norm ha.norm).of_norm
  have hc := negative_series_coefficient_proved357 b hb (-n)
  have hzero : (if -n ≤ 0 then b (-n).natAbs else 0) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      simp [b, a, logCoefficient521]
    · rw [ite_eq_right (by omega)]
  have heq :
      (∫ z in (0 : ℝ)..1, logarithmicModel521 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun z => logarithmicModel521 N z ^ 2) (-n) := by
    rw [coefficient_integral357]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    unfold LeanLab.Perelli1996.Kernel.e
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  rw [hshift, heq]
  change fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
    (fun z => (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2) (-n) = 0
  simp_rw [square_series521 a ha]
  exact hc.trans hzero

/-- P0093 page 161 equation 6.3 and its nonpositive residual case.
The exact full period model coefficient uses the natural part of a signed
residual. At a negative residual the convolution is empty and both sides vanish. -/
theorem logarithmic_model_signed_full_period521 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ), logarithmicModel521 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
        ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) := by
  by_cases hn : 0 ≤ n
  · have hcast : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    simpa only [hcast] using logarithmic_model_full_period521 N hN n.toNat
  · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simpa [hz, logConvolution1622] using
      logarithmic_model_nonpositive521 N hN n (by omega)

end LeanLab.Linnik1951
