module

public import LeanLab.LanguascoPerelli1996.Statements

/-!
P0071 page 358 display 21, finite partial summation before specialization.
All frequencies in this calculation are nonnegative integers.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Partial381
open Real intervalIntegral

/-- Page 358 display 21, exact finite partial summation for the multiplier n. -/
theorem weighted_sum_eq_prefix {m N : ℕ} (hmN : m ≤ N) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc m N, (n : ℂ) * f n) =
      (N : ℂ) * (∑ n ∈ Finset.Icc m N, f n) -
        ∑ k ∈ Finset.Ico m N, ∑ n ∈ Finset.Icc m k, f n := by
  have h := Finset.sum_Ico_by_parts (fun n : ℕ => (n : ℂ)) f
    (show m < N + 1 by omega)
  simp only [smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, one_mul, Finset.Ico_add_one_right_eq_Icc] at h
  have hprefix (k : ℕ) (hk : m ≤ k) :
      (∑ n ∈ Finset.range (k + 1), f n) =
        (∑ n ∈ Finset.range m, f n) + ∑ n ∈ Finset.Icc m k, f n := by
    have hh := Finset.sum_range_add_sum_Ico f (show m ≤ k + 1 by omega)
    rw [Finset.Ico_add_one_right_eq_Icc] at hh
    exact hh.symm
  have hinner : (∑ k ∈ Finset.Ico m N, ∑ n ∈ Finset.range (k + 1), f n) =
      ∑ k ∈ Finset.Ico m N,
        ((∑ n ∈ Finset.range m, f n) + ∑ n ∈ Finset.Icc m k, f n) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hprefix k (Finset.mem_Ico.mp hk).1
  rw [hprefix N hmN, hinner, Finset.sum_add_distrib] at h
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hmN] at h
  linear_combination h

/-- Page 358 display 21, the finite Cauchy Schwarz step in L2.
The squared mass of a sum is at most its number of terms times the sum
of the individual squared masses. -/
theorem sum_mass_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ i ∈ s, f i t‖ ^ 2) ≤
      (s.card : ℝ) * ∑ i ∈ s, ∫ t in a..b, ‖f i t‖ ^ 2 := by
  have hp (t : ℝ) : ‖∑ i ∈ s, f i t‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i t‖ ^ 2 := by
    calc
      _ ≤ (∑ i ∈ s, ‖f i t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  have hcont : Continuous (fun t => ∑ i ∈ s, f i t) := continuous_finsetSum s hf
  have hcont' : Continuous (fun t => ∑ i ∈ s, ‖f i t‖ ^ 2) :=
    continuous_finsetSum s (fun i hi => (hf i hi).norm.pow 2)
  have hh := integral_mono_on (μ := MeasureTheory.volume) hab
    ((hcont.norm.pow 2).intervalIntegrable a b)
    ((continuous_const.mul hcont').intervalIntegrable a b) (fun t _ => hp t)
  simp only [Pi.mul_apply, Pi.pow_apply] at hh
  rw [integral_const_mul, integral_finsetSum (fun i hi => (show IntervalIntegrable (fun t => ‖f i t‖ ^ 2) MeasureTheory.volume a b from ((hf i hi).norm.pow 2).intervalIntegrable a b))] at hh
  exact hh

/-- Page 358 display 21, the L2 consequence of finite partial summation.
Uniform mass bounds for all prefixes give a bound four N squared M
for the sum multiplied by its integer frequencies. -/
theorem weighted_mass_le {m N : ℕ} (hmN : m ≤ N) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n, Continuous (f n)) {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hmass : ∀ k, m ≤ k → k ≤ N →
      (∫ t in a..b, ‖∑ n ∈ Finset.Icc m k, f n t‖ ^ 2) ≤ M) :
    (∫ t in a..b, ‖∑ n ∈ Finset.Icc m N, (n : ℂ) * f n t‖ ^ 2) ≤
      4 * (N : ℝ) ^ 2 * M := by
  let P := fun k t => ∑ n ∈ Finset.Icc m k, f n t
  have hP (k : ℕ) : Continuous (P k) := continuous_finsetSum _ (fun n _ => hf n)
  have heq (t : ℝ) : (∑ n ∈ Finset.Icc m N, (n : ℂ) * f n t) =
      (N : ℂ) * P N t - ∑ k ∈ Finset.Ico m N, P k t := weighted_sum_eq_prefix hmN _
  have hc : Continuous (fun t => ∑ k ∈ Finset.Ico m N, P k t) :=
    continuous_finsetSum _ (fun k _ => hP k)
  have hp (t : ℝ) : ‖(N : ℂ) * P N t - ∑ k ∈ Finset.Ico m N, P k t‖ ^ 2 ≤
      2 * ((N : ℝ) ^ 2 * ‖P N t‖ ^ 2 + ‖∑ k ∈ Finset.Ico m N, P k t‖ ^ 2) := by
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_le ((N : ℂ) * P N t) (∑ k ∈ Finset.Ico m N, P k t)) 2
    have hn : ‖(N : ℂ) * P N t‖ = (N : ℝ) * ‖P N t‖ := by simp [norm_mul]
    rw [hn] at hh
    nlinarith [sq_nonneg ((N : ℝ) * ‖P N t‖ - ‖∑ k ∈ Finset.Ico m N, P k t‖)]
  have hint := integral_mono_on (μ := MeasureTheory.volume) hab
    (((continuous_const.mul (hP N)).sub hc).norm.pow 2 |>.intervalIntegrable a b)
    ((continuous_const.mul ((continuous_const.mul ((hP N).norm.pow 2)).add
      (hc.norm.pow 2))).intervalIntegrable a b) (fun t _ => hp t)
  simp only [Pi.mul_apply, Pi.add_apply] at hint
  rw [integral_const_mul, integral_add
    (((hP N).norm.pow 2).intervalIntegrable a b |>.const_mul _)
    ((hc.norm.pow 2).intervalIntegrable a b), integral_const_mul] at hint
  have hs := sum_mass_le (Finset.Ico m N) P (fun k _ => hP k) hab
  have hsum : (∑ k ∈ Finset.Ico m N, ∫ t in a..b, ‖P k t‖ ^ 2) ≤
      ((Finset.Ico m N).card : ℝ) * M := by
    calc
      _ ≤ ∑ _k ∈ Finset.Ico m N, M := Finset.sum_le_sum (fun k hk =>
        hmass k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2.le)
      _ = _ := by simp
  have hcard : ((Finset.Ico m N).card : ℝ) ≤ N := by
    simp only [Nat.card_Ico]
    exact_mod_cast Nat.sub_le N m
  have hc0 : 0 ≤ ((Finset.Ico m N).card : ℝ) := by positivity
  have hs' : (∫ t in a..b, ‖∑ k ∈ Finset.Ico m N, P k t‖ ^ 2) ≤ (N : ℝ) ^ 2 * M := by
    calc
      _ ≤ ((Finset.Ico m N).card : ℝ) * ∑ k ∈ Finset.Ico m N, ∫ t in a..b, ‖P k t‖ ^ 2 := hs
      _ ≤ ((Finset.Ico m N).card : ℝ) * (((Finset.Ico m N).card : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum hc0
      _ ≤ (N : ℝ) ^ 2 * M := by nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcard 2) hM]
  have hN := hmass N hmN le_rfl
  have heqfun : (fun t => ∑ n ∈ Finset.Icc m N, (n : ℂ) * f n t) =
      fun t => (N : ℂ) * P N t - ∑ k ∈ Finset.Ico m N, P k t := funext heq
  simp_rw [heq]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at hint
  nlinarith [mul_le_mul_of_nonneg_left hN (sq_nonneg (N : ℝ))]

/-- Page 358 display 21. Differentiation multiplies each frequency n
by two pi i n. The finite polynomial has no convergence obligation. -/
theorem polynomial_hasDerivAt (m N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun v : ℝ => ∑ n ∈ Finset.Icc m N, c n * e ((n : ℝ) * v))
      ((2 * Real.pi * Complex.I) *
        ∑ n ∈ Finset.Icc m N, (n : ℂ) * (c n * e ((n : ℝ) * t))) t := by
  have hcast : HasDerivAt (fun v : ℝ => (v : ℂ)) (1 : ℂ) t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      Complex.ofRealCLM.hasDerivAt
  have hi (n : ℕ) : HasDerivAt (fun v : ℝ => c n * e ((n : ℝ) * v))
      ((2 * Real.pi * Complex.I) * ((n : ℂ) * (c n * e ((n : ℝ) * t)))) t := by
    have hh := ((hcast.const_mul ((2 * Real.pi * Complex.I) * (n : ℂ))).cexp).const_mul (c n)
    convert hh using 1 <;> simp only [e, Complex.ofReal_mul, Complex.ofReal_natCast, mul_one] <;> ring
  have hh := HasDerivAt.fun_sum (u := Finset.Icc m N) (fun n _ => hi n)
  simpa only [Finset.mul_sum] using hh

/-- Page 358 display 21. A finite exponential polynomial with every
prefix mass at most M has derivative mass at most sixteen pi squared
N squared M. This is the integer frequency form of L2 partial summation. -/
theorem polynomial_derivative_mass {m N : ℕ} (hmN : m ≤ N) (c : ℕ → ℂ)
    {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hmass : ∀ k, m ≤ k → k ≤ N →
      (∫ t in a..b, ‖∑ n ∈ Finset.Icc m k, c n * e ((n : ℝ) * t)‖ ^ 2) ≤ M) :
    (∫ t in a..b,
      ‖deriv (fun v : ℝ => ∑ n ∈ Finset.Icc m N, c n * e ((n : ℝ) * v)) t‖ ^ 2) ≤
        16 * Real.pi ^ 2 * (N : ℝ) ^ 2 * M := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => c n * e ((n : ℝ) * t)) := by
    unfold e
    fun_prop
  have hh := weighted_mass_le hmN (fun n t => c n * e ((n : ℝ) * t)) hc hab hM hmass
  have hnorm (t : ℝ) :
      ‖deriv (fun v : ℝ => ∑ n ∈ Finset.Icc m N, c n * e ((n : ℝ) * v)) t‖ ^ 2 =
        (4 * Real.pi ^ 2) * ‖∑ n ∈ Finset.Icc m N, (n : ℂ) * (c n * e ((n : ℝ) * t))‖ ^ 2 := by
    rw [(polynomial_hasDerivAt m N c t).deriv, norm_mul, mul_pow]
    have hconst : ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 = 4 * Real.pi ^ 2 := by
      simp [norm_mul, abs_of_pos Real.pi_pos]
      <;> ring
    rw [hconst]
  simp_rw [hnorm]
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * Real.pi ^ 2 by positivity)
  nlinarith

end LeanLab.LanguascoPerelli1996.Partial381


