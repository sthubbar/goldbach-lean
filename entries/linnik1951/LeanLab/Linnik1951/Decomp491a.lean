module

public import LeanLab.Linnik1951.Data491
public import LeanLab.Linnik1951.Geometry491
public import LeanLab.Linnik1951.Decomp376d

/-!
P0093 pages 165 and 166. Modulus and tuple bookkeeping for equation 8.2.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. P0093 page 166 equation 8.2. Auxiliary telescoping estimate for the
sum of reciprocal square roots of positive moduli. -/
theorem sum_inv_sqrt491 (Q : ℕ) :
    (∑ i ∈ range Q, 1 / Real.sqrt (i + 1 : ℕ)) ≤ 2 * Real.sqrt Q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [sum_range_succ]
    have hx : 0 < Real.sqrt (Q + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hy : Real.sqrt (Q : ℝ) ≤ Real.sqrt (Q + 1 : ℕ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.le_succ Q
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Q by positivity)
    have ht := Real.sq_sqrt (show (0 : ℝ) ≤ (Q + 1 : ℕ) by positivity)
    have hdiff : 1 / Real.sqrt (Q + 1 : ℕ) ≤
        2 * (Real.sqrt (Q + 1 : ℕ) - Real.sqrt Q) := by
      apply (div_le_iff₀ hx).mpr
      have hn := sq_nonneg (Real.sqrt (Q + 1 : ℕ) - Real.sqrt Q)
      push_cast at ht hn ⊢
      nlinarith
    linarith

/-- LEAF. P0093 page 166 equation 8.2. Summation over the moduli keeps the
square root of Q rather than Q in the second error term. -/
theorem modulus_error_sum491 (Q : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    (∑ q ∈ Icc 1 Q, (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ))) ≤
      (Q : ℝ) / τ + 2 * Real.sqrt Q / Real.sqrt τ := by
  have heq : (∑ q ∈ Icc 1 Q, (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ))) =
      ∑ i ∈ range Q, (1 / τ + 1 / Real.sqrt (((i + 1 : ℕ) : ℝ) * τ)) := by
    have hset : Ico 1 (Q + 1) = Icc 1 Q := by
      ext i
      simp only [mem_Ico, mem_Icc]
      omega
    simpa only [zero_add, Nat.Ico_zero_eq_range, hset] using
      (sum_Ico_add' (fun q : ℕ => 1 / τ + 1 / Real.sqrt ((q : ℝ) * τ)) 0 Q 1).symm
  rw [heq]
  have hfactor (i : ℕ) : 1 / Real.sqrt (((i + 1 : ℕ) : ℝ) * τ) =
      (1 / Real.sqrt τ) * (1 / Real.sqrt (i + 1 : ℕ)) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), ← one_div_mul_one_div_rev]
  simp_rw [hfactor]
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
  calc
    _ ≤ (Q : ℝ) * (1 / τ) + (1 / Real.sqrt τ) * (2 * Real.sqrt Q) := by
      gcongr
      exact sum_inv_sqrt491 Q
    _ = _ := by ring

/-- LEAF. P0093 page 166 equation 8.2. At the chosen Q and tau the two
scales have the common saving three over one hundred forty. -/
theorem major_parameter_saving491 (x : ℝ) (hx : 1 ≤ x) :
    x ^ (1 / 10 : ℝ) / x ^ (1 / 7 : ℝ) +
        Real.sqrt (x ^ (1 / 10 : ℝ) / x ^ (1 / 7 : ℝ)) ≤
      2 * x ^ (-(3 / 140 : ℝ)) := by
  have hpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hratio : x ^ (1 / 10 : ℝ) / x ^ (1 / 7 : ℝ) =
      x ^ (-(3 / 70 : ℝ)) := by
    rw [← Real.rpow_sub hpos]
    norm_num
  rw [hratio, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]
  have hhalf : (-(3 / 70 : ℝ)) * (1 / 2 : ℝ) = -(3 / 140 : ℝ) := by norm_num
  rw [hhalf]
  have hle : x ^ (-(3 / 70 : ℝ)) ≤ x ^ (-(3 / 140 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  linarith

/-- P0093 page 165 equation 8.1. The full tuple damping weight. -/
noncomputable def tupleWeight491 (k N : ℕ) (ν : Fin k → ℕ) : ℝ :=
  ∏ i, Real.exp (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N)

/-- P0093 page 165 equation 8.1. The residual is signed before selecting its main term. -/
def tupleResidual491 (k N : ℕ) (ν : Fin k → ℕ) : ℤ :=
  (N : ℤ) - ∑ i, (2 ^ (ν i + 1) : ℕ)

/-- P0093 page 161 equation 6.4 before the convolution asymptotic. -/
noncomputable def localMain491 (N q : ℕ) (n : ℤ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat *
    ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)

/-- P0093 page 165 equation 8.1 with the exact convolution retained. -/
noncomputable def convolutionMain491 (k N : ℕ) : ℝ :=
  ∑ ν ∈ residualTuples357 k N,
    truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) *
      logConvolution1622 (N - ∑ i, 2 ^ (ν i).val)

/-- LEAF. P0093 page 161 after equation 6.3. There are no convolution pairs
when the natural residual is at most three. -/
theorem logConvolution_vanish491 (n : ℕ) (hn : n ≤ 3) :
    logConvolution1622 n = 0 := by
  unfold logConvolution1622
  apply Finset.sum_eq_zero
  intro m hm
  have hh := Finset.mem_Icc.mp hm
  omega

/-- LEAF. P0093 page 165 equation 8.1. Taking the natural part of the signed
residual gives truncated natural subtraction, including at negative residuals. -/
theorem tuple_residual_toNat491 (k N : ℕ) (ν : Fin k → ℕ) :
    (tupleResidual491 k N ν).toNat = N - ∑ i, 2 ^ (ν i + 1) := by
  unfold tupleResidual491
  omega

/-- LEAF. P0093 page 165 equation 8.1. For a tuple with nonnegative residual,
the tuple damping and residual damping multiply to exp of minus one. -/
theorem tuple_damping_cancel491 (k N : ℕ) (hN : 1 ≤ N) (ν : Fin k → ℕ)
    (hν : ∑ i, 2 ^ (ν i + 1) ≤ N) :
    tupleWeight491 k N ν *
      Real.exp (-((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) / N) = Real.exp (-1) := by
  unfold tupleWeight491
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  rw [Nat.cast_sub hν]
  simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
  push_cast
  have hNr : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- LEAF. P0093 page 165 equation 8.1. The finite singular coefficient is real.
The divisor expansion of the Ramanujan sum supplies this fact. -/
theorem truncated_coefficient491 (N n : ℕ) :
    (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n) =
      (truncatedSingular357 N n : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro q hq
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hram : (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).im = 0 := by
      rw [LeanLab.Perelli1996.Ramanujan103.ramanujanSum_divisor_expansion q n hq0,
        Complex.im_sum]
      apply Finset.sum_eq_zero
      intro d hd
      split_ifs <;> simp
    simp only [Complex.mul_im, Complex.ofReal_im, hram, mul_zero, zero_mul, add_zero]

/-- LEAF. P0093 page 165 equation 8.1. One positive residual tuple contributes
its finite singular coefficient times the exact convolution with common damping. -/
theorem tuple_convolution_term491 (k N : ℕ) (hN : 1 ≤ N)
    (ν : Fin k → Fin (N + 1)) (hν : ν ∈ residualTuples357 k N) :
    (tupleWeight491 k N (fun i => (ν i).val - 1) : ℂ) *
      (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
        localMain491 N q (tupleResidual491 k N (fun i => (ν i).val - 1))) =
      ((Real.exp (-1) * (truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) *
        logConvolution1622 (N - ∑ i, 2 ^ (ν i).val)) : ℝ) : ℂ) := by
  have hv (i : Fin k) : (ν i).val - 1 + 1 = (ν i).val := by
    have hh := (mem_filter.mp hν).2.1 i
    omega
  have hs : ∑ i, 2 ^ (ν i).val ≤ N := by
    have hh := (mem_filter.mp hν).2.2.1
    omega
  have hres : (tupleResidual491 k N (fun i => (ν i).val - 1)).toNat =
      N - ∑ i, 2 ^ (ν i).val := by
    rw [tuple_residual_toNat491]
    simp_rw [hv]
  simp_rw [localMain491, hres]
  rw [← Finset.sum_mul, truncated_coefficient491]
  have hc := tuple_damping_cancel491 k N hN (fun i => (ν i).val - 1)
    (by simpa only [hv] using hs)
  simp only [hv] at hc
  simp only [← Complex.ofReal_mul]
  congr 1
  calc
    _ = (tupleWeight491 k N (fun i => (ν i).val - 1) *
      Real.exp (-((N - ∑ i, 2 ^ (ν i).val : ℕ) : ℝ) / N)) *
      (truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) *
        logConvolution1622 (N - ∑ i, 2 ^ (ν i).val)) := by ring
    _ = _ := by rw [hc]

/-- LEAF. P0093 page 165 equation 8.1. Auxiliary absolutely convergent product
identity for the full tuple series. The proof uses Mathlib product sums and
induction on the finite number of factors. -/
theorem tuple_product_sum491 (f : ℕ → ℝ) (hf : Summable f) (k : ℕ) :
    Summable (fun ν : Fin k → ℕ => ∏ i, f (ν i)) ∧
      (∑' n, f n) ^ k = ∑' ν : Fin k → ℕ, ∏ i, f (ν i) := by
  induction k with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp [tsum_fintype]
  | succ k ih =>
    have hprod : Summable (fun z : (Fin k → ℕ) × ℕ =>
        (∏ i, f (z.1 i)) * f z.2) := (ih.1.norm.mul_norm hf.norm).of_norm
    let e : ((Fin k → ℕ) × ℕ) ≃ (Fin (k + 1) → ℕ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ))
    constructor
    · have hc := hprod.comp_injective e.symm.injective
      convert hc using 1
      ext ν
      simp [e, Fin.prod_univ_succ, Fin.tail, mul_comm]
    · rw [pow_succ, ih.2]
      calc
        _ = ∑' z : (Fin k → ℕ) × ℕ, (∏ i, f (z.1 i)) * f z.2 :=
          tsum_mul_tsum_of_summable_norm ih.1.norm hf.norm
        _ = _ := by
          simpa [e, Fin.prod_univ_succ, Fin.tail, mul_comm] using
            e.tsum_eq (fun ν : Fin (k + 1) → ℕ => ∏ i, f (ν i))

/-- LEAF. P0093 pages 161 and 165 equations 7.1 and 8.1. The total full tuple
weight is the kth power of the positive dyadic damping sum. -/
theorem tuple_weight_sum491 (k N : ℕ) (hN : 1 ≤ N) :
    Summable (tupleWeight491 k N) ∧
      (∑' ν, tupleWeight491 k N ν) = ‖powerFourier111 N 0‖ ^ k := by
  let f : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp
      (add_left_injective 1)
  have hf : Summable f := (damping_summable111 N hN).comp_injective hi
  have hh := tuple_product_sum491 f hf k
  have heq : powerFourier111 N 0 = ((∑' m, f m : ℝ) : ℂ) := by
    unfold powerFourier111
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    simp [f]
  refine ⟨hh.1, ?_⟩
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun m => (Real.exp_pos _).le))]
  exact hh.2.symm

/-- LEAF. P0093 page 165 equation 8.1. The absolutely convergent complex
product identity retains all phases of the full tuple series. -/
theorem tuple_product_complex491 (f : ℕ → ℂ) (hf : Summable (fun n => ‖f n‖)) (k : ℕ) :
    Summable (fun ν : Fin k → ℕ => ∏ i, f (ν i)) ∧
      (∑' n, f n) ^ k = ∑' ν : Fin k → ℕ, ∏ i, f (ν i) := by
  induction k with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp [tsum_fintype]
  | succ k ih =>
    have hprod : Summable (fun z : (Fin k → ℕ) × ℕ =>
        (∏ i, f (z.1 i)) * f z.2) := (ih.1.norm.mul_norm hf).of_norm
    let e : ((Fin k → ℕ) × ℕ) ≃ (Fin (k + 1) → ℕ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ))
    constructor
    · have hc := hprod.comp_injective e.symm.injective
      convert hc using 1
      ext ν
      simp [e, Fin.prod_univ_succ, Fin.tail, mul_comm]
    · rw [pow_succ, ih.2]
      calc
        _ = ∑' z : (Fin k → ℕ) × ℕ, (∏ i, f (z.1 i)) * f z.2 :=
          tsum_mul_tsum_of_summable_norm ih.1.norm hf
        _ = _ := by
          simpa [e, Fin.prod_univ_succ, Fin.tail, mul_comm] using
            e.tsum_eq (fun ν : Fin (k + 1) → ℕ => ∏ i, f (ν i))

/-- LEAF. P0093 page 165 equation 8.1. Expanding T to the kth power gives an
absolutely convergent series over every positive exponent tuple with its full
complex Fourier phase and its exact damping weight. -/
theorem tuple_fourier_expansion491 (k N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    Summable (fun ν : Fin k → ℕ => (tupleWeight491 k N ν : ℂ) *
      Complex.exp (((-(2 * Real.pi * α *
        ((∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) ∧
      powerFourier111 N α ^ k =
        ∑' ν : Fin k → ℕ, (tupleWeight491 k N ν : ℂ) *
          Complex.exp (((-(2 * Real.pi * α *
            ((∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  let f : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp (((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) : ℂ) * Complex.I)
  have hf : Summable (fun m => ‖f m‖) := (power_fourier_summable111 N hN α).norm
  have hp := tuple_product_complex491 f hf k
  have heq (ν : Fin k → ℕ) : (∏ i, f (ν i)) =
      (tupleWeight491 k N ν : ℂ) * Complex.exp
        (((-(2 * Real.pi * α * ((∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    simp only [f, Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Complex.exp_sum]
    congr 1
    congr 1
    push_cast
    simp only [Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  refine ⟨hp.1.congr heq, ?_⟩
  change (∑' m, f m) ^ k = _
  rw [hp.2]
  exact tsum_congr heq

/-- LEAF. P0093 page 165 equation 8.1. The absolutely convergent full tuple
series can be integrated term by term on any subset of the unit interval.
This step retains every signed residual and requires no rational arc geometry. -/
theorem tuple_integral_exchange491 (k N : ℕ) (hN : 1 ≤ N) (s : Set ℝ)
    (hs : s ⊆ Set.Icc 0 1) :
    HasSum (fun ν : Fin k → ℕ => (tupleWeight491 k N ν : ℂ) *
      ∫ α in s, primeFourier111 N α ^ 2 *
        Complex.exp (((2 * Real.pi * α * (tupleResidual491 k N ν : ℝ) : ℝ) : ℂ) * Complex.I))
      (∫ α in s, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I)) := by
  let F : (Fin k → ℕ) → ℝ → ℂ := fun ν α => (tupleWeight491 k N ν : ℂ) *
    (primeFourier111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * (tupleResidual491 k N ν : ℝ) : ℝ) : ℂ) * Complex.I))
  have hS := continuous_prime_fourier111 N hN
  have hFi (ν : Fin k → ℕ) : IntegrableOn (F ν) s := by
    have hfull : IntegrableOn (F ν) (Set.Icc 0 1) := by
      apply Continuous.integrableOn_Icc
      dsimp [F]
      fun_prop
    exact hfull.mono_set hs
  have hnorm (ν : Fin k → ℕ) (α : ℝ) :
      ‖F ν α‖ = tupleWeight491 k N ν * ‖primeFourier111 N α‖ ^ 2 := by
    dsimp [F]
    simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ tupleWeight491 k N ν by unfold tupleWeight491; positivity)]
  have hsum : Summable (fun ν : Fin k → ℕ => ∫ α in s, ‖F ν α‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact (tuple_weight_sum491 k N hN).1.mul_right _
  have hpoint (α : ℝ) : primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I) = ∑' ν, F ν α := by
    rw [(tuple_fourier_expansion491 k N hN α).2, ← tsum_mul_left, ← tsum_mul_right]
    apply tsum_congr
    intro ν
    have hp : Complex.exp (((-(2 * Real.pi * α *
        ((∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * α * (tupleResidual491 k N ν : ℝ) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      unfold tupleResidual491
      push_cast
      ring
    dsimp [F]
    calc
      _ = (tupleWeight491 k N ν : ℂ) * primeFourier111 N α ^ 2 *
        (Complex.exp (((-(2 * Real.pi * α *
          ((∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [hp]; ring
  have hh := hasSum_integral_of_summable_integral_norm hFi hsum
  convert hh using 1
  · funext ν
    dsimp [F]
    rw [integral_const_mul]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint

/-- LEAF. P0093 page 165 equation 8.1. The prime Fourier series has period one.
This holds term by term and does not require a prime distribution estimate. -/
theorem prime_periodic491 (N : ℕ) : Function.Periodic (primeFourier111 N) 1 := by
  intro α
  unfold primeFourier111
  apply tsum_congr
  intro p
  congr 1
  have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
        ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by push_cast; ring
  rw [he, Complex.exp_add]
  have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
  rw [hp, mul_one]

/-- LEAF. P0093 page 165 equation 8.1. Every signed integer residual prime
square integrand has period one. Negative residuals satisfy the same identity. -/
theorem residual_integrand_periodic491 (N : ℕ) (n : ℤ) :
    Function.Periodic (fun α : ℝ => primeFourier111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)) 1 := by
  intro α
  dsimp only
  rw [prime_periodic491 N α]
  congr 1
  have he : (((2 * Real.pi * (α + 1) * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) +
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  have hp : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I n using 1 <;> ring
  rw [he, Complex.exp_add, hp, mul_one]

/-- LEAF. P0093 pages 165 and 166 equation 8.1. A continuous period one
function has the exact rational arc partition integral when Q is N to one tenth
and tau is N to one seventh. The clipped endpoint arcs are joined by periodicity.
This statement has no primes, no character series and no exponent tuples. -/
theorem major_arc_partition491 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ f : ℝ → ℂ,
      Continuous f → Function.Periodic f 1 →
      (∫ α in majorArcs280 N, f α) =
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
                (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              f ((a : ℝ) / q + z) := by
  exact major_arc_partition_proved491

/-- LEAF. P0093 page 165 equation 8.1. Expand the infinite damped T
series, exchange its sum and the integral, and join the disjoint rational
arcs. The two clipped endpoint pieces are joined by period one. Every signed
residual is retained. This is an exact identity with no local expansion input. -/
theorem major_tuple_identity491 (k : ℕ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      HasSum (fun ν : Fin k → ℕ =>
        (tupleWeight491 k N ν : ℂ) *
          ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
            localArc1622 N q (tupleResidual491 k N ν))
        (∫ α in majorArcs280 N,
          primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
            Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨N0, hpart⟩ := major_arc_partition491
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by have := le_max_left 1 N0; omega
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hS := continuous_prime_fourier111 N hN1
  have hlocal (ν : Fin k → ℕ) :
      (∫ α in majorArcs280 N, primeFourier111 N α ^ 2 *
        Complex.exp (((2 * Real.pi * α * (tupleResidual491 k N ν : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
        localArc1622 N q (tupleResidual491 k N ν) := by
    rw [hpart N hN0 _ (by fun_prop) (residual_integrand_periodic491 N _)]
    apply Finset.sum_congr rfl
    intro q hq
    unfold localArc1622
    apply Finset.sum_congr rfl
    intro a ha
    apply intervalIntegral.integral_congr
    intro z hz
    congr 1
    congr 1
    push_cast
    ring
  have hh := tuple_integral_exchange491 k N hN1 (majorArcs280 N) (fun α hα => hα.1)
  convert hh using 1
  funext ν
  rw [hlocal]

/-- LEAF. P0093 page 165 equation 8.1. The convolution main term has
finite support in the positive residual tuples. The damping factors multiply
to exp of minus one. No estimate and no local arc integral occurs here. -/
theorem tuple_convolution_identity491 (k N : ℕ) (hN : 1 ≤ N) (hev : Even N) :
    HasSum (fun ν : Fin k → ℕ =>
      (tupleWeight491 k N ν : ℂ) *
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          localMain491 N q (tupleResidual491 k N ν))
      ((Real.exp (-1) * convolutionMain491 k N : ℝ) : ℂ) := by
  classical
  let S := residualTuples357 k N
  let e : {ν // ν ∈ S} → (Fin k → ℕ) := fun ν i => (ν.val i).val - 1
  let f : (Fin k → ℕ) → ℂ := fun ν =>
    (tupleWeight491 k N ν : ℂ) *
      ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
        localMain491 N q (tupleResidual491 k N ν)
  have hi : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have ha := (mem_filter.mp a.property).2.1 i
    have hb := (mem_filter.mp b.property).2.1 i
    have hh := congrFun h i
    dsimp [e] at hh
    omega
  have hsupport (ν : Fin k → ℕ)
      (hν : 2 ≤ (tupleResidual491 k N ν).toNat) : ν ∈ Set.range e := by
    rw [tuple_residual_toNat491] at hν
    have hs : ∑ i, 2 ^ (ν i + 1) ≤ N := by omega
    have hb (i : Fin k) : ν i + 1 < N + 1 := by
      have hi : 2 ^ (ν i + 1) ≤ ∑ j, 2 ^ (ν j + 1) :=
        single_le_sum (f := fun j : Fin k => 2 ^ (ν j + 1))
          (fun j _ => Nat.zero_le _) (mem_univ i)
      have hp : ν i + 1 < 2 ^ (ν i + 1) := Nat.lt_two_pow_self
      omega
    let v : Fin k → Fin (N + 1) := fun i => ⟨ν i + 1, hb i⟩
    have hv : v ∈ S := by
      change v ∈ residualTuples357 k N
      simp only [residualTuples357, mem_filter, mem_univ, true_and]
      refine ⟨fun i => by dsimp [v]; omega, ?_, ?_⟩
      · exact hν
      · apply even_iff_two_dvd.mpr
        apply Nat.dvd_sub (even_iff_two_dvd.mp hev)
        apply Finset.dvd_sum
        intro i hi
        exact dvd_pow_self 2 (by dsimp [v]; omega)
    refine ⟨⟨v, hv⟩, ?_⟩
    funext i
    simp [e, v]
  have houtside : ∀ ν, ν ∉ Set.range e → f ν = 0 := by
    intro ν hν
    have hn : (tupleResidual491 k N ν).toNat ≤ 1 := by
      by_contra hh
      exact hν (hsupport ν (by omega))
    have hz := logConvolution_vanish491 _ (show (tupleResidual491 k N ν).toNat ≤ 3 by omega)
    simp [f, localMain491, hz]
  have hterm (ν : {ν // ν ∈ S}) : f (e ν) =
      ((Real.exp (-1) * (truncatedSingular357 N (N - ∑ i, 2 ^ (ν.val i).val) *
        logConvolution1622 (N - ∑ i, 2 ^ (ν.val i).val)) : ℝ) : ℂ) :=
    tuple_convolution_term491 k N hN ν.val ν.property
  apply (hi.hasSum_iff houtside).mp
  have hh := hasSum_fintype (f ∘ e)
  have heq : (∑ ν : {ν // ν ∈ S}, f (e ν)) =
      ((Real.exp (-1) * convolutionMain491 k N : ℝ) : ℂ) := by
    simp_rw [hterm]
    rw [← Complex.ofReal_sum, ← mul_sum]
    congr 2
    simpa only [convolutionMain491, S] using
      Finset.sum_coe_sort S (fun ν => truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) *
        logConvolution1622 (N - ∑ i, 2 ^ (ν i).val))
  exact heq ▸ hh

/-- LEAF. P0093 page 165 equation 8.1. The explicit relative correction controls
the replacement of the exact convolution by n over log squared n. -/
theorem convolution_main_error491 (k N : ℕ) (B : ℝ)
    (hC : ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) :
    |convolutionMain491 k N - truncatedMain357 k N| ≤ B * majorRelative376 k N := by
  classical
  have heq : convolutionMain491 k N - truncatedMain357 k N =
      ∑ ν ∈ residualTuples357 k N,
        truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) *
          (logConvolution1622 (N - ∑ i, 2 ^ (ν i).val) -
            (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2) := by
    unfold convolutionMain491 truncatedMain357 residualTuples357
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro ν hν
    ring
  rw [heq, majorRelative376, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro ν hν
  have hn := (mem_filter.mp hν).2.2.1
  rw [abs_mul]
  calc
    _ ≤ |truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val)| *
        (B * ((N - ∑ i, 2 ^ (ν i).val : ℕ) /
          Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2) *
          (1 / Real.sqrt (Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ)))) :=
      mul_le_mul_of_nonneg_left (hC _ hn) (abs_nonneg _)
    _ = _ := by ring

/-- LEAF. P0093 page 166 equation 8.2. The summed modulus error has a saving
stronger than the one thousandth used by the sealed target. -/
theorem modulus_error_saving491 (N : ℕ) (hN : 1 ≤ N) :
    (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
        1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤
      4 * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hτ : 0 < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hp _
  have hQ : (⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Nat.floor_le (by positivity)
  have hs := modulus_error_sum491 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ _ hτ
  have hdiv : Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ)) /
      Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) =
      Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)) :=
    (Real.sqrt_div (by positivity) _).symm
  calc
    _ ≤ (⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) +
        2 * Real.sqrt ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ /
          Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) := hs
    _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) +
        2 * Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ)) /
          Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) := by gcongr
    _ ≤ 2 * ((N : ℝ) ^ (1 / 10 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) +
        Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ))) := by
      rw [show 2 * Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ)) /
        Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) =
        2 * (Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ)) /
          Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) by ring, hdiv]
      have hnonneg : 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
      linarith
    _ ≤ 4 * (N : ℝ) ^ (-(3 / 140 : ℝ)) := by
      nlinarith [major_parameter_saving491 (N : ℝ) hNr]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNr
        (show (-(3 / 140 : ℝ)) ≤ -(1 / 1000 : ℝ) by norm_num)) (by norm_num)

/-- LEAF. P0093 page 165 equation 8.1. A uniform signed residual error can be
summed against every damped tuple. This does not delete any negative residual. -/
theorem weighted_error_sum491 {ι : Type*} (w : ι → ℝ) (hw : Summable w)
    (hw0 : ∀ i, 0 ≤ w i) (f g : ι → ℂ) (F G : ℂ)
    (hf : HasSum (fun i => (w i : ℂ) * f i) F)
    (hg : HasSum (fun i => (w i : ℂ) * g i) G)
    (D : ℝ) (hD : ∀ i, ‖f i - g i‖ ≤ D) :
    ‖F - G‖ ≤ (∑' i, w i) * D := by
  have he := hf.sub hg
  have hterm (i : ι) : ‖(w i : ℂ) * f i - (w i : ℂ) * g i‖ ≤ w i * D := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
    exact mul_le_mul_of_nonneg_left (hD i) (hw0 i)
  calc
    _ = ‖∑' i, ((w i : ℂ) * f i - (w i : ℂ) * g i)‖ := by rw [he.tsum_eq]
    _ ≤ ∑' i, ‖(w i : ℂ) * f i - (w i : ℂ) * g i‖ :=
      norm_tsum_le_tsum_norm he.summable.norm
    _ ≤ ∑' i, w i * D := Summable.tsum_le_tsum hterm he.summable.norm (hw.mul_right D)
    _ = _ := tsum_mul_right

/-- LEAF. P0093 page 165 equation 8.1. Sum the supplied local error over all
moduli at one signed residual. Only LocalExpansion1622 is used. -/
theorem local_error_sum491 (B : ℝ) (N0 N : ℕ) (hL : LocalExpansion1622 B N0)
    (hN : N0 < N) (n : ℤ) (hn : n ≤ N) :
    ‖(∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊, localArc1622 N q n) -
      ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊, localMain491 N q n‖ ≤
      B * (N : ℝ) * Real.log N ^ 13 *
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  rw [← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q hq
  obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hq
  have hqr : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    (Nat.cast_le.mpr hqQ).trans (Nat.floor_le (by positivity))
  exact hL N hN q hq1 hqr n hn

/-- LEAF. P0093 pages 165 and 166 equations 8.1 and 8.2. The local expansion
and the two exact tuple identities give the power saving before any
convolution asymptotic. CONDITIONAL on the supplied local expansion. Both tuple identities are proved. -/
theorem local_to_major_convolution491 (k : ℕ) (B : ℝ) (hB : 0 < B) (N0 : ℕ)
    (hL : LocalExpansion1622 B N0) :
    ∃ A : ℝ, 0 < A ∧ ∃ N1 : ℕ, ∀ N : ℕ, Even N → N1 < N →
      |arcContribution280 k N (majorArcs280 N) - convolutionMain491 k N| ≤
        A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  obtain ⟨C, hC, NC, hCbound⟩ := power_uniform_log_proved357
  obtain ⟨NT, hT⟩ := major_tuple_identity491 k
  refine ⟨4 * Real.exp 1 * B * C ^ k, by positivity,
    max 2 (max N0 (max NC NT)), ?_⟩
  intro N hev hN
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNC : NC < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNT : NT < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN1 : 1 ≤ N := by omega
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hNr : (0 : ℝ) < N := by positivity
  let D : ℝ := B * (N : ℝ) * Real.log N ^ 13 *
    (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
        1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD : D ≤ B * (N : ℝ) * Real.log N ^ 13 *
      (4 * (N : ℝ) ^ (-(1 / 1000 : ℝ))) := by
    dsimp [D]
    gcongr
    exact modulus_error_saving491 N hN1
  have hw := tuple_weight_sum491 k N hN1
  have hh := weighted_error_sum491 (tupleWeight491 k N) hw.1
    (fun ν => by unfold tupleWeight491; positivity)
    (fun ν => ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
      localArc1622 N q (tupleResidual491 k N ν))
    (fun ν => ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
      localMain491 N q (tupleResidual491 k N ν))
    _ _ (hT N hNT) (tuple_convolution_identity491 k N hN1 hev) D
    (fun ν => local_error_sum491 B N0 N hL hN0 _ (by
      unfold tupleResidual491
      have hs : (0 : ℤ) ≤ ∑ i : Fin k, (2 ^ (ν i + 1) : ℕ) := by positivity
      omega))
  rw [hw.2] at hh
  have hpow : ‖powerFourier111 N 0‖ ^ k ≤ C ^ k * Real.log N ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCbound N hNC 0) k
  have hre : |arcContribution280 k N (majorArcs280 N) - convolutionMain491 k N| ≤
      Real.exp 1 * ‖(∫ α in majorArcs280 N,
          primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
            Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-1) * convolutionMain491 k N : ℝ) : ℂ)‖ := by
    have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
    have heq : arcContribution280 k N (majorArcs280 N) - convolutionMain491 k N =
      Real.exp 1 * ((∫ α in majorArcs280 N,
          primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
            Complex.exp (((2 * Real.pi * α * N : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-1) * convolutionMain491 k N : ℝ) : ℂ)).re := by
      simp only [Complex.sub_re, Complex.ofReal_re, arcContribution280]
      rw [mul_sub, ← mul_assoc, he, one_mul]
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos 1)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos _).le
  have heqpow : (N : ℝ) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) =
      (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) := by
    simpa only [Real.rpow_one, sub_eq_add_neg] using
      (Real.rpow_add hNr (1 : ℝ) (-(1 / 1000 : ℝ))).symm
  calc
    _ ≤ Real.exp 1 * (‖powerFourier111 N 0‖ ^ k * D) :=
      hre.trans (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)
    _ ≤ Real.exp 1 * ((C ^ k * Real.log N ^ k) *
        (B * (N : ℝ) * Real.log N ^ 13 * (4 * (N : ℝ) ^ (-(1 / 1000 : ℝ))))) := by
      gcongr
    _ = _ := by
      rw [pow_add]
      calc
        _ = (4 * Real.exp 1 * B * C ^ k) *
          ((N : ℝ) * (N : ℝ) ^ (-(1 / 1000 : ℝ))) *
          (Real.log N ^ k * Real.log N ^ 13) := by ring
        _ = _ := by rw [heqpow]

/-- LEAF. P0093 pages 165 and 166 equations 8.1 and 8.2. Elementary final
assembly with the convolution estimate supplied as a hypothesis.
CONDITIONAL on the supplied local expansion and convolution estimate. -/
theorem major_bookkeeping_assembled491 (k : ℕ) (B : ℝ) (hB : 0 < B) (N0 : ℕ)
    (hL : LocalExpansion1622 B N0) (B' : ℝ) (hB' : 0 < B')
    (hC : ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B' * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) :
    ∃ A : ℝ, 0 < A ∧ ∃ N1 : ℕ, ∀ N : ℕ, Even N → N1 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  obtain ⟨C, hCpos, NC, hClocal⟩ := local_to_major_convolution491 k B hB N0 hL
  refine ⟨max C B', lt_of_lt_of_le hCpos (le_max_left _ _), max 2 NC, ?_⟩
  intro N hev hN
  have hNC : NC < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hrel : 0 ≤ majorRelative376 k N := by
    unfold majorRelative376
    apply Finset.sum_nonneg
    intro ν hν
    positivity
  calc
    _ ≤ |arcContribution280 k N (majorArcs280 N) - convolutionMain491 k N| +
        |convolutionMain491 k N - truncatedMain357 k N| := abs_sub_le _ _ _
    _ ≤ C * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) +
        B' * majorRelative376 k N := add_le_add (hClocal N hev hNC)
          (convolution_main_error491 k N B' hC)
    _ ≤ _ := by
      have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
      have hpow : 0 ≤ (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by positivity
      have ha := mul_le_mul_of_nonneg_right (le_max_left C B') hpow
      have hb := mul_le_mul_of_nonneg_right (le_max_right C B') hrel
      nlinarith

end LeanLab.Linnik1951
