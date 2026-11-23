module

public import LeanLab.Linnik1951.PrimeArcAbel491
public import LeanLab.Linnik1951.PrimeArcPowers491
public import LeanLab.Linnik1951.Base491b
public import LeanLab.Linnik1951.Decomp552b

/-!
P0093 pages 159 through 161. The truncated form of the mean square estimate on the
arc for the prime series against the model series S one, equations 6.1 and 6.3.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- The phase of the paper in the convention of the large sieve port. -/
private lemma phase_eq_partial491 (n : ℕ) (z : ℝ) :
    Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) =
      LeanLab.PNTPort.LargeSieve.e (n * (-z)) := by
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- Termwise decomposition of the coefficient: the von Mangoldt part, a correction
at zero and one, and the proper prime power part. -/
private lemma coeff_partial491 (N n : ℕ) :
    primeCoefficient552 N n - logCoefficient520 N n =
      ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) * LeanLab.PNTPort.Gallagher.lam1 n) +
        (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) -
        ((Real.exp (-(n / N : ℝ)) * (ArithmeticFunction.vonMangoldt n / Real.log n -
          (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) := by
  unfold primeCoefficient552 logCoefficient520 LeanLab.PNTPort.Gallagher.lam1
  simp only [neg_div]
  by_cases h2 : 2 ≤ n
  · have hm : max n 2 = n := max_eq_left h2
    have hlt : ¬ n < 2 := by omega
    rw [hm]
    by_cases hp : n.Prime
    · simp only [hp, h2, hlt, ↓reduceIte]
      push_cast
      ring
    · simp only [hp, h2, hlt, ↓reduceIte]
      push_cast
      ring
  · have hnp : ¬ n.Prime := fun hp => h2 hp.two_le
    have hlt : n < 2 := by omega
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n <;> simp
    simp only [hnp, h2, hlt, ↓reduceIte, hΛ]
    push_cast
    ring

/-- The correction at zero and one has size at most two. -/
private lemma corr_le_partial491 (N n : ℕ) :
    ‖(if n < 2 then
      (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0)‖ ≤
      (if n < 2 then (2 : ℝ) else 0) := by
  by_cases h : n < 2
  · have hm : max n 2 = 2 := max_eq_right h.le
    simp only [h, ↓reduceIte, hm]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    have hl' : 1 / Real.log ((2 : ℕ) : ℝ) ≤ 2 := by
      push_cast
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hl0 : 0 ≤ 1 / Real.log ((2 : ℕ) : ℝ) := by
      push_cast
      have : 0 < Real.log 2 := by linarith
      positivity
    have he : Real.exp (-((n : ℝ) / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (n : ℝ) / N := by positivity
      linarith
    rw [abs_of_nonneg (mul_nonneg hl0 (Real.exp_pos _).le)]
    nlinarith [Real.exp_pos (-((n : ℝ) / N))]
  · simp [h]

private lemma corr_sum_partial491 (M : ℕ) :
    ∑ n ∈ range M, (if n < 2 then (2 : ℝ) else 0) ≤ 4 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((range M).filter (fun n => n < 2)).card ≤ 2 := by
    calc ((range M).filter (fun n => n < 2)).card ≤ (range 2).card :=
          Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx
            exact Finset.mem_range.mpr hx.2)
      _ = 2 := Finset.card_range 2
  have : (((range M).filter (fun n => n < 2)).card : ℝ) ≤ 2 := by exact_mod_cast hc
  linarith

/-- Pointwise bound for the square of the truncated difference. -/
private lemma pointwise_partial491 (N M : ℕ) (P : ℝ)
    (hP : ∑ n ∈ range M, Real.exp (-(n / N : ℝ)) *
      (ArithmeticFunction.vonMangoldt n / Real.log n -
        (if n.Prime then (1 : ℝ) else 0)) ≤ P) (z : ℝ) :
    ‖∑ n ∈ range M, (primeCoefficient552 N n - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2 ≤
      3 * ‖∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * (-z))))‖ ^ 2 + (48 + 3 * P ^ 2) := by
  have hsplit : ∑ n ∈ range M, (primeCoefficient552 N n - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) =
      (∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * (-z))))) +
        (∑ n ∈ range M, (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))) -
        ∑ n ∈ range M, ((Real.exp (-(n / N : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.log n -
            (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [phase_eq_partial491, coeff_partial491]
    ring
  have hc : ‖∑ n ∈ range M, (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))‖ ≤ 4 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => ?_)).trans
      (corr_sum_partial491 M))
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one]
    exact corr_le_partial491 N n
  have hg : ‖∑ n ∈ range M, ((Real.exp (-(n / N : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.log n -
            (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))‖ ≤ P := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => ?_)).trans hP)
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (proper_power_weight_nonneg491 n))]
  rw [hsplit]
  set a := ∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * (-z))))
  set c := ∑ n ∈ range M, (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))
  set g := ∑ n ∈ range M, ((Real.exp (-(n / N : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.log n -
            (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))
  have h1 : ‖a + c - g‖ ≤ ‖a‖ + 4 + P :=
    (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (by linarith)) hg)
  have h2 : ‖a + c - g‖ ^ 2 ≤ (‖a‖ + 4 + P) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - 4), sq_nonneg (‖a‖ - P), sq_nonneg (P - 4)]

private lemma cont_A_partial491 (N M : ℕ) :
    Continuous (fun β : ℝ => ‖∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * β)))‖ ^ 2) := by
  simp only [LeanLab.PNTPort.LargeSieve.e]
  fun_prop

private lemma cont_D_partial491 (N M : ℕ) :
    Continuous (fun z : ℝ => ‖∑ n ∈ range M, (primeCoefficient552 N n - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) := by
  fun_prop

/-- Integration of a pointwise bound against a reflected majorant. -/
private lemma integral_abs_partial491 (D A : ℝ → ℝ) (hD : Continuous D) (hA : Continuous A)
    (K δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ z, D z ≤ 3 * A (-z) + K) :
    (∫ z in -δ..δ, D z) ≤ 3 * (∫ β in -δ..δ, A β) + 2 * δ * K := by
  have hA' : Continuous (fun z : ℝ => A (-z)) := hA.comp continuous_neg
  have hrefl : (∫ z in -δ..δ, A (-z)) = ∫ β in -δ..δ, A β := by
    have := intervalIntegral.integral_comp_neg (a := -δ) (b := δ) A
    simpa only [neg_neg] using this
  calc (∫ z in -δ..δ, D z) ≤ ∫ z in -δ..δ, (3 * A (-z) + K) :=
        intervalIntegral.integral_mono_on (by linarith) (hD.intervalIntegrable _ _)
          (((hA'.const_mul 3).add continuous_const).intervalIntegrable _ _) (fun z _ => h z)
    _ = 3 * (∫ β in -δ..δ, A β) + 2 * δ * K := by
        rw [intervalIntegral.integral_add ((hA'.const_mul 3).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          hrefl, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

/-- Widening a symmetric interval increases the integral of a nonnegative function. -/
private lemma widen_partial491 (A : ℝ → ℝ) (hA : Continuous A) (h0 : ∀ x, 0 ≤ A x)
    (δ δ' : ℝ) (hδ : 0 ≤ δ) (h : δ ≤ δ') :
    (∫ β in -δ..δ, A β) ≤ ∫ β in -δ'..δ', A β :=
  intervalIntegral.integral_mono_interval (by linarith) (by linarith) h
    (Filter.Eventually.of_forall h0) (hA.intervalIntegrable _ _)

/-- Scale facts on the arc: q tau is at least two and its square is at most N. -/
private lemma scale_partial491 (N q : ℕ) (hN : 128 < N) (hq : 1 ≤ q)
    (hqQ : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    2 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ∧ ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ N := by
  have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [he] at hh
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨by nlinarith, ?_⟩
  have h10 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h7 : (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hq4 : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hR : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    rw [this]
    exact mul_le_mul (hqQ.trans h10) h7 (by positivity) hq4.le
  have hsq : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [sq, ← Real.rpow_add hN0]; norm_num
  calc ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hR 2
    _ = N := hsq

/-- Real arithmetic collecting the three terms of the mean square bound, the
correction and the proper prime power part. -/
private lemma arith_partial491 (N R L ℓ lg s Ca Cp sN : ℝ) (hN : 1 ≤ N) (hR : 2 ≤ R)
    (hRN : R ^ 2 ≤ N) (hL4 : R ≤ 4 * L) (hL2 : 2 * L ≤ R) (hL1 : 1 ≤ L) (hℓ : 1 ≤ ℓ)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ ℓ) (hs : 1 ≤ s) (hCa : 0 ≤ Ca) (hsN : sN ^ 2 = N) :
    3 * (Ca * (N * (lg + 3) ^ 2 / L + N * ((ℓ + 2) ^ 2 / s) / L ^ 2 + L * (ℓ + 1) ^ 2)) +
        2 * (1 / R) * (48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2) ≤
      (306 * Ca + 96 + 24 * Cp ^ 2) * N / R * ℓ ^ 13 := by
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < N := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = N * ℓ ^ 2 / R := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : X * R = N * ℓ ^ 2 := by rw [hXdef]; field_simp
  have a2 : X * R ≤ X * (4 * L) := mul_le_mul_of_nonneg_left hL4 hX0
  have hT1 : N * (lg + 3) ^ 2 / L ≤ 64 * X := by
    rw [div_le_iff₀ hL0]
    have h : (lg + 3) ^ 2 ≤ 16 * ℓ ^ 2 := by nlinarith
    have a1 : N * (lg + 3) ^ 2 ≤ N * (16 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h hN0.le
    linarith
  have hT2 : N * ((ℓ + 2) ^ 2 / s) / L ^ 2 ≤ 36 * X := by
    have b0 : (ℓ + 2) ^ 2 / s ≤ 9 * ℓ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : (ℓ + 2) ^ 2 ≤ 9 * ℓ ^ 2 := by nlinarith
      have h2 : 9 * ℓ ^ 2 ≤ 9 * ℓ ^ 2 * s := le_mul_of_one_le_right (by positivity) hs
      linarith
    rw [div_le_iff₀ (by positivity)]
    have b1 : N * ((ℓ + 2) ^ 2 / s) ≤ N * (9 * ℓ ^ 2) := mul_le_mul_of_nonneg_left b0 hN0.le
    have b2 : L ≤ L ^ 2 := by nlinarith
    have b3 : X * L ≤ X * L ^ 2 := mul_le_mul_of_nonneg_left b2 hX0
    linarith
  have hT3 : L * (ℓ + 1) ^ 2 ≤ 2 * X := by
    have h : (ℓ + 1) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have c1 : L * (ℓ + 1) ^ 2 ≤ L * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h hL0.le
    have c2 : L * (4 * ℓ ^ 2) ≤ R / 2 * (4 * ℓ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have c3 : R * ℓ ^ 2 ≤ X := by
      rw [hXdef, le_div_iff₀ hR0]
      have : R ^ 2 * ℓ ^ 2 ≤ N * ℓ ^ 2 := mul_le_mul_of_nonneg_right hRN (by positivity)
      linarith
    linarith
  have hT4 : 2 * (1 / R) * (48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2) ≤ (96 + 24 * Cp ^ 2) * X := by
    have e1 : (Cp * sN * (ℓ + 1)) ^ 2 = Cp ^ 2 * (N * (ℓ + 1) ^ 2) := by rw [← hsN]; ring
    have h : (ℓ + 1) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have e2 : Cp ^ 2 * (N * (ℓ + 1) ^ 2) ≤ Cp ^ 2 * (N * (4 * ℓ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hN0.le) (sq_nonneg _)
    have e3 : 1 ≤ N * ℓ ^ 2 := by nlinarith
    have e4 : 48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2 ≤ (48 + 12 * Cp ^ 2) * (X * R) := by
      rw [hX, e1]
      linarith
    have e5 : 2 * (1 / R) * (48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2) ≤
        2 * (1 / R) * ((48 + 12 * Cp ^ 2) * (X * R)) :=
      mul_le_mul_of_nonneg_left e4 (by positivity)
    have e6 : 2 * (1 / R) * ((48 + 12 * Cp ^ 2) * (X * R)) = (96 + 24 * Cp ^ 2) * X := by
      field_simp
      ring
    linarith
  have hX13 : X ≤ N / R * ℓ ^ 13 := by
    rw [hXdef, show N * ℓ ^ 2 / R = N / R * ℓ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ (by norm_num)) (by positivity)
  have d1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hT1 hT2) hT3) hCa
  have d3 : (306 * Ca + 96 + 24 * Cp ^ 2) * X ≤
      (306 * Ca + 96 + 24 * Cp ^ 2) * (N / R * ℓ ^ 13) :=
    mul_le_mul_of_nonneg_left hX13 (by positivity)
  have d4 : (306 * Ca + 96 + 24 * Cp ^ 2) * N / R * ℓ ^ 13 =
      (306 * Ca + 96 + 24 * Cp ^ 2) * (N / R * ℓ ^ 13) := by ring
  rw [d4]
  linarith

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, on the arc, for
every truncation of the difference of the prime series and the model series S one.
Not a statement of the print; formalizer's route, see prime_arc_mean_square491.
Inputs: the mean square lam_log_mean_square491 of the von Mangoldt series with
weights one over ln n, which rests on the PNTPort.Selberg short interval mean
square under the Riemann hypothesis, in the conventions LargeSieve.e and
Gallagher.lam1 of PNTPort, and the proper prime power bound
proper_power_damped491. -/
theorem prime_arc_partial491 (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ M : ℕ,
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖∑ n ∈ range M, (primeCoefficient552 N n - logCoefficient520 N n) *
            Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤
          C * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
  obtain ⟨Ca, hCa, hA⟩ := lam_log_mean_square491 hRH
  obtain ⟨Cp, hCp, hPw⟩ := proper_power_damped491
  refine ⟨306 * Ca + 96 + 24 * Cp ^ 2, by positivity, 128, ?_⟩
  intro N hN q hq hqQ M
  obtain ⟨hR2, hRN⟩ := scale_partial491 N q hN hq hqQ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hRdef
  have hR0 : 0 < R := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌊R / 2⌋₊ := ⟨_, rfl⟩
  have hLle : (L : ℝ) ≤ R / 2 := by rw [hLdef]; exact Nat.floor_le (by linarith)
  have hLlt : R / 2 < L + 1 := by rw [hLdef]; exact Nat.lt_floor_add_one _
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Nat.le_floor (by push_cast; linarith)
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hLNr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hP := hPw N M (by omega)
  have h1 := integral_abs_partial491 _ _ (cont_D_partial491 N M) (cont_A_partial491 N M)
    (48 + 3 * (Cp * Real.sqrt N * (Real.log N + 1)) ^ 2) (1 / R) (by positivity)
    (pointwise_partial491 N M _ hP)
  have h2 := widen_partial491 _ (cont_A_partial491 N M) (fun x => by positivity)
    (1 / R) (1 / (2 * (L : ℝ))) (by positivity)
    (one_div_le_one_div_of_le (by linarith) (by linarith))
  have h3 := hA N L M hL1 hLN
  have h4 := arith_partial491 N R L (Real.log N) (Real.log (N / L)) (Real.sqrt L) Ca Cp
    (Real.sqrt N) hNr hR2 hRN (by linarith) (by linarith) hL1r hl
    (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    (Real.log_le_log (by positivity) (div_le_self (by linarith) hL1r))
    (Real.one_le_sqrt.mpr hL1r) hCa (Real.sq_sqrt (by linarith))
  linarith

end LeanLab.Linnik1951
