module

public import LeanLab.HardyLittlewood1923.EulerR

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5903, paper P0004.

# Hardy-Littlewood 1923, the mean value of the binary singular series

The case r = 2 of the product `Br`: `Br 2 n = ∏_{p ∣ n, p odd} (p-1)/(p-2)`, and
`Cr 2 = ∏_{p ≥ 3} (1 - 1/(p-1)^2)` is the twin prime constant `C₂`.

* `Cr2_pos`: `Cr 2 > 0`, indeed `Cr 2 ≥ e^{-1}`.
* `mean_even_Br2`: `Σ_{n ≤ N, n even} n Br 2 n = N^2/(4 Cr 2) + o(N^2)`.

Proof: `Br 2 n = Σ_{d ∣ n, d squarefree} g(d)` with `g = gr 2`, `g(p) = 1/(p-2)` for odd `p`,
`g(2) = 0`. Swapping sums, the inner sum over even `n ≤ N` divisible by an odd `d` is the sum of
the multiples of `2d` up to `N`, which is `N^2/(4d)` up to `N/2`. The weight `F(d) = g(d)/d` is
multiplicative with `F(p) = 1/(p(p-2)) ≤ 2/(p-1)^2`, so the `√d` trick of `EulerE.tail_bound`,
run with the constant 2, gives both `Σ_{d ≤ N} g(d) ≤ e^{16} √N` and the truncation of
`Σ F(d)`. Prime by prime `(1 - 1/(p-1)^2)(1 + 1/(p(p-2))) = 1`, so the Euler product of `F` is
`1/Cr 2`. No cited input. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter Topology
open LeanLab.PNTPort.Vinogradov (dvd_primorial_of_sqf sum_tele_le)

/-! ### Generic tools with a constant `c` -/

theorem euler_absSqrt_le_c (F : ArithmeticFunction ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hp : ∀ p : ℕ, p.Prime → |F p| ≤ c / ((p : ℝ) - 1) ^ 2) (D : ℕ) :
    ∏ p ∈ Nat.primesLE D, (1 + absSqrt F p) ≤ Real.exp (8 * c) := by
  have h0 : ∀ p ∈ Nat.primesLE D, 0 ≤ 1 + absSqrt F p := fun p _ => by
    rw [absSqrt_apply]; positivity
  calc ∏ p ∈ Nat.primesLE D, (1 + absSqrt F p) ≤ ∏ p ∈ Nat.primesLE D, Real.exp (absSqrt F p) :=
        Finset.prod_le_prod₀ (h0 := h0) (h1 := fun p _ => by
          have := Real.add_one_le_exp (absSqrt F p); linarith)
    _ = Real.exp (∑ p ∈ Nat.primesLE D, absSqrt F p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (8 * c) := by
        apply Real.exp_le_exp.2
        calc ∑ p ∈ Nat.primesLE D, absSqrt F p
            ≤ ∑ p ∈ Nat.primesLE D, c * (Real.sqrt p / ((p : ℝ) - 1) ^ 2) := by
              refine sum_le_sum fun p hp' => ?_
              rw [Nat.mem_primesLE] at hp'
              rw [absSqrt_apply, mul_comm]
              have := hp p hp'.2
              have hs := Real.sqrt_nonneg (p : ℝ)
              calc Real.sqrt p * |F p| ≤ Real.sqrt p * (c / ((p : ℝ) - 1) ^ 2) :=
                    mul_le_mul_of_nonneg_left this hs
                _ = c * (Real.sqrt p / ((p : ℝ) - 1) ^ 2) := by ring
          _ = c * ∑ p ∈ Nat.primesLE D, Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by rw [mul_sum]
          _ ≤ c * ∑ m ∈ Icc 2 D, Real.sqrt m / ((m : ℝ) - 1) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ hc
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp'
                rw [Nat.mem_primesLE] at hp'
                rw [mem_Icc]; exact ⟨hp'.2.two_le, hp'.1⟩
              · intro _ _ _; positivity
          _ ≤ c * 8 := mul_le_mul_of_nonneg_left (sum_tele_le D) hc
          _ = 8 * c := by ring

/-- The partial sums of `absSqrt F` over squarefree `d ≤ N` are below the Euler product. -/
theorem sqf_sum_absSqrt_le (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative) (N : ℕ) :
    ∑ d ∈ (Icc 1 N).filter Squarefree, absSqrt F d ≤ ∏ p ∈ Nat.primesLE N, (1 + absSqrt F p) := by
  calc ∑ d ∈ (Icc 1 N).filter Squarefree, absSqrt F d
      ≤ ∑ d ∈ (primorial N).divisors, absSqrt F d := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter, mem_Icc] at hd
          exact Nat.mem_divisors.2 ⟨dvd_primorial_of_sqf hd.2 hd.1.2, (primorial_pos N).ne'⟩
        · intro d _ _; rw [absSqrt_apply]; positivity
    _ = ∏ p ∈ Nat.primesLE N, (1 + absSqrt F p) := by
        rw [← (absSqrt_mult hF).prodPrimeFactors_one_add_of_squarefree
          (squarefree_primorial N), primeFactors_primorial]

/-- The truncated squarefree divisor sum is the Euler product up to `e^{8c}/√D`. -/
theorem tail_bound_c (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative) (c : ℝ) (hc : 0 ≤ c)
    (hp : ∀ p : ℕ, p.Prime → |F p| ≤ c / ((p : ℝ) - 1) ^ 2) {D : ℕ} (hD : 1 ≤ D) :
    |∑ d ∈ (Icc 1 D).filter Squarefree, F d - ∏ p ∈ Nat.primesLE D, (1 + F p)| ≤
      Real.exp (8 * c) / Real.sqrt D := by
  have hPr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hsP : 0 < Real.sqrt D := Real.sqrt_pos.2 hPr
  have hset : (Icc 1 D).filter Squarefree = (primorial D).divisors.filter (fun d => d ≤ D) := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨dvd_primorial_of_sqf h3 h2, (primorial_pos D).ne'⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h1 (primorial_pos D), h3⟩,
        (squarefree_primorial D).squarefree_of_dvd h1⟩
  rw [hset]
  have hsplit : ∑ d ∈ (primorial D).divisors.filter (fun d => d ≤ D), F d +
      ∑ d ∈ (primorial D).divisors.filter (fun d => ¬ d ≤ D), F d =
      ∏ p ∈ Nat.primesLE D, (1 + F p) := by
    rw [sum_filter_add_sum_filter_not,
      ← hF.prodPrimeFactors_one_add_of_squarefree (squarefree_primorial D),
      primeFactors_primorial]
  have htail : |∑ d ∈ (primorial D).divisors.filter (fun d => ¬ d ≤ D), F d| ≤
      Real.exp (8 * c) / Real.sqrt D := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (primorial D).divisors.filter (fun d => ¬ d ≤ D), |F d|
        ≤ ∑ d ∈ (primorial D).divisors.filter (fun d => ¬ d ≤ D), absSqrt F d / Real.sqrt D := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter] at hd
          rw [absSqrt_apply, le_div_iff₀ hsP]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Real.sqrt_le_sqrt (by exact_mod_cast (not_le.1 hd.2).le)
      _ ≤ ∑ d ∈ (primorial D).divisors, absSqrt F d / Real.sqrt D := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _; rw [absSqrt_apply]; positivity
      _ = (∏ p ∈ Nat.primesLE D, (1 + absSqrt F p)) / Real.sqrt D := by
          rw [← sum_div, ← (absSqrt_mult hF).prodPrimeFactors_one_add_of_squarefree
            (squarefree_primorial D), primeFactors_primorial]
      _ ≤ Real.exp (8 * c) / Real.sqrt D :=
          div_le_div_of_nonneg_right (euler_absSqrt_le_c F c hc hp D) hsP.le
  rw [← hsplit]
  rw [show ∀ a b : ℝ, a - (a + b) = -b by intros; ring, abs_neg]
  exact htail

/-! ### Local quantities at r = 2 -/

/-- The value at a prime of `F(d) = g_2(d)/d`. -/
noncomputable def fp2 (p : ℕ) : ℝ := if p = 2 then 0 else 1 / ((p : ℝ) * ((p : ℝ) - 2))

/-- `F(d) = g_2(d)/d` on squarefree `d`, as a multiplicative function. -/
noncomputable def F2 : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors fp2

theorem F2_mult : F2.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem F2_prime {p : ℕ} (hp : p.Prime) : F2 p = fp2 p := by
  simp [F2, hp.ne_zero, hp.primeFactors]

theorem gvR2_odd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : gvR 2 p = 1 / ((p : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
  rw [gvR, if_neg h2]
  have a1 : ((p : ℝ) - 1) ^ 2 - (-1) ^ 2 ≠ 0 := by nlinarith
  have a2 : (p : ℝ) - 2 ≠ 0 := by intro h; linarith
  rw [div_eq_div_iff a1 a2]
  ring

theorem gvR2_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ gvR 2 p := by
  by_cases h2 : p = 2
  · simp [gvR, h2]
  · rw [gvR2_odd hp h2]
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
    apply div_nonneg zero_le_one; linarith

theorem fp2_eq {p : ℕ} (hp : p.Prime) : fp2 p = gvR 2 p / p := by
  by_cases h2 : p = 2
  · simp [fp2, gvR, h2]
  · rw [fp2, if_neg h2, gvR2_odd hp h2, div_div, mul_comm]

theorem fp2_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ fp2 p := by
  rw [fp2_eq hp]
  exact div_nonneg (gvR2_nonneg hp) (Nat.cast_nonneg _)

theorem fp2_le_ttR {p : ℕ} (hp : p.Prime) : fp2 p ≤ ttR p := by
  by_cases h2 : p = 2
  · simp [fp2, ttR, h2]
  · rw [fp2, if_neg h2, ttR_odd hp h2]
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith

theorem fp2_le {p : ℕ} (hp : p.Prime) : |fp2 p| ≤ 2 / ((p : ℝ) - 1) ^ 2 := by
  rw [abs_of_nonneg (fp2_nonneg hp)]
  by_cases h2 : p = 2
  · simp [fp2, h2]; norm_num
  · rw [fp2, if_neg h2]
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith

theorem frR2_mul {p : ℕ} (hp : p.Prime) : frR 2 p * (1 + fp2 p) = 1 := by
  by_cases h2 : p = 2
  · simp [frR, fp2, h2]
  · rw [frR, fp2, if_neg h2, if_neg h2]
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
    have a1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
    have a2 : (p : ℝ) - 2 ≠ 0 := by intro h; linarith
    have a3 : (p : ℝ) ≠ 0 := by intro h; linarith
    field_simp
    ring

theorem gr2_nonneg (d : ℕ) : 0 ≤ gr 2 d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rw [gr_apply 2 hd.ne']
  exact prod_nonneg fun p hp => gvR2_nonneg (Nat.prime_of_mem_primeFactors hp)

theorem gr2_even {d : ℕ} (hd : d ≠ 0) (he : Even d) : gr 2 d = 0 := by
  rw [gr_apply 2 hd]
  apply prod_eq_zero_iff.2
  refine ⟨2, Nat.mem_primeFactors.2 ⟨Nat.prime_two, even_iff_two_dvd.1 he, hd⟩, ?_⟩
  simp [gvR]

theorem F2_eq {d : ℕ} (hd : Squarefree d) : F2 d = gr 2 d / d := by
  have hd0 := hd.ne_zero
  rw [F2, ArithmeticFunction.prodPrimeFactors_apply hd0, gr_apply 2 hd0]
  have e : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [e, ← prod_div_distrib]
  exact prod_congr rfl fun p hp => fp2_eq (Nat.prime_of_mem_primeFactors hp)

theorem F2_nonneg (d : ℕ) : 0 ≤ F2 d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rw [F2, ArithmeticFunction.prodPrimeFactors_apply hd.ne']
  exact prod_nonneg fun p hp => fp2_nonneg (Nat.prime_of_mem_primeFactors hp)

/-! ### The constant `Cr 2` -/

theorem frR2_mult : Multipliable (fun p : {p : ℕ // p.Prime} => frR 2 p) := by
  have hsum : Summable (fun n : ℕ => 4 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 4
  have hs : Summable (fun p : {p : ℕ // p.Prime} =>
      if (p : ℕ) = 2 then (0 : ℝ) else -((-1 : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2)) := by
    refine Summable.of_norm_bounded (hsum.subtype (fun p : ℕ => p.Prime)) fun p => ?_
    have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    simp only [Function.comp_apply, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_zero]; positivity
    · rw [abs_neg, neg_one_sq, abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by nlinarith)]
      field_simp
      nlinarith
  refine (Real.multipliable_one_add_of_summable hs).congr fun p => ?_
  by_cases h : (p : ℕ) = 2
  · simp [frR, h]
  · simp [frR, h, sub_eq_add_neg]

theorem tendsto_frR2 :
    Tendsto (fun D => ∏ p ∈ Nat.primesLE D, frR 2 p) atTop (𝓝 (Cr 2)) := by
  rw [Cr_eq_tprod]; exact tendsto_primesLE_prod _ frR2_mult

theorem prod_one_add_fp2 (D : ℕ) :
    (∏ p ∈ Nat.primesLE D, frR 2 p) * ∏ p ∈ Nat.primesLE D, (1 + fp2 p) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun p hp => frR2_mul (Nat.mem_primesLE.1 hp).2

theorem prod_fp2_le (D : ℕ) : ∏ p ∈ Nat.primesLE D, (1 + fp2 p) ≤ Real.exp 1 := by
  calc ∏ p ∈ Nat.primesLE D, (1 + fp2 p) ≤ ∏ p ∈ Nat.primesLE D, Real.exp (ttR p) := by
        refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
        · have := fp2_nonneg (Nat.mem_primesLE.1 hp).2; linarith
        · have := fp2_le_ttR (Nat.mem_primesLE.1 hp).2
          have := Real.add_one_le_exp (ttR p)
          linarith
    _ = Real.exp (∑ p ∈ Nat.primesLE D, ttR p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.2
        have hsum := sum_ttR_le (Nat.primesLE D) (le_refl 2) (fun p hp h2 => by
          have := three_le_of_prime_ne_two (Nat.mem_primesLE.1 hp).2 h2
          omega)
        norm_num at hsum
        exact hsum

theorem frR2_prod_ge (D : ℕ) : Real.exp (-1) ≤ ∏ p ∈ Nat.primesLE D, frR 2 p := by
  have h1 := prod_one_add_fp2 D
  have h2 := prod_fp2_le D
  have h3 : 0 < ∏ p ∈ Nat.primesLE D, (1 + fp2 p) :=
    prod_pos fun p hp => by have := fp2_nonneg (Nat.mem_primesLE.1 hp).2; linarith
  have h4 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have h5 : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

theorem Cr2_ge : Real.exp (-1) ≤ Cr 2 := ge_of_tendsto' tendsto_frR2 frR2_prod_ge

theorem Cr2_pos : 0 < Cr 2 := lt_of_lt_of_le (Real.exp_pos _) Cr2_ge

/-! ### Sums of multiples -/

theorem sum_multiples (m N : ℕ) (hm : 0 < m) :
    |∑ n ∈ (Finset.range (N + 1)).filter (fun n => m ∣ n), (n : ℝ) - (N : ℝ) ^ 2 / (2 * m)| ≤
      (N : ℝ) / 2 := by
  set k := N / m with hk
  have hset : (Finset.range (N + 1)).filter (fun n => m ∣ n) =
      (Finset.range (k + 1)).map ⟨(m * ·), mul_right_injective₀ hm.ne'⟩ := by
    ext n
    simp only [mem_filter, mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      have : j ≤ k := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; omega)
      omega
    · rintro ⟨j, hj, rfl⟩
      have : j * m ≤ N := (Nat.le_div_iff_mul_le hm).1 (by omega)
      exact ⟨by rw [mul_comm]; omega, dvd_mul_right _ _⟩
  have hnat : 2 * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => m ∣ n), n = m * ((k + 1) * k) := by
    rw [hset, sum_map]
    simp only [Function.Embedding.coeFn_mk]
    rw [← mul_sum, mul_left_comm, mul_comm 2, Finset.sum_range_id_mul_two]
    simp
  have hreal : 2 * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => m ∣ n), (n : ℝ) =
      (m : ℝ) * (((k : ℝ) + 1) * k) := by
    rw [← Nat.cast_sum]; exact_mod_cast hnat
  set X := ∑ n ∈ (Finset.range (N + 1)).filter (fun n => m ∣ n), (n : ℝ)
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have a1 : (m : ℝ) * k ≤ N := by exact_mod_cast Nat.mul_div_le N m
  have a2 : (N : ℝ) + 1 ≤ m * (k + 1) := by exact_mod_cast Nat.lt_mul_div_succ N hm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set Y := (N : ℝ) ^ 2 / (2 * m)
  have hY : Y * (2 * m) = (N : ℝ) ^ 2 := by
    simp only [Y]; field_simp
  have hX : X * (2 * m) = (m * k) * (m * (k + 1)) := by nlinarith
  rw [abs_le]
  have b1 : (m * k) * (m * (k + 1)) ≤ (N : ℝ) * (N + m) := by
    have := mul_le_mul a1 (show (m : ℝ) * (k + 1) ≤ N + m by nlinarith) (by positivity) hN0
    linarith
  have b2 : (N : ℝ) * (N - m) ≤ (m * k) * (m * (k + 1)) := by
    by_cases hNm : (N : ℝ) ≤ m
    · have : (N : ℝ) * (N - m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 (by linarith)
      have : 0 ≤ (m * k) * ((m : ℝ) * (k + 1)) := by positivity
      linarith
    · have := mul_le_mul (show (N : ℝ) - m ≤ m * k by linarith) (show (N : ℝ) ≤ m * (k + 1) by linarith)
        hN0 (by positivity)
      linarith
  constructor
  · by_contra h
    replace h := not_le.1 h
    have := mul_lt_mul_of_pos_right h (show (0 : ℝ) < 2 * m by positivity)
    nlinarith
  · by_contra h
    replace h := not_le.1 h
    have := mul_lt_mul_of_pos_right h (show (0 : ℝ) < 2 * m by positivity)
    nlinarith

/-! ### The swap of summations -/

theorem swap_sum (N : ℕ) :
    ∑ n ∈ (Finset.range (N + 1)).filter Even, (n : ℝ) * Br 2 n =
      ∑ d ∈ (Icc 1 N).filter Squarefree,
        gr 2 d * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => 2 * d ∣ n), (n : ℝ) := by
  set E := (Finset.range (N + 1)).filter Even
  set Q := (Icc 1 N).filter Squarefree
  have h1 : ∀ n ∈ E, (n : ℝ) * Br 2 n = ∑ d ∈ Q, if d ∣ n then (n : ℝ) * gr 2 d else 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    rw [Br_eq_sum 2 n hn0 (by norm_num), mul_sum, ← sum_filter]
    have hnN : n ≤ N := by have := (mem_filter.1 hn).1; rw [mem_range] at this; omega
    have hs : Q.filter (fun d => d ∣ n) = n.divisors.filter Squarefree := by
      ext d
      simp only [Q, mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨_, _⟩, h3⟩, h4⟩; exact ⟨⟨h4, hn0.ne'⟩, h3⟩
      · rintro ⟨⟨h4, _⟩, h3⟩
        have := Nat.le_of_dvd hn0 h4
        have := Nat.pos_of_dvd_of_pos h4 hn0
        exact ⟨⟨⟨by omega, by omega⟩, h3⟩, h4⟩
    rw [hs]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (mem_filter.1 hd).2.ne_zero
  rw [← sum_filter, ← sum_mul, mul_comm]
  rcases Nat.even_or_odd d with he | ho
  · rw [gr2_even hd0 he, zero_mul, zero_mul]
  · congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [E, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.2 ho)
        (even_iff_two_dvd.1 h2) h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, even_iff_two_dvd.2 (dvd_trans (dvd_mul_right 2 d) h2)⟩,
        dvd_trans (dvd_mul_left d 2) h2⟩

/-- `Σ_{d ≤ N} g_2(d) ≤ e^{16} √N`. -/
theorem gr2_sum_le (N : ℕ) :
    ∑ d ∈ (Icc 1 N).filter Squarefree, gr 2 d ≤ Real.sqrt N * Real.exp 16 := by
  have hb : ∀ p : ℕ, p.Prime → |F2 p| ≤ 2 / ((p : ℝ) - 1) ^ 2 := fun p hp => by
    rw [F2_prime hp]; exact fp2_le hp
  have hE := (sqf_sum_absSqrt_le F2 F2_mult N).trans (euler_absSqrt_le_c F2 2 (by norm_num) hb N)
  rw [show (8 : ℝ) * 2 = 16 by norm_num] at hE
  calc ∑ d ∈ (Icc 1 N).filter Squarefree, gr 2 d
      ≤ ∑ d ∈ (Icc 1 N).filter Squarefree, Real.sqrt N * absSqrt F2 d := by
        refine sum_le_sum fun d hd => ?_
        rw [mem_filter, mem_Icc] at hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
        rw [absSqrt_apply, abs_of_nonneg (F2_nonneg d), F2_eq hd.2]
        have e : gr 2 d = (gr 2 d / d * Real.sqrt d) * Real.sqrt d := by
          rw [mul_assoc, Real.mul_self_sqrt hd0.le]; field_simp
        have h1 : Real.sqrt d ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hd.1.2)
        have h2 : 0 ≤ gr 2 d / d * Real.sqrt d := by
          have := gr2_nonneg d; positivity
        calc gr 2 d = (gr 2 d / d * Real.sqrt d) * Real.sqrt d := e
          _ ≤ (gr 2 d / d * Real.sqrt d) * Real.sqrt N := mul_le_mul_of_nonneg_left h1 h2
          _ = Real.sqrt N * (gr 2 d / d * Real.sqrt d) := mul_comm _ _
    _ = Real.sqrt N * ∑ d ∈ (Icc 1 N).filter Squarefree, absSqrt F2 d := by rw [mul_sum]
    _ ≤ Real.sqrt N * Real.exp 16 := mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _)

/-! ### Assembly -/

/-- The error term, divided by `N^2`. -/
noncomputable def errF (N : ℕ) : ℝ :=
  Real.exp 16 / Real.sqrt N + |1 / (∏ p ∈ Nat.primesLE N, frR 2 p) - 1 / Cr 2|

theorem tendsto_errF : Tendsto errF atTop (𝓝 0) := by
  have t1 : Tendsto (fun N : ℕ => Real.exp 16 / Real.sqrt N) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have t2 : Tendsto (fun N : ℕ => |1 / (∏ p ∈ Nat.primesLE N, frR 2 p) - 1 / Cr 2|) atTop
      (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).div tendsto_frR2 Cr2_pos.ne').sub_const
      (1 / Cr 2)
    rw [sub_self] at h
    have := h.abs
    rw [abs_zero] at this
    exact this
  have := t1.add t2
  rw [add_zero] at this
  exact this

theorem main_bound_F (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ (Finset.range (N + 1)).filter Even, (n : ℝ) * Br 2 n - (N : ℝ) ^ 2 / (4 * Cr 2)| ≤
      errF N * (N : ℝ) ^ 2 := by
  set Q := (Icc 1 N).filter Squarefree
  set T : ℕ → ℝ := fun d => ∑ n ∈ (Finset.range (N + 1)).filter (fun n => 2 * d ∣ n), (n : ℝ)
  set A := ∑ d ∈ Q, F2 d
  set P := ∏ p ∈ Nat.primesLE N, (1 + F2 p)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  rw [swap_sum]
  -- first error: the multiples
  have hA : ∑ d ∈ Q, gr 2 d * ((N : ℝ) ^ 2 / (2 * ((2 * d : ℕ) : ℝ))) = (N : ℝ) ^ 2 / 4 * A := by
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by
      have := (mem_filter.1 hd).1; rw [mem_Icc] at this; exact_mod_cast (show 0 < d by omega)
    rw [F2_eq (mem_filter.1 hd).2]
    push_cast
    field_simp
    ring
  have e1 : |∑ d ∈ Q, gr 2 d * T d - (N : ℝ) ^ 2 / 4 * A| ≤ (N : ℝ) / 2 * (Real.sqrt N * Real.exp 16) := by
    rw [← hA, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Q, |gr 2 d * T d - gr 2 d * ((N : ℝ) ^ 2 / (2 * ((2 * d : ℕ) : ℝ)))|
        ≤ ∑ d ∈ Q, gr 2 d * ((N : ℝ) / 2) := by
          refine sum_le_sum fun d hd => ?_
          have hd0 : 0 < d := by
            have := (mem_filter.1 hd).1; rw [mem_Icc] at this; omega
          rw [← mul_sub, abs_mul, abs_of_nonneg (gr2_nonneg d)]
          exact mul_le_mul_of_nonneg_left (sum_multiples (2 * d) N (by omega)) (gr2_nonneg d)
      _ = (N : ℝ) / 2 * ∑ d ∈ Q, gr 2 d := by rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ (N : ℝ) / 2 * (Real.sqrt N * Real.exp 16) :=
          mul_le_mul_of_nonneg_left (gr2_sum_le N) (by positivity)
  -- second error: truncation of the Euler product
  have hb : ∀ p : ℕ, p.Prime → |F2 p| ≤ 2 / ((p : ℝ) - 1) ^ 2 := fun p hp => by
    rw [F2_prime hp]; exact fp2_le hp
  have e2 : |A - P| ≤ Real.exp 16 / Real.sqrt N := by
    have := tail_bound_c F2 F2_mult 2 (by norm_num) hb hN
    rw [show (8 : ℝ) * 2 = 16 by norm_num] at this
    exact this
  have hP : P = 1 / ∏ p ∈ Nat.primesLE N, frR 2 p := by
    have h := prod_one_add_fp2 N
    have hP' : P = ∏ p ∈ Nat.primesLE N, (1 + fp2 p) :=
      prod_congr rfl fun p hp => by rw [F2_prime (Nat.mem_primesLE.1 hp).2]
    rw [hP', eq_div_iff (by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h), mul_comm, h]
  set δ := |1 / (∏ p ∈ Nat.primesLE N, frR 2 p) - 1 / Cr 2|
  have e3 : |A - 1 / Cr 2| ≤ Real.exp 16 / Real.sqrt N + δ := by
    have := abs_sub_le A P (1 / Cr 2)
    rw [hP] at this e2
    linarith
  have key : ∑ d ∈ Q, gr 2 d * T d - (N : ℝ) ^ 2 / (4 * Cr 2) =
      (∑ d ∈ Q, gr 2 d * T d - (N : ℝ) ^ 2 / 4 * A) + (N : ℝ) ^ 2 / 4 * (A - 1 / Cr 2) := by
    have := Cr2_pos.ne'
    field_simp
    ring
  rw [key]
  have e4 : |(N : ℝ) ^ 2 / 4 * (A - 1 / Cr 2)| ≤ (N : ℝ) ^ 2 / 4 * (Real.exp 16 / Real.sqrt N + δ) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  have e5 : (N : ℝ) / 2 * (Real.sqrt N * Real.exp 16) = (N : ℝ) ^ 2 / 2 * (Real.exp 16 / Real.sqrt N) := by
    set t := Real.sqrt (N : ℝ)
    have hN' : (N : ℝ) = t * t := hss.symm
    rw [hN']
    field_simp
  have hδ : 0 ≤ δ := abs_nonneg _
  have hq : 0 ≤ (N : ℝ) ^ 2 * (Real.exp 16 / Real.sqrt N) := by positivity
  have hq2 : 0 ≤ (N : ℝ) ^ 2 * δ := by positivity
  have herr : errF N * (N : ℝ) ^ 2 = (N : ℝ) ^ 2 * (Real.exp 16 / Real.sqrt N) + (N : ℝ) ^ 2 * δ := by
    simp only [errF, δ]; ring
  rw [herr]
  have tri := abs_add_le (∑ d ∈ Q, gr 2 d * T d - (N : ℝ) ^ 2 / 4 * A) ((N : ℝ) ^ 2 / 4 * (A - 1 / Cr 2))
  nlinarith

/-- The mean value of n · Br 2 n over even n. -/
theorem mean_even_Br2 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |∑ n ∈ (Finset.range (N + 1)).filter Even, (n : ℝ) * Br 2 n - (N : ℝ) ^ 2 / (4 * Cr 2)| ≤
      ε * (N : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (((tendsto_order.1 tendsto_errF).2 ε hε).and (eventually_ge_atTop 1))
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := hN₁ N hN
  exact (main_bound_F N h2).trans (mul_le_mul_of_nonneg_right h1.le (by positivity))

end LeanLab.HardyLittlewood1923

