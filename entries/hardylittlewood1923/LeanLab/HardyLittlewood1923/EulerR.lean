module

public import LeanLab.HardyLittlewood1923.TheoremB34

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5901, paper P0004.

# Hardy-Littlewood 1923, the Euler-product side of Theorem B for general r ≥ 3

The r = 3 template is `EulerE`; here everything is done for every `r ≥ 3`.

* `gr r`: the multiplicative function with `g_r(p) = (-1)^r p/((p-1)^r - (-1)^r)` for odd `p`,
  `g_r(2) = 0`; sums are always restricted to squarefree `d`.
* `Br_eq_sum`: `Br r m = Σ_{d ∣ m, d squarefree} g_r(d)` for `m > 0` and `r ≥ 1`. For `r = 0`
  the identity fails, since every local factor of `Br 0` has the denominator `1 - 1 = 0`;
  see `Br_eq_sum_fails_r0`.
* `Cr_pos`, `Br_bounds`: `Cr r ≥ 3/4` and `e^{-2} ≤ Br r n ≤ e` for `r ≥ 3`.
* `gr_tail`, `gr_sum_bdd`: the tail of `Σ |g_r(d)|/φ(d)` beyond `D` is at most `e^8/√D`, and
  `Σ |g_r(d)| ≤ e`.
* `euler_avg_r`: uniformly in `n > 0`, `Σ_{d < D, d squarefree, (d,n) = 1} g_r(d)/φ(d)` tends
  to `Cr (r+1)/Cr r · Br (r+1) n`.

Proof: prime by prime, with `q = p - 1` and `s = (-1)^r`, for odd `p ∤ n`
`(1 - s/q^r)(1 + g_r(p)/q) = 1 + s/q^{r+1}`, and for odd `p ∣ n` the factor `1 - s/q^r` is the
`Cr (r+1)` factor times the `Br (r+1)` factor. The truncation uses the `√d` trick of
`EulerE.tail_bound`; the factors of `Br` lie in `[1/(1 + 2t_p), 1 + t_p]` with the telescoping
`t_p = 1/(p-2) - 1/(p-1)`. No cited input. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter Topology
open LeanLab.VanDerCorput1939 (summable_inv_sub_one_cube one_sub_sum_le_prod)
open LeanLab.PNTPort.Vinogradov (dvd_primorial_of_sqf)

/-- g_r, multiplicative, supported on odd squarefree d: g_r(p) = (-1)^r p/((p-1)^r - (-1)^r) for odd p, g_r(2) = 0. -/
noncomputable def gr (r : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors
    (fun p : ℕ => if p = 2 then 0 else (-1 : ℝ) ^ r * p / (((p : ℝ) - 1) ^ r - (-1) ^ r))

/-! ### Local quantities -/

/-- The value of `g_r` at a prime. -/
noncomputable def gvR (r p : ℕ) : ℝ :=
  if p = 2 then 0 else (-1 : ℝ) ^ r * p / (((p : ℝ) - 1) ^ r - (-1) ^ r)

/-- The local factor of `Br`. -/
noncomputable def bfacR (r p : ℕ) : ℝ :=
  (((p : ℝ) - 1) ^ r + (-1) ^ r * ((p : ℝ) - 1)) / (((p : ℝ) - 1) ^ r - (-1) ^ r)

/-- The telescoping majorant, zero at `2`. -/
noncomputable def ttR (p : ℕ) : ℝ := if p = 2 then 0 else 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)

/-- The local factor of `Cr`. -/
noncomputable def frR (r p : ℕ) : ℝ := if p = 2 then 1 else 1 - (-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r

theorem gr_mult (r : ℕ) : (gr r).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem gr_apply (r : ℕ) {d : ℕ} (hd : d ≠ 0) : gr r d = ∏ p ∈ d.primeFactors, gvR r p := by
  rw [gr, ArithmeticFunction.prodPrimeFactors_apply hd]; rfl

theorem gr_prime (r : ℕ) {p : ℕ} (hp : p.Prime) : gr r p = gvR r p := by
  rw [gr_apply r hp.ne_zero, hp.primeFactors, prod_singleton]

theorem two_le_q {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : (2 : ℝ) ≤ (p : ℝ) - 1 := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
  linarith

theorem neg_one_pow_bounds (r : ℕ) : -1 ≤ (-1 : ℝ) ^ r ∧ (-1 : ℝ) ^ r ≤ 1 := by
  rcases neg_one_pow_eq_or ℝ r with h | h <;> rw [h] <;> norm_num

theorem den_pos {r : ℕ} (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    0 < ((p : ℝ) - 1) ^ r - (-1) ^ r := by
  have hq := two_le_q hp h2
  have h1 : (p : ℝ) - 1 ≤ ((p : ℝ) - 1) ^ r := le_self_pow₀ (by linarith) (by omega)
  have := neg_one_pow_bounds r
  linarith

theorem tele_eq {p : ℕ} (h3 : (3 : ℝ) ≤ p) :
    1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
  have a1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  have a2 : (p : ℝ) - 2 ≠ 0 := by intro h; linarith
  field_simp; ring

theorem ttR_odd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ttR p = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
  rw [ttR, if_neg h2, tele_eq (by exact_mod_cast three_le_of_prime_ne_two hp h2)]

theorem ttR_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ ttR p := by
  by_cases h2 : p = 2
  · simp [ttR, h2]
  · rw [ttR_odd hp h2]
    have hq := two_le_q hp h2
    apply div_nonneg zero_le_one; apply mul_nonneg <;> linarith

theorem ttR_le_half {p : ℕ} (hp : p.Prime) : ttR p ≤ 1 / 2 := by
  by_cases h2 : p = 2
  · simp [ttR, h2]
  · rw [ttR_odd hp h2]
    have hq := two_le_q hp h2
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith

/-- Core estimate: `|s (q+1)/(X - s)| ≤ 1/((q-1) q)`. -/
theorem core_abs (q X s : ℝ) (hq : 2 ≤ q) (hX : q ^ 3 ≤ X) (hs : s = 1 ∨ s = -1) :
    |s * (q + 1) / (X - s)| ≤ 1 / ((q - 1) * q) := by
  have hs1 : |s| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hsb : s ≤ 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hq3 : 8 ≤ q ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hq 3; norm_num at this; linarith
  have hden : 0 < X - s := by linarith
  rw [abs_div, abs_mul, hs1, one_mul, abs_of_pos (by linarith : 0 < q + 1), abs_of_pos hden]
  rw [div_le_div_iff₀ hden (by nlinarith)]
  have e : (q + 1) * ((q - 1) * q) = q ^ 3 - q := by ring
  rw [e]
  linarith

theorem abs_gvR_le (r : ℕ) (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) : |gvR r p| ≤ ttR p := by
  by_cases h2 : p = 2
  · simp [gvR, ttR, h2]
  have hq := two_le_q hp h2
  have hX : ((p : ℝ) - 1) ^ 3 ≤ ((p : ℝ) - 1) ^ r := pow_le_pow_right₀ (by linarith) hr
  rw [ttR_odd hp h2, gvR, if_neg h2]
  have e2 : (p : ℝ) - 2 = ((p : ℝ) - 1) - 1 := by ring
  have e3 : (-1 : ℝ) ^ r * p = (-1) ^ r * (((p : ℝ) - 1) + 1) := by ring
  rw [e2, e3]
  exact core_abs _ _ _ hq hX (neg_one_pow_eq_or ℝ r)

theorem bfacR_eq (r : ℕ) (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    bfacR r p = 1 + gvR r p := by
  have hden := den_pos hr hp h2
  rw [bfacR, gvR, if_neg h2, one_add_div hden.ne']
  congr 1; ring

/-- A factor `x` with `|x - 1| ≤ t ≤ 1/2`. -/
theorem factor_ok (x t : ℝ) (h : |x - 1| ≤ t) (ht : t ≤ 1 / 2) :
    0 < x ∧ 0 ≤ t ∧ x ≤ 1 + t ∧ 1 ≤ x * (1 + 2 * t) := by
  have ht0 : 0 ≤ t := (abs_nonneg _).trans h
  rw [abs_le] at h
  refine ⟨by linarith, ht0, by linarith, ?_⟩
  have h1 : (1 - t) * (1 + 2 * t) ≤ x * (1 + 2 * t) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

theorem bfacR_ok (r : ℕ) (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    0 < bfacR r p ∧ 0 ≤ ttR p ∧ bfacR r p ≤ 1 + ttR p ∧ 1 ≤ bfacR r p * (1 + 2 * ttR p) := by
  apply factor_ok _ _ _ (ttR_le_half hp)
  rw [bfacR_eq r (by omega) hp h2, add_sub_cancel_left]
  exact abs_gvR_le r hr hp

/-- Products of factors in `[1/(1 + 2t), 1 + t]`. -/
theorem prod_bounds_of_factor {S : Finset ℕ} (x t : ℕ → ℝ)
    (h : ∀ i ∈ S, 0 < x i ∧ 0 ≤ t i ∧ x i ≤ 1 + t i ∧ 1 ≤ x i * (1 + 2 * t i)) :
    Real.exp (-(2 * ∑ i ∈ S, t i)) ≤ ∏ i ∈ S, x i ∧ ∏ i ∈ S, x i ≤ Real.exp (∑ i ∈ S, t i) := by
  have hP0 : 0 ≤ ∏ i ∈ S, x i := prod_nonneg fun i hi => (h i hi).1.le
  have hup : ∏ i ∈ S, x i ≤ Real.exp (∑ i ∈ S, t i) := by
    rw [Real.exp_sum]
    refine prod_le_prod₀ (fun i hi => (h i hi).1.le) fun i hi => ?_
    have := Real.add_one_le_exp (t i)
    linarith [(h i hi).2.2.1]
  refine ⟨?_, hup⟩
  have hPQ : 1 ≤ (∏ i ∈ S, x i) * ∏ i ∈ S, (1 + 2 * t i) := by
    rw [← prod_mul_distrib]
    exact one_le_prod₀ fun i hi => (h i hi).2.2.2
  have hQ : ∏ i ∈ S, (1 + 2 * t i) ≤ Real.exp (2 * ∑ i ∈ S, t i) := by
    rw [mul_sum, Real.exp_sum]
    refine prod_le_prod₀ (fun i hi => by linarith [(h i hi).2.1]) fun i hi => ?_
    have := Real.add_one_le_exp (2 * t i)
    linarith
  have h1 : 1 ≤ (∏ i ∈ S, x i) * Real.exp (2 * ∑ i ∈ S, t i) :=
    hPQ.trans (mul_le_mul_of_nonneg_left hQ hP0)
  have h2 : Real.exp (-(2 * ∑ i ∈ S, t i)) * Real.exp (2 * ∑ i ∈ S, t i) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(2 * ∑ i ∈ S, t i))
      = Real.exp (-(2 * ∑ i ∈ S, t i)) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-(2 * ∑ i ∈ S, t i)) * ((∏ i ∈ S, x i) * Real.exp (2 * ∑ i ∈ S, t i)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = ∏ i ∈ S, x i := by rw [mul_comm, mul_assoc, mul_comm (Real.exp _), h2, mul_one]

theorem sum_ttR_le (S : Finset ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (hS : ∀ p ∈ S, p ≠ 2 → Q + 1 ≤ p) :
    ∑ p ∈ S, ttR p ≤ 1 / ((Q : ℝ) - 1) := by
  rw [← sum_filter_add_sum_filter_not S (fun p => p ≠ 2)]
  have h0 : ∑ p ∈ S.filter (fun p => ¬ p ≠ 2), ttR p = 0 := by
    refine sum_eq_zero fun p hp => ?_
    rw [mem_filter, not_not] at hp
    simp [ttR, hp.2]
  rw [h0, add_zero]
  have e : ∑ p ∈ S.filter (fun p => p ≠ 2), ttR p =
      ∑ p ∈ S.filter (fun p => p ≠ 2), (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) := by
    refine sum_congr rfl fun p hp => ?_
    rw [mem_filter] at hp
    rw [ttR, if_neg hp.2]
  rw [e]
  apply tele_set_le _ hQ
  intro p hp
  rw [mem_filter] at hp
  exact hS p hp.1 hp.2

/-! ### The divisor sum and the bounds for `Br` -/

theorem Br_eq_sum' (r m : ℕ) (hm : 0 < m) (hr : 1 ≤ r) :
    Br r m = ∑ d ∈ m.divisors.filter Squarefree, gr r d := by
  rw [sum_sqf_divisors_eq_prod (gr r) (gr_mult r) hm.ne']
  unfold Br
  have key : ∏ p ∈ m.primeFactors, (1 + gr r p) =
      ∏ p ∈ m.primeFactors.filter (· ≠ 2), (1 + gr r p) := by
    refine (prod_filter_of_ne ?_).symm
    intro p hp hne h2
    apply hne
    rw [h2, gr_prime r Nat.prime_two]
    simp [gvR]
  rw [key]
  · refine prod_congr rfl fun p hp => ?_
    rw [mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    rw [gr_prime r hpp, ← bfacR_eq r hr hpp hp.2]
    rfl

theorem Br_le_ge (r : ℕ) (hr : 3 ≤ r) (n : ℕ) :
    Real.exp (-2) ≤ Br r n ∧ Br r n ≤ Real.exp 1 := by
  have hS : ∀ p ∈ n.primeFactors.filter (· ≠ 2),
      0 < bfacR r p ∧ 0 ≤ ttR p ∧ bfacR r p ≤ 1 + ttR p ∧ 1 ≤ bfacR r p * (1 + 2 * ttR p) := by
    intro p hp
    rw [mem_filter] at hp
    exact bfacR_ok r hr (Nat.prime_of_mem_primeFactors hp.1) hp.2
  obtain ⟨h1, h2⟩ := prod_bounds_of_factor _ _ hS
  have hsum : ∑ p ∈ n.primeFactors.filter (· ≠ 2), ttR p ≤ 1 := by
    have := sum_ttR_le (n.primeFactors.filter (· ≠ 2)) (le_refl 2) (fun p hp h2 => by
      rw [mem_filter] at hp
      have := three_le_of_prime_ne_two (Nat.prime_of_mem_primeFactors hp.1) h2
      omega)
    norm_num at this
    exact this
  have eB : Br r n = ∏ p ∈ n.primeFactors.filter (· ≠ 2), bfacR r p := rfl
  rw [eB]
  constructor
  · exact (Real.exp_le_exp.2 (by linarith)).trans h1
  · exact h2.trans (Real.exp_le_exp.2 hsum)

/-! ### The constant `Cr` -/

theorem Cr_eq_tprod (r : ℕ) : Cr r = ∏' p : {p : ℕ // p.Prime}, frR r p := by
  unfold Cr
  refine tprod_congr fun p => ?_
  by_cases h : (p : ℕ) = 2
  · have : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h
    simp [frR, h, this]
  · have : p ≠ ⟨2, Nat.prime_two⟩ := fun e => h (by rw [e])
    simp [frR, h, this]

theorem abs_sgn_div_le (r : ℕ) (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    |(-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r| ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
  have hq := two_le_q hp h2
  have hX : ((p : ℝ) - 1) ^ 3 ≤ ((p : ℝ) - 1) ^ r := pow_le_pow_right₀ (by linarith) hr
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (pow_pos (by linarith) r)]
  exact one_div_le_one_div_of_le (pow_pos (by linarith) 3) hX

theorem frR_mult (r : ℕ) (hr : 3 ≤ r) : Multipliable (fun p : {p : ℕ // p.Prime} => frR r p) := by
  have hs : Summable (fun p : {p : ℕ // p.Prime} =>
      if (p : ℕ) = 2 then (0 : ℝ) else -((-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r)) := by
    refine Summable.of_norm_bounded (summable_inv_sub_one_cube.subtype (fun p : ℕ => p.Prime))
      fun p => ?_
    have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    simp only [Function.comp_apply, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_zero]; apply div_nonneg zero_le_one; apply pow_nonneg; linarith
    · rw [abs_neg]; exact abs_sgn_div_le r hr p.2 h
  refine (Real.multipliable_one_add_of_summable hs).congr fun p => ?_
  by_cases h : (p : ℕ) = 2
  · simp [frR, h]
  · simp [frR, h, sub_eq_add_neg]

theorem tendsto_frR (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun D => ∏ p ∈ Nat.primesLE D, frR r p) atTop (𝓝 (Cr r)) := by
  rw [Cr_eq_tprod]; exact tendsto_primesLE_prod _ (frR_mult r hr)

/-- The partial products of `Cr r` are at least `3/4`. -/
theorem frR_prod_ge (r : ℕ) (hr : 3 ≤ r) (D : ℕ) : (3 : ℝ) / 4 ≤ ∏ p ∈ Nat.primesLE D, frR r p := by
  set v : ℕ → ℝ := fun p => if p = 2 then 0 else 1 / ((p : ℝ) - 1) ^ 3 with hv
  have hv01 : ∀ p ∈ Nat.primesLE D, 0 ≤ v p ∧ v p ≤ 1 := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    by_cases h : p = 2
    · simp [hv, h]
    · have hq := two_le_q hpp h
      simp only [hv, if_neg h]
      constructor
      · apply div_nonneg zero_le_one; apply pow_nonneg; linarith
      · rw [div_le_one (pow_pos (by linarith) 3)]
        exact one_le_pow₀ (by linarith)
  have hle : ∀ p ∈ Nat.primesLE D, 1 - v p ≤ frR r p := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    by_cases h : p = 2
    · simp [hv, frR, h]
    · simp only [hv, frR, if_neg h]
      have := abs_sgn_div_le r hr hpp h
      have := le_abs_self ((-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r)
      linarith
  have hprod : ∏ p ∈ Nat.primesLE D, (1 - v p) ≤ ∏ p ∈ Nat.primesLE D, frR r p :=
    prod_le_prod₀ (fun p hp => by linarith [(hv01 p hp).2]) hle
  refine le_trans ?_ (le_trans (one_sub_sum_le_prod _ v hv01) hprod)
  have hsum : ∑ p ∈ Nat.primesLE D, v p ≤ 1 / 4 := by
    calc ∑ p ∈ Nat.primesLE D, v p ≤ ∑ p ∈ Nat.primesLE D, (1 / 4) * ttR p := by
          refine sum_le_sum fun p hp => ?_
          have hpp := (Nat.mem_primesLE.1 hp).2
          by_cases h : p = 2
          · simp [hv, ttR, h]
          · simp only [hv, if_neg h]
            rw [ttR_odd hpp h, one_div_mul_one_div]
            have hq := two_le_q hpp h
            apply one_div_le_one_div_of_le
              (by apply mul_pos (by norm_num); apply mul_pos <;> linarith)
            set y : ℝ := (p : ℝ) - 1 with hy
            have hx : (p : ℝ) - 2 = y - 1 := by rw [hy]; ring
            rw [hx]
            have h4 : 0 ≤ y * (y - 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
            nlinarith
      _ = (1 / 4) * ∑ p ∈ Nat.primesLE D, ttR p := by rw [mul_sum]
      _ ≤ (1 / 4) * (1 / ((2 : ℕ) - 1 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply sum_ttR_le _ le_rfl
          intro p hp h2
          have := three_le_of_prime_ne_two (Nat.mem_primesLE.1 hp).2 h2
          omega
      _ = 1 / 4 := by norm_num
  linarith

theorem Cr_ge (r : ℕ) (hr : 3 ≤ r) : (3 : ℝ) / 4 ≤ Cr r :=
  ge_of_tendsto' (tendsto_frR r hr) (frR_prod_ge r hr)


/-! ### The weight `g_r(d)/φ(d)` on squarefree `d` coprime to `n` -/

/-- The value at a prime `p` of `d ↦ 1_{(d,n)=1} g_r(d)/φ(d)`. -/
noncomputable def phiR (r n p : ℕ) : ℝ := if p ∣ n then 0 else gvR r p / ((p : ℝ) - 1)

/-- The multiplicative function `d ↦ ∏_{p ∣ d} phiR r n p`. -/
noncomputable def HR (r n : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (phiR r n)

theorem HR_mult (r n : ℕ) : (HR r n).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem HR_prime (r n : ℕ) {p : ℕ} (hp : p.Prime) : HR r n p = phiR r n p := by
  simp [HR, hp.ne_zero, hp.primeFactors]

theorem phiR_bound (r : ℕ) (hr : 3 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    |phiR r n p| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hnn : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
    apply div_nonneg zero_le_one; apply pow_nonneg; linarith
  unfold phiR
  split_ifs with h
  · rw [abs_zero]; exact hnn
  by_cases h2 : p = 2
  · simp [gvR, h2]
  have hq := two_le_q hp h2
  have hg := abs_gvR_le r hr hp
  rw [ttR_odd hp h2] at hg
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
  calc |gvR r p| / ((p : ℝ) - 1) ≤ 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) / ((p : ℝ) - 1) :=
        div_le_div_of_nonneg_right hg (by linarith)
    _ ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
        rw [div_div]
        apply one_div_le_one_div_of_le (pow_pos (by linarith) 2)
        have : (1 : ℝ) ≤ (p : ℝ) - 2 := by linarith
        have hq0 : (0 : ℝ) ≤ ((p : ℝ) - 1) * ((p : ℝ) - 1) := mul_self_nonneg _
        nlinarith

theorem HR_eq (r n : ℕ) {d : ℕ} (hd : Squarefree d) :
    HR r n d = if Nat.Coprime d n then gr r d / (d.totient : ℝ) else 0 := by
  have hd0 := hd.ne_zero
  rw [HR, ArithmeticFunction.prodPrimeFactors_apply hd0]
  split_ifs with h
  · rw [totient_sqf hd, gr_apply r hd0, ← prod_div_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hn : ¬ p ∣ n :=
      (Nat.Prime.coprime_iff_not_dvd hpp).1 (Nat.Coprime.coprime_dvd_left hpd h)
    rw [phiR, if_neg hn]
  · apply prod_eq_zero_iff.2
    obtain ⟨p, hp, hpd, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
    exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpd, hd0⟩, by simp [phiR, hpn]⟩

theorem sum_eq_sum_HR (r n D : ℕ) :
    ∑ d ∈ (Finset.range (D + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
      gr r d / (Nat.totient d : ℝ) = ∑ d ∈ (Icc 1 D).filter Squarefree, HR r n d := by
  have hs : (Finset.range (D + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n) =
      ((Icc 1 D).filter Squarefree).filter (fun d => Nat.Coprime d n) := by
    ext d
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have := h2.ne_zero
      exact ⟨⟨⟨by omega, by omega⟩, h2⟩, h3⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨by omega, h3, h4⟩
  rw [hs, sum_filter]
  refine sum_congr rfl fun d hd => ?_
  rw [HR_eq r n (mem_filter.1 hd).2]

/-! ### The local identity -/

/-- The local factor of `Br (r+1) n` at `p`, and `1` off the odd divisors of `n`. -/
noncomputable def rrR (r n p : ℕ) : ℝ := if p ≠ 2 ∧ p ∣ n then bfacR (r + 1) p else 1

theorem core_A (P X s t : ℝ) (hq : P - 1 ≠ 0) (hX : X ≠ 0) (h1 : X * (P - 1) - t ≠ 0)
    (ht : t = -s) :
    1 - s / X = (1 - t / (X * (P - 1))) * ((X * (P - 1) + t * (P - 1)) / (X * (P - 1) - t)) := by
  subst ht
  field_simp
  ring

theorem core_B (P X s t : ℝ) (hq : P - 1 ≠ 0) (hX : X ≠ 0) (hXs : X - s ≠ 0) (ht : t = -s) :
    (1 - s / X) * (1 + s * P / (X - s) / (P - 1)) = 1 - t / (X * (P - 1)) := by
  subst ht
  field_simp
  ring

theorem local_identity_r (r : ℕ) (hr : 3 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    frR r p * (1 + phiR r n p) = frR (r + 1) p * rrR r n p := by
  by_cases h2 : p = 2
  · subst h2; simp [frR, rrR, phiR, gvR]
  have hq := two_le_q hp h2
  have hden := den_pos (by omega : 1 ≤ r) hp h2
  have hqr : 0 < ((p : ℝ) - 1) ^ r := pow_pos (by linarith) r
  have ht : (-1 : ℝ) ^ (r + 1) = -(-1) ^ r := by rw [pow_succ]; ring
  have hX : ((p : ℝ) - 1) ^ (r + 1) = ((p : ℝ) - 1) ^ r * ((p : ℝ) - 1) := pow_succ _ _
  have hs := neg_one_pow_bounds r
  have hbig : 0 < ((p : ℝ) - 1) ^ r * ((p : ℝ) - 1) - (-1) ^ (r + 1) := by
    rw [ht]
    have hX1 : 1 ≤ ((p : ℝ) - 1) ^ r := one_le_pow₀ (by linarith)
    have : (p : ℝ) - 1 ≤ ((p : ℝ) - 1) ^ r * ((p : ℝ) - 1) := by nlinarith
    linarith
  by_cases hn : p ∣ n
  · rw [show phiR r n p = 0 by simp [phiR, hn], show rrR r n p = bfacR (r + 1) p by
      simp [rrR, hn, h2], add_zero, mul_one]
    simp only [frR, if_neg h2, bfacR]
    rw [hX]
    exact core_A _ _ _ _ (by linarith) hqr.ne' hbig.ne' ht
  · rw [show phiR r n p = gvR r p / ((p : ℝ) - 1) by simp [phiR, hn],
      show rrR r n p = 1 by simp [rrR, hn], mul_one]
    simp only [frR, gvR, if_neg h2]
    rw [hX]
    exact core_B _ _ _ _ (by linarith) hqr.ne' hden.ne' ht

theorem rrR_ok (r : ℕ) (hr : 3 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    0 < rrR r n p ∧ 0 ≤ ttR p ∧ rrR r n p ≤ 1 + ttR p ∧ 1 ≤ rrR r n p * (1 + 2 * ttR p) := by
  have ht0 := ttR_nonneg hp
  unfold rrR
  split_ifs with h
  · exact bfacR_ok (r + 1) (by omega) hp h.1
  · refine ⟨one_pos, ht0, by linarith, by linarith⟩

/-- `Br (r+1) n` as a product of `rrR r n p` over the primes `p ≤ M`, `M ≥ n > 0`. -/
theorem Br_eq_prod (r n M : ℕ) (hn : 0 < n) (hM : n ≤ M) :
    Br (r + 1) n = ∏ p ∈ Nat.primesLE M, rrR r n p := by
  unfold Br
  have hsub : n.primeFactors.filter (fun p => p ≠ 2) ⊆ Nat.primesLE M := by
    intro p hp
    rw [mem_filter, Nat.mem_primeFactors] at hp
    exact Nat.mem_primesLE.2 ⟨(Nat.le_of_dvd hn hp.1.2.1).trans hM, hp.1.1⟩
  rw [← prod_subset hsub]
  · refine prod_congr rfl fun p hp => ?_
    rw [mem_filter] at hp
    rw [rrR, if_pos ⟨hp.2, Nat.dvd_of_mem_primeFactors hp.1⟩]
    rfl
  · intro p hp hpn
    rw [rrR, if_neg]
    rintro ⟨h2, hd⟩
    exact hpn (mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨(Nat.mem_primesLE.1 hp).2, hd, hn.ne'⟩, h2⟩)

/-- Splitting `Br (r+1) n` at `D`. -/
theorem Br_split (r : ℕ) (hr : 3 ≤ r) (n D : ℕ) (hn : 0 < n) (hD : 2 ≤ D) :
    ∃ T : ℝ, Br (r + 1) n = (∏ p ∈ Nat.primesLE D, rrR r n p) * T ∧
      Real.exp (-(2 * (1 / ((D : ℝ) - 1)))) ≤ T ∧ T ≤ Real.exp (1 / ((D : ℝ) - 1)) := by
  set M := max n D
  have hS : (Nat.primesLE M).filter (fun p => p ≤ D) = Nat.primesLE D := by
    ext p; simp only [mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨⟨h'.trans (le_max_right _ _), h⟩, h'⟩
  refine ⟨∏ p ∈ (Nat.primesLE M).filter (fun p => ¬ p ≤ D), rrR r n p, ?_, ?_⟩
  · rw [Br_eq_prod r n M hn (le_max_left _ _), ← hS, prod_filter_mul_prod_filter_not]
  · have hb : ∀ p ∈ (Nat.primesLE M).filter (fun p => ¬ p ≤ D),
        0 < rrR r n p ∧ 0 ≤ ttR p ∧ rrR r n p ≤ 1 + ttR p ∧
          1 ≤ rrR r n p * (1 + 2 * ttR p) := by
      intro p hp
      rw [mem_filter, Nat.mem_primesLE] at hp
      exact rrR_ok r hr n hp.1.2
    obtain ⟨h1, h2⟩ := prod_bounds_of_factor _ _ hb
    have hsum := sum_ttR_le ((Nat.primesLE M).filter (fun p => ¬ p ≤ D)) hD (fun p hp _ => by
      rw [mem_filter] at hp; omega)
    refine ⟨le_trans (Real.exp_le_exp.2 (by linarith)) h1, h2.trans (Real.exp_le_exp.2 hsum)⟩

theorem rrR_prod_bounds (r : ℕ) (hr : 3 ≤ r) (n D : ℕ) :
    0 ≤ ∏ p ∈ Nat.primesLE D, rrR r n p ∧ ∏ p ∈ Nat.primesLE D, rrR r n p ≤ Real.exp 1 := by
  have hb : ∀ p ∈ Nat.primesLE D,
      0 < rrR r n p ∧ 0 ≤ ttR p ∧ rrR r n p ≤ 1 + ttR p ∧ 1 ≤ rrR r n p * (1 + 2 * ttR p) :=
    fun p hp => rrR_ok r hr n (Nat.mem_primesLE.1 hp).2
  obtain ⟨_, h2⟩ := prod_bounds_of_factor _ _ hb
  have hsum := sum_ttR_le (Nat.primesLE D) (le_refl 2) (fun p hp h2 => by
    have := three_le_of_prime_ne_two (Nat.mem_primesLE.1 hp).2 h2
    omega)
  norm_num at hsum
  exact ⟨prod_nonneg fun p hp => (hb p hp).1.le, h2.trans (Real.exp_le_exp.2 hsum)⟩

/-! ### Assembly -/

/-- The error term of the uniform approximation. -/
noncomputable def errR (r D : ℕ) : ℝ :=
  Real.exp 8 / Real.sqrt D +
    Real.exp 1 * |(∏ p ∈ Nat.primesLE D, frR (r + 1) p) / (∏ p ∈ Nat.primesLE D, frR r p) -
      Cr (r + 1) / Cr r| +
    Real.exp 1 * (Cr (r + 1) / Cr r) * (Real.exp (2 * (1 / ((D : ℝ) - 1))) - 1)

theorem main_bound_r (r : ℕ) (hr : 3 ≤ r) (n D : ℕ) (hn : 0 < n) (hD : 2 ≤ D) :
    |∑ d ∈ (Icc 1 D).filter Squarefree, HR r n d - Cr (r + 1) / Cr r * Br (r + 1) n| ≤
      errR r D := by
  set S := ∑ d ∈ (Icc 1 D).filter Squarefree, HR r n d with hS
  set E := ∏ p ∈ Nat.primesLE D, (1 + phiR r n p) with hE
  set A := ∏ p ∈ Nat.primesLE D, frR r p with hA
  set B := ∏ p ∈ Nat.primesLE D, frR (r + 1) p with hB
  set R := ∏ p ∈ Nat.primesLE D, rrR r n p with hR
  set C := Cr r with hC
  set C' := Cr (r + 1) with hC'
  have hSE : |S - E| ≤ Real.exp 8 / Real.sqrt D := by
    have h := tail_bound (HR r n) (HR_mult r n)
      (fun p hp => by rw [HR_prime r n hp]; exact phiR_bound r hr n hp) (by omega : 1 ≤ D)
    have e : ∏ p ∈ Nat.primesLE D, (1 + HR r n p) = E :=
      prod_congr rfl fun p hp => by rw [HR_prime r n (Nat.mem_primesLE.1 hp).2]
    rwa [e] at h
  have hAE : A * E = B * R := by
    rw [hA, hE, hB, hR, ← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun p hp => local_identity_r r hr n (Nat.mem_primesLE.1 hp).2
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) (frR_prod_ge r hr D)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) (Cr_ge r hr)
  have hC'0 : 0 < C' := lt_of_lt_of_le (by norm_num) (Cr_ge (r + 1) (by omega))
  have hEq : E = B * R / A := by
    rw [eq_div_iff hA0.ne', mul_comm, hAE]
  obtain ⟨T, hT, hT1, hT2⟩ := Br_split r hr n D hn hD
  obtain ⟨hR0, hRe⟩ := rrR_prod_bounds r hr n D
  set x : ℝ := 1 / ((D : ℝ) - 1) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; apply div_nonneg zero_le_one
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hT3 : |1 - T| ≤ Real.exp (2 * x) - 1 := by
    rw [abs_le]
    have e1 := Real.add_one_le_exp (-(2 * x))
    have e2 := Real.add_one_le_exp (2 * x)
    have e3 : Real.exp x ≤ Real.exp (2 * x) := Real.exp_le_exp.2 (by linarith)
    constructor <;> linarith
  have key : S - C' / C * Br (r + 1) n =
      (S - E) + R * ((B / A - C' / C) + C' / C * (1 - T)) := by
    rw [hT, hEq]; ring
  rw [key]
  have hCC : 0 ≤ C' / C := (div_pos hC'0 hC0).le
  have b2 : |R * ((B / A - C' / C) + C' / C * (1 - T))| ≤
      Real.exp 1 * |B / A - C' / C| + Real.exp 1 * (C' / C) * (Real.exp (2 * x) - 1) := by
    rw [abs_mul, abs_of_nonneg hR0]
    have h1 : |(B / A - C' / C) + C' / C * (1 - T)| ≤
        |B / A - C' / C| + C' / C * (Real.exp (2 * x) - 1) := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_nonneg hCC]
      exact mul_le_mul_of_nonneg_left hT3 hCC
    calc R * |(B / A - C' / C) + C' / C * (1 - T)|
        ≤ Real.exp 1 * (|B / A - C' / C| + C' / C * (Real.exp (2 * x) - 1)) :=
          mul_le_mul hRe h1 (abs_nonneg _) (Real.exp_pos 1).le
      _ = _ := by ring
  have herr : errR r D = Real.exp 8 / Real.sqrt D + Real.exp 1 * |B / A - C' / C| +
      Real.exp 1 * (C' / C) * (Real.exp (2 * x) - 1) := rfl
  rw [herr]
  have tri := abs_add_le (S - E) (R * ((B / A - C' / C) + C' / C * (1 - T)))
  linarith

theorem tendsto_errR (r : ℕ) (hr : 3 ≤ r) : Tendsto (errR r) atTop (𝓝 0) := by
  have hC0 : 0 < Cr r := lt_of_lt_of_le (by norm_num) (Cr_ge r hr)
  have t1 : Tendsto (fun D : ℕ => Real.exp 8 / Real.sqrt D) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have t2 : Tendsto (fun D : ℕ => Real.exp 1 *
      |(∏ p ∈ Nat.primesLE D, frR (r + 1) p) / (∏ p ∈ Nat.primesLE D, frR r p) -
        Cr (r + 1) / Cr r|) atTop (𝓝 (Real.exp 1 * 0)) := by
    have h := ((tendsto_frR (r + 1) (by omega)).div (tendsto_frR r hr) hC0.ne').sub_const
      (Cr (r + 1) / Cr r)
    rw [sub_self] at h
    have := h.abs
    rw [abs_zero] at this
    exact this.const_mul _
  have t3 : Tendsto (fun D : ℕ => Real.exp 1 * (Cr (r + 1) / Cr r) *
      (Real.exp (2 * (1 / ((D : ℝ) - 1))) - 1)) atTop
      (𝓝 (Real.exp 1 * (Cr (r + 1) / Cr r) * 0)) := by
    have h0 : Tendsto (fun D : ℕ => 1 / ((D : ℝ) - 1)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun x : ℝ => Real.exp (2 * x) - 1) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun x : ℝ => Real.exp (2 * x) - 1) := by fun_prop
      have := hcont.tendsto (0 : ℝ)
      simpa using this
    exact (hc.comp h0).const_mul _
  have := (t1.add t2).add t3
  rw [show (0 : ℝ) + Real.exp 1 * 0 + Real.exp 1 * (Cr (r + 1) / Cr r) * 0 = 0 by ring] at this
  exact this

/-! ### The listed statements -/

/-- Divisor expansion of `Br`. False for `r = 0`, see `Br_eq_sum_fails_r0`, hence `1 ≤ r`. -/
theorem Br_eq_sum (r m : ℕ) (hm : 0 < m) (hr : 1 ≤ r) :
    Br r m = ∑ d ∈ m.divisors.filter Squarefree, gr r d :=
  Br_eq_sum' r m hm hr

theorem Cr_pos (r : ℕ) (hr : 3 ≤ r) : 0 < Cr r :=
  lt_of_lt_of_le (by norm_num) (Cr_ge r hr)

theorem Br_bounds (r : ℕ) (hr : 3 ≤ r) : ∃ c K : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ Br r n ∧ Br r n ≤ K :=
  ⟨Real.exp (-2), Real.exp 1, Real.exp_pos _, Br_le_ge r hr⟩

/-- The tail of `Σ |F d|` over squarefree `d ∈ (D, N]`, by the `√d` trick. -/
theorem sqrt_tail (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative)
    (hp : ∀ p : ℕ, p.Prime → |F p| ≤ 1 / ((p : ℝ) - 1) ^ 2) (D N : ℕ) (hD : 1 ≤ D) :
    ∑ d ∈ (Finset.Ioc D N).filter Squarefree, |F d| ≤ Real.exp 8 / Real.sqrt D := by
  have hPr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hsP : 0 < Real.sqrt D := Real.sqrt_pos.2 hPr
  calc ∑ d ∈ (Finset.Ioc D N).filter Squarefree, |F d|
      ≤ ∑ d ∈ (Finset.Ioc D N).filter Squarefree, absSqrt F d / Real.sqrt D := by
        refine sum_le_sum fun d hd => ?_
        rw [mem_filter, mem_Ioc] at hd
        rw [absSqrt_apply, le_div_iff₀ hsP]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact Real.sqrt_le_sqrt (by exact_mod_cast hd.1.1.le)
    _ ≤ ∑ d ∈ (primorial N).divisors, absSqrt F d / Real.sqrt D := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter, mem_Ioc] at hd
          exact Nat.mem_divisors.2 ⟨dvd_primorial_of_sqf hd.2 hd.1.2, (primorial_pos N).ne'⟩
        · intro d _ _; rw [absSqrt_apply]; positivity
    _ = (∏ p ∈ Nat.primesLE N, (1 + absSqrt F p)) / Real.sqrt D := by
        rw [← sum_div, ← (absSqrt_mult hF).prodPrimeFactors_one_add_of_squarefree
          (squarefree_primorial N), primeFactors_primorial]
    _ ≤ Real.exp 8 / Real.sqrt D :=
        div_le_div_of_nonneg_right (euler_absSqrt_le F hp N) hsP.le

/-- Uniform tail of Σ |g_r(d)|/φ(d) and boundedness of Σ |g_r(d)|. -/
theorem gr_tail (r : ℕ) (hr : 3 ≤ r) : ∃ K : ℝ, ∀ D N : ℕ, 1 ≤ D →
    ∑ d ∈ (Finset.Ioc D N).filter Squarefree, |gr r d| / (Nat.totient d : ℝ) ≤ K / Real.sqrt D := by
  refine ⟨Real.exp 8, fun D N hD => ?_⟩
  refine le_trans (le_of_eq ?_) (sqrt_tail (HR r 1) (HR_mult r 1)
    (fun p hp => by rw [HR_prime r 1 hp]; exact phiR_bound r hr 1 hp) D N hD)
  refine sum_congr rfl fun d hd => ?_
  rw [HR_eq r 1 (mem_filter.1 hd).2, if_pos (Nat.coprime_one_right d), abs_div, Nat.abs_cast]

/-- `|g_r|` on squarefree numbers, as a multiplicative function. -/
noncomputable def GaR (r : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => |gvR r p|)

theorem gr_sum_bdd (r : ℕ) (hr : 3 ≤ r) : ∃ K : ℝ, ∀ N : ℕ,
    ∑ d ∈ (Finset.range N).filter Squarefree, |gr r d| ≤ K := by
  refine ⟨Real.exp 1, fun N => ?_⟩
  have hGm : (GaR r).IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hGp : ∀ p : ℕ, p.Prime → GaR r p = |gvR r p| := fun p hp => by
    simp [GaR, hp.ne_zero, hp.primeFactors]
  calc ∑ d ∈ (Finset.range N).filter Squarefree, |gr r d|
      = ∑ d ∈ (Finset.range N).filter Squarefree, GaR r d := by
        refine sum_congr rfl fun d hd => ?_
        have hd0 := (mem_filter.1 hd).2.ne_zero
        rw [gr_apply r hd0, abs_prod, GaR, ArithmeticFunction.prodPrimeFactors_apply hd0]
    _ ≤ ∑ d ∈ (primorial N).divisors, GaR r d := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter, mem_range] at hd
          exact Nat.mem_divisors.2 ⟨dvd_primorial_of_sqf hd.2 hd.1.le, (primorial_pos N).ne'⟩
        · intro d hd _
          have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
          rw [GaR, ArithmeticFunction.prodPrimeFactors_apply hd0]
          exact prod_nonneg fun _ _ => abs_nonneg _
    _ = ∏ p ∈ Nat.primesLE N, (1 + GaR r p) := by
        rw [← hGm.prodPrimeFactors_one_add_of_squarefree (squarefree_primorial N),
          primeFactors_primorial]
    _ ≤ ∏ p ∈ Nat.primesLE N, Real.exp (ttR p) := by
        refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
        · rw [hGp p (Nat.mem_primesLE.1 hp).2]; positivity
        · rw [hGp p (Nat.mem_primesLE.1 hp).2]
          have := abs_gvR_le r hr (Nat.mem_primesLE.1 hp).2
          have := Real.add_one_le_exp (ttR p)
          linarith
    _ = Real.exp (∑ p ∈ Nat.primesLE N, ttR p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.2
        have hsum := sum_ttR_le (Nat.primesLE N) (le_refl 2) (fun p hp h2 => by
          have := three_le_of_prime_ne_two (Nat.mem_primesLE.1 hp).2 h2
          omega)
        norm_num at hsum
        exact hsum

/-- The Euler product identity, uniformly in n. -/
theorem euler_avg_r (r : ℕ) (hr : 3 ≤ r) : ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, ∀ D n : ℕ, D₀ ≤ D → 0 < n →
    |∑ d ∈ (Finset.range D).filter (fun d => Squarefree d ∧ Nat.Coprime d n), gr r d / (Nat.totient d : ℝ)
      - Cr (r + 1) / Cr r * Br (r + 1) n| ≤ ε := by
  intro ε hε
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.1
    (((tendsto_order.1 (tendsto_errR r hr)).2 ε hε).and (eventually_ge_atTop 2))
  refine ⟨D₁ + 1, fun D n hD hn => ?_⟩
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  obtain ⟨h1, h2⟩ := hD₁ D' (by omega)
  rw [sum_eq_sum_HR]
  exact (main_bound_r r hr n D' hn h2).trans h1.le

/-- `Br_eq_sum` fails for `r = 0`: the local factor of `Br 0` at `3` has denominator `0`. -/
theorem Br_eq_sum_fails_r0 :
    Br 0 3 ≠ ∑ d ∈ (3 : ℕ).divisors.filter Squarefree, gr 0 d := by
  rw [sum_sqf_divisors_eq_prod (gr 0) (gr_mult 0) (by norm_num), Nat.prime_three.primeFactors,
    prod_singleton, gr_prime 0 Nat.prime_three]
  simp [Br, gvR, Nat.prime_three.primeFactors]

end LeanLab.HardyLittlewood1923

