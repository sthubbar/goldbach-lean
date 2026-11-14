module

public import LeanLab.HardyLittlewood1923.TheoremEStatements

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5707, paper P0004.

# Hardy-Littlewood 1923, Theorem E: the Euler-product side of the average of the singular series

* `Pi3_eq_sum`: for odd `m`, `Pi3 m = Σ_{d ∣ m, d squarefree} g d`.
* `abs_g_le`: `|g d| ≤ 1/d` for odd squarefree `d`.
* `euler_avg_tendsto`: uniformly in even `n > 0`,
  `C₃ Σ_{d ≤ D, d odd squarefree, (d, n) = 1} g(d)/φ(d) → C₄ Pi4 n` as `D → ∞`.
* `C4_pos`, `one_le_Pi4`.

Proof: the truncated divisor sum is the finite Euler product over `p ≤ D` up to `e⁸/√D`
(the `√d` trick of `PNTPort.Vinogradov.SingPos`), and prime by prime
`(1 + 1/(p-1)³)(1 + g(p)/(p-1)) = 1 - 1/(p-1)⁴` for odd `p ∤ n`, while for odd `p ∣ n`
`1 + 1/(p-1)³ = (1 - 1/(p-1)⁴)(p-1)(p²-3p+3)/((p-2)(p²-2p+2))`. Tails are bounded by
telescoping sums. No cited input. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter Topology
open LeanLab.VanDerCorput1939 (summable_inv_sub_one_cube tele_sum one_le_K one_sub_sum_le_prod)
open LeanLab.PNTPort.Vinogradov (dvd_primorial_of_sqf sum_tele_le)

/-! ### Generic tools -/

theorem three_le_of_odd_prime {l : ℕ} (hp : l.Prime) (ho : Odd l) : 3 ≤ l := by
  rcases ho with ⟨k, hk⟩; have := hp.two_le; omega

theorem three_le_of_prime_ne_two {l : ℕ} (hp : l.Prime) (h2 : l ≠ 2) : 3 ≤ l :=
  three_le_of_odd_prime hp (hp.odd_of_ne_two h2)

/-- Divisor sum over squarefree divisors of a multiplicative function. -/
theorem sum_sqf_divisors_eq_prod (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative) {m : ℕ}
    (hm : m ≠ 0) :
    ∑ d ∈ m.divisors.filter Squarefree, F d = ∏ p ∈ m.primeFactors, (1 + F p) := by
  rw [Nat.sum_divisors_filter_squarefree hm, prod_one_add]
  have e : (UniqueFactorizationMonoid.normalizedFactors m).toFinset = m.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [e]
  refine sum_congr rfl fun t ht => ?_
  rw [mem_powerset] at ht
  have : t.val.prod = ∏ a ∈ t, a := by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  rw [this, hF.map_prod_of_subset_primeFactors m t ht]

/-- `φ(d) = ∏_{p ∣ d} (p - 1)` for squarefree `d`. -/
theorem totient_sqf {d : ℕ} (hd : Squarefree d) :
    (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have h2 : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
    rw [mul_comm] at h; exact Nat.eq_of_mul_eq_mul_left hd0 h
  rw [h2, Nat.cast_prod]
  refine prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp

/-- Sum of telescoping terms over a set of integers beyond `Q`. -/
theorem tele_set_le (S : Finset ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (hS : ∀ p ∈ S, Q + 1 ≤ p) :
    ∑ p ∈ S, (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) ≤ 1 / ((Q : ℝ) - 1) := by
  set M := ∑ p ∈ S, p + Q with hM
  calc ∑ p ∈ S, (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1))
      ≤ ∑ m ∈ Icc (Q + 1) M, (1 / ((m : ℝ) - 2) - 1 / ((m : ℝ) - 1)) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have h1 := hS p hp
          have h2 : p ≤ ∑ p ∈ S, p := single_le_sum (f := fun p => p) (fun _ _ => Nat.zero_le _) hp
          rw [mem_Icc]; constructor <;> omega
        · intro m hm _
          rw [mem_Icc] at hm
          have : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
          have h1 : 0 < (m : ℝ) - 2 := by linarith
          rw [sub_nonneg]
          apply one_div_le_one_div_of_le h1; linarith
    _ = 1 / ((Q : ℝ) - 1) - 1 / ((M : ℝ) - 1) := tele_sum Q M (by omega)
    _ ≤ 1 / ((Q : ℝ) - 1) := by
        have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 2 ≤ M)
        have : 0 ≤ 1 / ((M : ℝ) - 1) := by apply div_nonneg zero_le_one; linarith
        linarith

/-- Products of factors in `[1, 1 + t]`. -/
theorem prod_le_exp_sum {S : Finset ℕ} (f t : ℕ → ℝ) (h : ∀ i ∈ S, 1 ≤ f i ∧ f i ≤ 1 + t i) :
    1 ≤ ∏ i ∈ S, f i ∧ ∏ i ∈ S, f i ≤ Real.exp (∑ i ∈ S, t i) := by
  constructor
  · exact one_le_prod₀ fun i hi => (h i hi).1
  · rw [Real.exp_sum]
    refine prod_le_prod₀ (fun i hi => by linarith [(h i hi).1]) fun i hi => ?_
    have := Real.add_one_le_exp (t i)
    linarith [(h i hi).2]

/-! ### `Pi3` and `g` -/

/-- `g` as a multiplicative arithmetic function. -/
noncomputable def G : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun l : ℕ => -1 / ((l : ℝ) ^ 2 - 3 * l + 3))

/-- Divisor expansion: for odd m ≥ 1, Pi3 m = Σ over squarefree divisors d of m of g d. -/
theorem Pi3_eq_sum (m : ℕ) (hm : Odd m) :
    Pi3 m = ∑ d ∈ m.divisors.filter Squarefree, g d := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hG : G.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have h1 : ∑ d ∈ m.divisors.filter Squarefree, g d =
      ∑ d ∈ m.divisors.filter Squarefree, G d := by
    refine sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (mem_filter.1 hd).1)
    simp [G, g, ArithmeticFunction.prodPrimeFactors_apply hd0]
  rw [h1, sum_sqf_divisors_eq_prod G hG hm0]
  unfold Pi3
  refine prod_congr rfl fun p hp => ?_
  have hp := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : (p : ℝ) ^ 2 - 3 * p + 3 ≠ 0 := by nlinarith
  rw [show G p = -1 / ((p : ℝ) ^ 2 - 3 * p + 3) by
    simp [G, hp.ne_zero, hp.primeFactors]]
  rw [div_eq_iff hd, add_mul, div_mul_cancel₀ _ hd]
  ring

/-- |g d| ≤ 1/d for squarefree odd d (each factor: l² - 3l + 3 ≥ l for l ≥ 3). -/
theorem abs_g_le (d : ℕ) (hd : Squarefree d) (hodd : Odd d) : |g d| ≤ 1 / (d : ℝ) := by
  unfold g
  rw [abs_prod]
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  push_cast
  rw [one_div, ← prod_inv_distrib]
  refine prod_le_prod₀ (fun l _ => abs_nonneg _) fun l hl => ?_
  have hl' := Nat.prime_of_mem_primeFactors hl
  have hl3 : (3 : ℝ) ≤ l := by
    exact_mod_cast three_le_of_odd_prime hl' (Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hl))
  rw [abs_div, abs_neg, abs_one, abs_of_pos (by nlinarith), inv_eq_one_div]
  apply one_div_le_one_div_of_le (by linarith)
  nlinarith

/-! ### The tail of a divisor sum, after `SingPos` -/

/-- `d ↦ |F d| √d`. -/
noncomputable def absSqrt (F : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => |F d| * Real.sqrt d, by simp⟩

theorem absSqrt_apply (F : ArithmeticFunction ℝ) (d : ℕ) : absSqrt F d = |F d| * Real.sqrt d :=
  rfl

theorem absSqrt_mult {F : ArithmeticFunction ℝ} (hF : F.IsMultiplicative) :
    (absSqrt F).IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · show |F 1| * Real.sqrt ((1 : ℕ) : ℝ) = 1
    rw [hF.map_one]; simp
  · show |F (a * b)| * Real.sqrt ((a * b : ℕ) : ℝ) =
      (|F a| * Real.sqrt (a : ℝ)) * (|F b| * Real.sqrt (b : ℝ))
    rw [hF.map_mul_of_coprime hab, abs_mul]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg a)]
    ring

theorem euler_absSqrt_le (F : ArithmeticFunction ℝ)
    (hp : ∀ p : ℕ, p.Prime → |F p| ≤ 1 / ((p : ℝ) - 1) ^ 2) (D : ℕ) :
    ∏ p ∈ Nat.primesLE D, (1 + absSqrt F p) ≤ Real.exp 8 := by
  have h0 : ∀ p ∈ Nat.primesLE D, 0 ≤ 1 + absSqrt F p := fun p _ => by
    rw [absSqrt_apply]; positivity
  calc ∏ p ∈ Nat.primesLE D, (1 + absSqrt F p) ≤ ∏ p ∈ Nat.primesLE D, Real.exp (absSqrt F p) :=
        Finset.prod_le_prod₀ (h0 := h0) (h1 := fun p _ => by
          have := Real.add_one_le_exp (absSqrt F p); linarith)
    _ = Real.exp (∑ p ∈ Nat.primesLE D, absSqrt F p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 8 := by
        apply Real.exp_le_exp.2
        calc ∑ p ∈ Nat.primesLE D, absSqrt F p
            ≤ ∑ p ∈ Nat.primesLE D, Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by
              refine sum_le_sum fun p hp' => ?_
              rw [Nat.mem_primesLE] at hp'
              rw [absSqrt_apply, mul_comm]
              have := hp p hp'.2
              have hs := Real.sqrt_nonneg (p : ℝ)
              calc Real.sqrt p * |F p| ≤ Real.sqrt p * (1 / ((p : ℝ) - 1) ^ 2) :=
                    mul_le_mul_of_nonneg_left this hs
                _ = Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by ring
          _ ≤ ∑ m ∈ Icc 2 D, Real.sqrt m / ((m : ℝ) - 1) ^ 2 := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp'
                rw [Nat.mem_primesLE] at hp'
                rw [mem_Icc]; exact ⟨hp'.2.two_le, hp'.1⟩
              · intro _ _ _; positivity
          _ ≤ 8 := sum_tele_le D

/-- The truncated squarefree divisor sum is the Euler product up to `e⁸/√D`. -/
theorem tail_bound (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative)
    (hp : ∀ p : ℕ, p.Prime → |F p| ≤ 1 / ((p : ℝ) - 1) ^ 2) {D : ℕ} (hD : 1 ≤ D) :
    |∑ d ∈ (Icc 1 D).filter Squarefree, F d - ∏ p ∈ Nat.primesLE D, (1 + F p)| ≤
      Real.exp 8 / Real.sqrt D := by
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
      Real.exp 8 / Real.sqrt D := by
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
      _ ≤ Real.exp 8 / Real.sqrt D :=
          div_le_div_of_nonneg_right (euler_absSqrt_le F hp D) hsP.le
  rw [← hsplit]
  rw [show ∀ a b : ℝ, a - (a + b) = -b by intros; ring, abs_neg]
  exact htail

/-! ### The weight `g(d)/φ(d)` on odd squarefree `d` coprime to `n` -/

/-- The value at a prime `p` of `d ↦ 1_{d odd, (d,n)=1} g(d)/φ(d)`. -/
noncomputable def phi0 (n p : ℕ) : ℝ :=
  if p ≠ 2 ∧ ¬ p ∣ n then -1 / (((p : ℝ) ^ 2 - 3 * p + 3) * ((p : ℝ) - 1)) else 0

/-- The multiplicative function `d ↦ ∏_{p ∣ d} phi0 n p`. -/
noncomputable def H (n : ℕ) : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (phi0 n)

theorem H_mult (n : ℕ) : (H n).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem H_prime (n : ℕ) {p : ℕ} (hp : p.Prime) : H n p = phi0 n p := by
  simp [H, hp.ne_zero, hp.primeFactors]

theorem phi0_bounds (n : ℕ) {p : ℕ} (hp : p.Prime) :
    |phi0 n p| ≤ 1 / ((p : ℝ) - 1) ^ 2 ∧ phi0 n p ≤ 0 := by
  unfold phi0
  split_ifs with h
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h.1
    have hA : (p : ℝ) - 1 ≤ (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
    have hpos : 0 < ((p : ℝ) ^ 2 - 3 * p + 3) * ((p : ℝ) - 1) := by
      apply mul_pos <;> nlinarith
    constructor
    · rw [abs_div, abs_neg, abs_one, abs_of_pos hpos]
      apply one_div_le_one_div_of_le (by nlinarith)
      calc ((p : ℝ) - 1) ^ 2 = ((p : ℝ) - 1) * ((p : ℝ) - 1) := sq _
        _ ≤ ((p : ℝ) ^ 2 - 3 * p + 3) * ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hA (by linarith)
    · rw [neg_div]; have := one_div_pos.2 hpos; linarith
  · simp only [abs_zero, le_refl, and_true]; positivity

theorem H_eq (n : ℕ) {d : ℕ} (hd : Squarefree d) :
    H n d = if Odd d ∧ Nat.Coprime d n then g d / (d.totient : ℝ) else 0 := by
  have hd0 := hd.ne_zero
  rw [H, ArithmeticFunction.prodPrimeFactors_apply hd0]
  split_ifs with h
  · rw [totient_sqf hd, g, ← prod_div_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl; exact (Nat.not_even_iff_odd.2 h.1) (even_iff_two_dvd.2 hpd)
    have hn : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd hpp).1 (Nat.Coprime.coprime_dvd_left hpd h.2)
    rw [phi0, if_pos ⟨h2, hn⟩, div_div]
  · apply prod_eq_zero_iff.2
    by_cases ho : Odd d
    · have hc : ¬ Nat.Coprime d n := fun hc => h ⟨ho, hc⟩
      obtain ⟨p, hp, hpd, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
      refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpd, hd0⟩, ?_⟩
      simp [phi0, hpn]
    · have h2 : 2 ∣ d := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 ho)
      refine ⟨2, Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2, hd0⟩, ?_⟩
      simp [phi0]

theorem sum_eq_sum_H (n D : ℕ) :
    ∑ d ∈ (Icc 1 D).filter (fun d => Squarefree d ∧ Odd d ∧ Nat.Coprime d n),
      g d / (Nat.totient d : ℝ) = ∑ d ∈ (Icc 1 D).filter Squarefree, H n d := by
  rw [sum_filter, sum_filter]
  refine sum_congr rfl fun d _ => ?_
  by_cases hs : Squarefree d
  · rw [H_eq n hs]
    by_cases ho : Odd d ∧ Nat.Coprime d n
    · simp [hs, ho]
    · simp [hs, ho]
  · simp [hs]

/-! ### The Euler products -/

noncomputable def f3 (p : ℕ) : ℝ := if p = 2 then 1 else 1 + 1 / ((p : ℝ) - 1) ^ 3
noncomputable def f4 (p : ℕ) : ℝ := if p = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 4
noncomputable def rr (n p : ℕ) : ℝ :=
  if p ≠ 2 ∧ p ∣ n then
    ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 3 * p + 3) / (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2))
  else 1

theorem local_identity (n : ℕ) {p : ℕ} (hp : p.Prime) :
    f3 p * (1 + phi0 n p) = f4 p * rr n p := by
  by_cases h2 : p = 2
  · subst h2; simp [f3, f4, rr, phi0]
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
  have a1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  have a2 : (p : ℝ) - 2 ≠ 0 := by intro h; linarith
  have a3 : (p : ℝ) ^ 2 - 3 * p + 3 ≠ 0 := by nlinarith
  have a4 : (p : ℝ) ^ 2 - 2 * p + 2 ≠ 0 := by nlinarith
  have e3 : f3 p = 1 + 1 / ((p : ℝ) - 1) ^ 3 := by simp [f3, h2]
  have e4 : f4 p = 1 - 1 / ((p : ℝ) - 1) ^ 4 := by simp [f4, h2]
  rw [e3, e4]
  by_cases hn : p ∣ n
  · have e5 : phi0 n p = 0 := by simp [phi0, hn]
    have e6 : rr n p = ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 3 * p + 3) /
        (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2)) := by simp [rr, h2, hn]
    rw [e5, e6, add_zero, mul_one]
    have l1 : 1 + 1 / ((p : ℝ) - 1) ^ 3 = (p : ℝ) * ((p : ℝ) ^ 2 - 3 * p + 3) / ((p : ℝ) - 1) ^ 3 := by
      rw [one_add_div (pow_ne_zero 3 a1)]; congr 1; ring
    have l2 : 1 - 1 / ((p : ℝ) - 1) ^ 4 =
        (p : ℝ) * ((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2) / ((p : ℝ) - 1) ^ 4 := by
      rw [one_sub_div (pow_ne_zero 4 a1)]; congr 1; ring
    rw [l1, l2, div_mul_div_comm, div_eq_div_iff (pow_ne_zero 3 a1)
      (mul_ne_zero (pow_ne_zero 4 a1) (mul_ne_zero a2 a4))]
    ring
  · have e5 : phi0 n p = -1 / (((p : ℝ) ^ 2 - 3 * p + 3) * ((p : ℝ) - 1)) := by
      simp [phi0, hn, h2]
    have e6 : rr n p = 1 := by simp [rr, hn]
    rw [e5, e6, mul_one, neg_div, ← sub_eq_add_neg, one_add_div (pow_ne_zero 3 a1),
      one_sub_div (mul_ne_zero a3 a1), one_sub_div (pow_ne_zero 4 a1), div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 a1) (mul_ne_zero a3 a1)) (pow_ne_zero 4 a1)]
    ring

/-- `rr n p ∈ [1, 1 + 1/(p-2) - 1/(p-1)]` for primes `p ≥ 3`. -/
theorem rr_bounds (n : ℕ) {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    1 ≤ rr n p ∧ rr n p ≤ 1 + (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) := by
  have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
  have tpos : 0 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
    rw [sub_nonneg]; apply one_div_le_one_div_of_le (by linarith); linarith
  unfold rr
  split_ifs with h
  · have a1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
    have a2 : (p : ℝ) - 2 ≠ 0 := by intro h; linarith
    have a4 : 0 < (p : ℝ) ^ 2 - 2 * p + 2 := by nlinarith
    have e : ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 3 * p + 3) /
        (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2)) =
        1 + 1 / (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2)) := by
      rw [one_add_div (mul_ne_zero a2 a4.ne')]; congr 1; ring
    have e2 : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
      field_simp; ring
    rw [e, e2]
    have hpos : 0 < ((p : ℝ) - 2) * ((p : ℝ) - 1) := by apply mul_pos <;> linarith
    constructor
    · have : 0 < 1 / (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2)) := by
        apply one_div_pos.2; apply mul_pos (by linarith) a4
      linarith
    · have : 1 / (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2)) ≤
          1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
        apply one_div_le_one_div_of_le hpos
        apply mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      linarith
  · constructor <;> linarith

/-- `Pi4 n` as a product of `rr n p` over the primes `p ≤ M`, `M ≥ n > 0`. -/
theorem Pi4_eq_prod (n M : ℕ) (hn : 0 < n) (hM : n ≤ M) :
    Pi4 n = ∏ p ∈ Nat.primesLE M, rr n p := by
  unfold Pi4
  have hsub : n.primeFactors.filter (fun p => p ≠ 2) ⊆ Nat.primesLE M := by
    intro p hp
    rw [mem_filter, Nat.mem_primeFactors] at hp
    exact Nat.mem_primesLE.2 ⟨(Nat.le_of_dvd hn hp.1.2.1).trans hM, hp.1.1⟩
  rw [← prod_subset hsub]
  · refine prod_congr rfl fun p hp => ?_
    rw [mem_filter] at hp
    rw [rr, if_pos ⟨hp.2, Nat.dvd_of_mem_primeFactors hp.1⟩]
  · intro p hp hpn
    rw [rr, if_neg]
    rintro ⟨h2, hd⟩
    exact hpn (mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨(Nat.mem_primesLE.1 hp).2, hd, hn.ne'⟩, h2⟩)

/-- Splitting `Pi4 n` at `D`: `Pi4 n = R * T` with `T ∈ [1, exp (1/(D-1))]`. -/
theorem Pi4_split (n D : ℕ) (hn : 0 < n) (hD : 2 ≤ D) :
    ∃ T : ℝ, Pi4 n = (∏ p ∈ Nat.primesLE D, rr n p) * T ∧ 1 ≤ T ∧
      T ≤ Real.exp (1 / ((D : ℝ) - 1)) := by
  set M := max n D
  have hS : (Nat.primesLE M).filter (fun p => p ≤ D) = Nat.primesLE D := by
    ext p; simp only [mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨⟨h'.trans (le_max_right _ _), h⟩, h'⟩
  refine ⟨∏ p ∈ (Nat.primesLE M).filter (fun p => ¬ p ≤ D), rr n p, ?_, ?_⟩
  · rw [Pi4_eq_prod n M hn (le_max_left _ _), ← hS, prod_filter_mul_prod_filter_not]
  · have hb : ∀ p ∈ (Nat.primesLE M).filter (fun p => ¬ p ≤ D),
        1 ≤ rr n p ∧ rr n p ≤ 1 + (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) := by
      intro p hp
      rw [mem_filter, Nat.mem_primesLE] at hp
      exact rr_bounds n hp.1.2 (by omega)
    obtain ⟨h1, h2⟩ := prod_le_exp_sum _ _ hb
    refine ⟨h1, h2.trans (Real.exp_le_exp.2 ?_)⟩
    apply tele_set_le _ hD
    intro p hp
    rw [mem_filter] at hp; omega

/-- one_le_Pi4. -/
theorem one_le_Pi4 (n : ℕ) : 1 ≤ Pi4 n := by
  unfold Pi4
  refine one_le_prod₀ fun p hp => ?_
  rw [mem_filter] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have h := (rr_bounds n hpp (three_le_of_prime_ne_two hpp hp.2)).1
  rwa [rr, if_pos ⟨hp.2, Nat.dvd_of_mem_primeFactors hp.1⟩] at h

theorem Pi4_le_exp_one (n : ℕ) (hn : 0 < n) : Pi4 n ≤ Real.exp 1 := by
  obtain ⟨T, hT, h1, h2⟩ := Pi4_split n 2 hn le_rfl
  have hR : ∏ p ∈ Nat.primesLE 2, rr n p = 1 := by
    refine prod_eq_one fun p hp => ?_
    rw [Nat.mem_primesLE] at hp
    have : p = 2 := by have := hp.2.two_le; omega
    subst this; simp [rr]
  rw [hT, hR, one_mul]
  norm_num at h2
  exact h2

/-! ### Convergence of the partial products -/

theorem tendsto_primesLE_prod (f : ℕ → ℝ)
    (hf : Multipliable (fun p : {p : ℕ // p.Prime} => f p)) :
    Tendsto (fun D => ∏ p ∈ Nat.primesLE D, f p) atTop
      (𝓝 (∏' p : {p : ℕ // p.Prime}, f p)) := by
  set F : ℕ → Finset {p : ℕ // p.Prime} := fun Q => (Nat.primesLE Q).subtype (fun p => p.Prime)
  have hF : Tendsto F atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro a b hab x hx
      simp only [F, mem_subtype, Nat.mem_primesLE] at hx ⊢
      exact ⟨hx.1.trans hab, hx.2⟩
    · intro x
      refine ⟨x, ?_⟩
      simp only [F, mem_subtype, Nat.mem_primesLE]
      exact ⟨le_rfl, x.2⟩
  have hc := hf.hasProd.comp hF
  refine hc.congr fun Q => ?_
  simp only [Function.comp, F]
  rw [prod_subtype_eq_prod_filter (f := f)]
  rw [filter_true_of_mem (fun p hp => (Nat.mem_primesLE.1 hp).2)]

theorem C3_eq : C3 = ∏' p : {p : ℕ // p.Prime}, f3 p := by
  unfold C3
  refine tprod_congr fun p => ?_
  by_cases h : (p : ℕ) = 2
  · have : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h
    simp [f3, h, this]
  · have : p ≠ ⟨2, Nat.prime_two⟩ := fun e => h (by rw [e])
    simp [f3, h, this]

theorem C4_eq : C4 = ∏' p : {p : ℕ // p.Prime}, f4 p := by
  unfold C4
  refine tprod_congr fun p => ?_
  by_cases h : (p : ℕ) = 2
  · have : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h
    simp [f4, h, this]
  · have : p ≠ ⟨2, Nat.prime_two⟩ := fun e => h (by rw [e])
    simp [f4, h, this]

theorem inv4_le_inv3 {p : ℕ} (hp : p.Prime) : 1 / ((p : ℝ) - 1) ^ 4 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply one_div_le_one_div_of_le (pow_pos (by linarith) 3)
  have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  calc ((p : ℝ) - 1) ^ 3 = ((p : ℝ) - 1) ^ 3 * 1 := (mul_one _).symm
    _ ≤ ((p : ℝ) - 1) ^ 3 * ((p : ℝ) - 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((p : ℝ) - 1) ^ 4 := by ring

theorem f3_mult : Multipliable (fun p : {p : ℕ // p.Prime} => f3 p) := by
  have hs : Summable (fun p : {p : ℕ // p.Prime} =>
      if (p : ℕ) = 2 then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 3) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (summable_inv_sub_one_cube.subtype (fun p : ℕ => p.Prime))
    · have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
      split_ifs
      · exact le_rfl
      · apply div_nonneg zero_le_one; apply pow_nonneg; linarith
    · have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
      split_ifs
      · apply div_nonneg zero_le_one; apply pow_nonneg; linarith
      · exact le_rfl
  refine (Real.multipliable_one_add_of_summable hs).congr fun p => ?_
  by_cases h : (p : ℕ) = 2 <;> simp [f3, h]

theorem f4_mult : Multipliable (fun p : {p : ℕ // p.Prime} => f4 p) := by
  have hs : Summable (fun p : {p : ℕ // p.Prime} =>
      if (p : ℕ) = 2 then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 4) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (summable_inv_sub_one_cube.subtype (fun p : ℕ => p.Prime))
    · have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
      split_ifs
      · exact le_rfl
      · apply div_nonneg zero_le_one; apply pow_nonneg; linarith
    · have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
      split_ifs
      · apply div_nonneg zero_le_one; apply pow_nonneg; linarith
      · exact inv4_le_inv3 p.2
  refine (Real.multipliable_one_add_of_summable hs.neg).congr fun p => ?_
  by_cases h : (p : ℕ) = 2
  · simp [f4, h]
  · simp [f4, h, sub_eq_add_neg, neg_div]

theorem tendsto_A : Tendsto (fun D => ∏ p ∈ Nat.primesLE D, f3 p) atTop (𝓝 C3) := by
  rw [C3_eq]; exact tendsto_primesLE_prod f3 f3_mult

theorem tendsto_B : Tendsto (fun D => ∏ p ∈ Nat.primesLE D, f4 p) atTop (𝓝 C4) := by
  rw [C4_eq]; exact tendsto_primesLE_prod f4 f4_mult

/-- The partial products of `C₄` are at least `3/4`. -/
theorem B_ge (D : ℕ) : (3 : ℝ) / 4 ≤ ∏ p ∈ Nat.primesLE D, f4 p := by
  set v : ℕ → ℝ := fun p => if p = 2 then 0 else 1 / ((p : ℝ) - 1) ^ 4 with hv
  have hf : ∀ p ∈ Nat.primesLE D, f4 p = 1 - v p := by
    intro p _; by_cases h : p = 2 <;> simp [f4, hv, h]
  rw [prod_congr rfl hf]
  have hv01 : ∀ p ∈ Nat.primesLE D, 0 ≤ v p ∧ v p ≤ 1 := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    by_cases h : p = 2
    · simp [hv, h]
    · simp only [hv, if_neg h]
      constructor
      · apply div_nonneg zero_le_one; apply pow_nonneg; linarith
      · rw [div_le_one (pow_pos (by linarith) 4)]
        have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
        exact one_le_pow₀ h1
  refine le_trans ?_ (one_sub_sum_le_prod _ v hv01)
  have hsum : ∑ p ∈ Nat.primesLE D, v p ≤ 1 / 4 := by
    rw [← sum_filter_add_sum_filter_not (Nat.primesLE D) (fun p => p ≠ 2)]
    have h0 : ∑ p ∈ (Nat.primesLE D).filter (fun p => ¬ p ≠ 2), v p = 0 := by
      refine sum_eq_zero fun p hp => ?_
      rw [mem_filter, not_not] at hp
      simp [hv, hp.2]
    rw [h0, add_zero]
    calc ∑ p ∈ (Nat.primesLE D).filter (fun p => p ≠ 2), v p
        ≤ ∑ p ∈ (Nat.primesLE D).filter (fun p => p ≠ 2),
            (1 / 4) * (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter, Nat.mem_primesLE] at hp
          have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp.1.2 hp.2
          simp only [hv, if_neg hp.2]
          have e2 : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) =
              1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
            have a1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
            have a2 : (p : ℝ) - 2 ≠ 0 := by intro h; linarith
            field_simp; ring
          rw [e2, one_div_mul_one_div]
          apply one_div_le_one_div_of_le (by apply mul_pos (by norm_num); apply mul_pos <;> linarith)
          set y : ℝ := (p : ℝ) - 1 with hy
          have hy2 : 2 ≤ y := by linarith
          have hx : (p : ℝ) - 2 = y - 1 := by rw [hy]; ring
          rw [hx]
          have h4 : 4 * y ≤ y ^ 3 := by
            have hy4 : 4 ≤ y ^ 2 := by nlinarith
            have := mul_le_mul_of_nonneg_left hy4 (show (0 : ℝ) ≤ y by linarith)
            calc 4 * y = y * 4 := by ring
              _ ≤ y * y ^ 2 := this
              _ = y ^ 3 := by ring
          have h5 : y * (4 * y) ≤ y * y ^ 3 := mul_le_mul_of_nonneg_left h4 (by linarith)
          nlinarith
      _ = (1 / 4) * ∑ p ∈ (Nat.primesLE D).filter (fun p => p ≠ 2),
            (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) := by rw [mul_sum]
      _ ≤ (1 / 4) * (1 / ((2 : ℕ) - 1 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply tele_set_le _ le_rfl
          intro p hp
          rw [mem_filter, Nat.mem_primesLE] at hp
          have := three_le_of_prime_ne_two hp.1.2 hp.2
          omega
      _ = 1 / 4 := by norm_num
  linarith

/-- C4_pos. -/
theorem C4_pos : 0 < C4 := by
  have : (3 : ℝ) / 4 ≤ C4 := ge_of_tendsto' tendsto_B B_ge
  linarith

theorem C3_pos : 0 < C3 := by
  have h := LeanLab.HardyLittlewood1923.K_eq_two_mul_C3
  have := one_le_K
  linarith

/-! ### Assembly -/

/-- The error term of the uniform approximation. -/
noncomputable def errE (D : ℕ) : ℝ :=
  C3 * Real.exp 8 / Real.sqrt D + |C3 - ∏ p ∈ Nat.primesLE D, f3 p| +
    |∏ p ∈ Nat.primesLE D, f4 p - C4| * Real.exp 1 +
    C4 * Real.exp 1 * (Real.exp (1 / ((D : ℝ) - 1)) - 1)

theorem rr_nonneg (n : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ rr n p := by
  by_cases h2 : p = 2
  · subst h2; simp [rr]
  · linarith [(rr_bounds n hp (three_le_of_prime_ne_two hp h2)).1]

/-- The quantitative bound, for every `n > 0` and `D ≥ 2`. -/
theorem main_bound (n D : ℕ) (hn : 0 < n) (hD : 2 ≤ D) :
    |C3 * ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ Odd d ∧ Nat.Coprime d n),
        g d / (Nat.totient d : ℝ) - C4 * Pi4 n| ≤ errE D := by
  rw [sum_eq_sum_H]
  set S := ∑ d ∈ (Icc 1 D).filter Squarefree, H n d with hS
  set E := ∏ p ∈ Nat.primesLE D, (1 + phi0 n p) with hE
  set A := ∏ p ∈ Nat.primesLE D, f3 p with hA
  set B := ∏ p ∈ Nat.primesLE D, f4 p with hB
  set R := ∏ p ∈ Nat.primesLE D, rr n p with hR
  have hSE : |S - E| ≤ Real.exp 8 / Real.sqrt D := by
    have h := tail_bound (H n) (H_mult n)
      (fun p hp => by rw [H_prime n hp]; exact (phi0_bounds n hp).1) (by omega : 1 ≤ D)
    have e : ∏ p ∈ Nat.primesLE D, (1 + H n p) = E :=
      prod_congr rfl fun p hp => by rw [H_prime n (Nat.mem_primesLE.1 hp).2]
    rwa [e] at h
  have hE01 : 0 ≤ E ∧ E ≤ 1 := by
    have hfac : ∀ p ∈ Nat.primesLE D, 0 ≤ 1 + phi0 n p ∧ 1 + phi0 n p ≤ 1 := by
      intro p hp
      have hpp := (Nat.mem_primesLE.1 hp).2
      obtain ⟨h1, h2⟩ := phi0_bounds n hpp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have h3 : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        rw [div_le_one (pow_pos (by linarith) 2)]; nlinarith
      have := neg_abs_le (phi0 n p)
      constructor <;> linarith
    exact ⟨prod_nonneg fun p hp => (hfac p hp).1,
      prod_le_one₀ (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2)⟩
  have hAE : A * E = B * R := by
    rw [hA, hE, hB, hR, ← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun p hp => local_identity n (Nat.mem_primesLE.1 hp).2
  obtain ⟨T, hT, hT1, hT2⟩ := Pi4_split n D hn hD
  have hR0 : 0 ≤ R := prod_nonneg fun p hp => rr_nonneg n (Nat.mem_primesLE.1 hp).2
  have hRe : R ≤ Real.exp 1 := by
    have h1 := Pi4_le_exp_one n hn
    rw [hT] at h1
    nlinarith
  have hC3 := C3_pos
  have hC4 := C4_pos
  have key : C3 * S - C4 * Pi4 n =
      C3 * (S - E) + (C3 - A) * E + (B - C4) * R + C4 * R * (1 - T) := by
    rw [hT]; linear_combination hAE
  rw [key]
  have b1 : |C3 * (S - E)| ≤ C3 * Real.exp 8 / Real.sqrt D := by
    rw [abs_mul, abs_of_pos hC3, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hSE hC3.le
  have b2 : |(C3 - A) * E| ≤ |C3 - A| := by
    rw [abs_mul, abs_of_nonneg hE01.1]
    calc |C3 - A| * E ≤ |C3 - A| * 1 := mul_le_mul_of_nonneg_left hE01.2 (abs_nonneg _)
      _ = |C3 - A| := mul_one _
  have b3 : |(B - C4) * R| ≤ |B - C4| * Real.exp 1 := by
    rw [abs_mul, abs_of_nonneg hR0]
    exact mul_le_mul_of_nonneg_left hRe (abs_nonneg _)
  have b4 : |C4 * R * (1 - T)| ≤ C4 * Real.exp 1 * (Real.exp (1 / ((D : ℝ) - 1)) - 1) := by
    rw [abs_mul, abs_mul, abs_of_pos hC4, abs_of_nonneg hR0, abs_of_nonpos (by linarith)]
    have h1 : C4 * R ≤ C4 * Real.exp 1 := mul_le_mul_of_nonneg_left hRe hC4.le
    have h2 : -(1 - T) ≤ Real.exp (1 / ((D : ℝ) - 1)) - 1 := by linarith
    exact mul_le_mul h1 h2 (by linarith) (by positivity)
  have tri := abs_add_three (C3 * (S - E)) ((C3 - A) * E) ((B - C4) * R)
  have tri2 := abs_add_le (C3 * (S - E) + (C3 - A) * E + (B - C4) * R) (C4 * R * (1 - T))
  have herr : errE D = C3 * Real.exp 8 / Real.sqrt D + |C3 - A| + |B - C4| * Real.exp 1 +
      C4 * Real.exp 1 * (Real.exp (1 / ((D : ℝ) - 1)) - 1) := rfl
  rw [herr]
  linarith

theorem tendsto_errE : Tendsto errE atTop (𝓝 0) := by
  have t1 : Tendsto (fun D : ℕ => C3 * Real.exp 8 / Real.sqrt D) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have t2 : Tendsto (fun D : ℕ => |C3 - ∏ p ∈ Nat.primesLE D, f3 p|) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := C3)).sub tendsto_A
    simpa using this.abs
  have t3 : Tendsto (fun D : ℕ => |∏ p ∈ Nat.primesLE D, f4 p - C4| * Real.exp 1) atTop
      (𝓝 (0 * Real.exp 1)) := by
    have := (tendsto_B.sub_const C4).abs
    simp only [sub_self, abs_zero] at this
    exact this.mul_const _
  have t4 : Tendsto (fun D : ℕ => C4 * Real.exp 1 * (Real.exp (1 / ((D : ℝ) - 1)) - 1)) atTop
      (𝓝 (C4 * Real.exp 1 * 0)) := by
    have h0 : Tendsto (fun D : ℕ => 1 / ((D : ℝ) - 1)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun x : ℝ => Real.exp x - 1) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun x : ℝ => Real.exp x - 1) :=
        Real.continuous_exp.sub continuous_const
      have := hcont.tendsto (0 : ℝ)
      simpa using this
    exact (hc.comp h0).const_mul _
  have := ((t1.add t2).add t3).add t4
  rw [show (0 : ℝ) + 0 + 0 * Real.exp 1 + C4 * Real.exp 1 * 0 = 0 by ring] at this
  exact this

/-- The average of the singular series over p ≡ n, uniformly in even n: truncated sums tend to C4·Pi4 n / C3. -/
theorem euler_avg_tendsto : ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, ∀ D n : ℕ, D₀ ≤ D → Even n → 0 < n →
    |C3 * ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ Odd d ∧ Nat.Coprime d n),
        g d / (Nat.totient d : ℝ) - C4 * Pi4 n| ≤ ε := by
  intro ε hε
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.1
    (((tendsto_order.1 tendsto_errE).2 ε hε).and (eventually_ge_atTop 2))
  refine ⟨D₀, fun D n hD _ hn => ?_⟩
  obtain ⟨h1, h2⟩ := hD₀ D hD
  exact (main_bound n D hn h2).trans h1.le

end LeanLab.HardyLittlewood1923

