module

public import LeanLab.PNTPort.Vinogradov.SingPos

/-!
# The binary singular series, truncated, off a small exceptional set

Lab proof, unit U-6250, CLOUD 20261020T0917Z-cloud39. AI wrote the Lean code. Known
mathematics: Estermann 1938, Vaughan's book Chapter 3. Binary Goldbach is OPEN.

* `f2 n q = μ(q)² c_q(n) / φ(q)²`, multiplicative; `singP2 P n`, the truncated binary singular
  series `∑_{q ≤ P} ∑_{(a, q) = 1} (μ(q)/φ(q))² e(an/q)`, equals `∑_{q ≤ P} f2 n q`, `singP2_eq`.
* `euler2_ge_one`: for even `n` the Euler product `∏_{p ≤ P} (1 + f2 n p)` is at least 1.
* `G n = ∏_{p ∣ n} (1 + √p/(p - 1))`, the weight that the truncation error carries.
* `sing2_ge`: for even `n ≠ 0` and `P ≥ 2`, `∑_{q ≤ P} f2 n q ≥ 1 - e⁸ G(n)/√P`.
* `sum_G_le`: `∑_{n ≤ x} G(n) ≤ e⁸ x`, so `card_G_gt`: at most `e⁸ x / T` of the `n ≤ x`
  have `G(n) > T`. This is the exceptional set of Estermann's major arc count.
-/

@[expose] public section


namespace LeanLab.ExceptionalSet.MVMajor

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve

/-- `q ↦ 1/φ(q)²`. -/
noncomputable def invPhi2 : ArithmeticFunction ℝ := ⟨fun q => 1 / (q.totient : ℝ) ^ 2, by simp⟩

lemma invPhi2_mult : invPhi2.IsMultiplicative := by
  refine ⟨by simp [invPhi2], fun {a b} hab => ?_⟩
  show 1 / ((a * b).totient : ℝ) ^ 2 = 1 / (a.totient : ℝ) ^ 2 * (1 / (b.totient : ℝ) ^ 2)
  rw [Nat.totient_mul hab]; push_cast; rw [mul_pow, one_div_mul_one_div]

/-- The binary factor `f2(q) = μ(q)² c_q(n) / φ(q)²`. -/
noncomputable def f2 (n : ℕ) : ArithmeticFunction ℝ :=
  (((μ : ArithmeticFunction ℝ).pmul (μ : ArithmeticFunction ℝ)).pmul (cR n)).pmul invPhi2

lemma f2_mult (n : ℕ) : (f2 n).IsMultiplicative :=
  ((isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul
    (cR_mult n)).pmul invPhi2_mult

lemma f2_apply {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    f2 n q = (μ q : ℝ) ^ 2 * HeathBrown1985.ramanujan q n / (q.totient : ℝ) ^ 2 := by
  unfold f2
  rw [pmul_apply, pmul_apply, pmul_apply, intCoe_apply, cR_apply hq]
  show _ * (1 / (q.totient : ℝ) ^ 2) = _
  ring

/-- The truncated binary singular series. -/
noncomputable def singP2 (P n : ℕ) : ℂ :=
  ∑ p ∈ majIdx P, ((μ p.1 : ℂ) / p.1.totient) ^ 2 * e (n * ((p.2 : ℝ) / p.1))

/-- `𝔖_P(n)` in Ramanujan sum form, real. -/
theorem singP2_eq (P n : ℕ) : singP2 P n = ((∑ q ∈ Icc 1 P, f2 n q : ℝ) : ℂ) := by
  unfold singP2 majIdx
  rw [sum_filter, sum_product]
  push_cast
  refine sum_congr rfl fun q hq => ?_
  rw [mem_Icc] at hq
  have hset : ∀ a ∈ range P, (if a < q ∧ Nat.Coprime a q then
      ((μ q : ℂ) / q.totient) ^ 2 * e (n * ((a : ℝ) / q)) else 0) =
      if a ∈ (range q).filter (fun r => Nat.Coprime r q) then
        ((μ q : ℂ) / q.totient) ^ 2 * e (n * a / q) else 0 := by
    intro a _
    simp only [mem_filter, mem_range]
    split_ifs <;> first | rfl | (congr 2; ring)
  rw [sum_congr rfl hset, ← sum_filter]
  have hsub : (range P).filter (fun a => a ∈ (range q).filter (fun r => Nat.Coprime r q)) =
      (range q).filter (fun r => Nat.Coprime r q) := by
    ext a; simp only [mem_filter, mem_range]; constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨by omega, h⟩
  rw [hsub, ← mul_sum, ramanujan_sum hq.1 n, f2_apply hq.1]
  push_cast
  ring

lemma f2_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    f2 n p = (if p ∣ n then (p : ℝ) - 1 else -1) / ((p : ℝ) - 1) ^ 2 := by
  rw [f2_apply hp.one_lt.le, ramanujan_prime hp, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le]
  push_cast; ring

lemma f2_two_even {n : ℕ} (hn : Even n) : f2 n 2 = 1 := by
  rw [f2_prime Nat.prime_two, if_pos (even_iff_two_dvd.1 hn)]
  norm_num

lemma one_add_f2_ge {p : ℕ} (hp : p.Prime) (n : ℕ) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + f2 n p := by
  rw [f2_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : 0 < (p : ℝ) - 1 := by linarith
  split_ifs
  · have : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by positivity
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · rw [neg_div]; linarith

/-- The Euler product of `1 + f2(p)` over primes up to `P` is at least 1 for even `n`. -/
theorem euler2_ge_one {n : ℕ} (hn : Even n) {P : ℕ} (hP : 2 ≤ P) :
    1 ≤ ∏ p ∈ Nat.primesLE P, (1 + f2 n p) := by
  have h2 : 2 ∈ Nat.primesLE P := Nat.mem_primesLE.2 ⟨hP, Nat.prime_two⟩
  rw [← insert_erase h2, prod_insert (notMem_erase 2 _), f2_two_even hn]
  set T := (Nat.primesLE P).erase 2 with hT
  have hTsub : T ⊆ Icc 3 P := by
    intro p hp
    rw [hT, mem_erase, Nat.mem_primesLE] at hp
    rw [mem_Icc]
    exact ⟨by have := hp.2.2.two_le; omega, hp.2.1⟩
  have hfac : ∀ m ∈ Icc 3 P, 0 ≤ 1 - 1 / ((m : ℝ) - 1) ^ 2 ∧ 1 - 1 / ((m : ℝ) - 1) ^ 2 ≤ 1 := by
    intro m hm
    rw [mem_Icc] at hm
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
    have h1 : (2 : ℝ) ≤ (m : ℝ) - 1 := by linarith
    have h4 : (4 : ℝ) ≤ ((m : ℝ) - 1) ^ 2 := by nlinarith
    constructor
    · rw [sub_nonneg, div_le_one (by positivity)]; linarith
    · have : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
      linarith
  have hA : ∏ m ∈ Icc 3 P, (1 - 1 / ((m : ℝ) - 1) ^ 2) ≤ ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    prod_le_prod_of_subset_of_le_one₀ hTsub (fun i hi => (hfac i hi).1)
      (fun i hi _ => (hfac i hi).2)
  have hB : ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ ∏ p ∈ T, (1 + f2 n p) := by
    refine Finset.prod_le_prod₀ (h0 := fun p hp => (hfac p (hTsub hp)).1) (h1 := fun p hp => ?_)
    rw [hT, mem_erase, Nat.mem_primesLE] at hp
    exact one_add_f2_ge hp.2.2 n
  rw [tele_prod P hP] at hA
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hhalf : 1 / 2 ≤ (P : ℝ) / (2 * ((P : ℝ) - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have : (1 : ℝ) + 1 = 2 := by norm_num
  rw [this]
  linarith

lemma sum_divisors_primorial2 (n P : ℕ) :
    ∑ d ∈ (primorial P).divisors, f2 n d = ∏ p ∈ Nat.primesLE P, (1 + f2 n p) := by
  rw [← (f2_mult n).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial P),
    primeFactors_primorial]

lemma f2_eq_zero_of_not_sqf {n q : ℕ} (hq : 1 ≤ q) (h : ¬ Squarefree q) : f2 n q = 0 := by
  rw [f2_apply hq, moebius_eq_zero_of_not_squarefree h]; simp

lemma sum_Icc_eq_divisors2 (n P : ℕ) :
    ∑ q ∈ Icc 1 P, f2 n q = ∑ d ∈ (primorial P).divisors.filter (· ≤ P), f2 n d := by
  symm
  apply sum_subset
  · intro d hd
    rw [mem_filter, Nat.mem_divisors] at hd
    rw [mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 (primorial_pos P), hd.2⟩
  · intro q hq hq'
    rw [mem_Icc] at hq
    by_contra hne
    apply hq'
    have hsqf : Squarefree q := by
      by_contra hs; exact hne (f2_eq_zero_of_not_sqf hq.1 hs)
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_primorial_of_sqf hsqf hq.2, (primorial_pos P).ne'⟩, hq.2⟩

/-- `d ↦ |f2(d)| √d`, multiplicative. -/
noncomputable def h2 (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |f2 n d| * Real.sqrt d, by simp⟩

lemma h2_apply (n d : ℕ) : h2 n d = |f2 n d| * Real.sqrt d := rfl

lemma h2_mult (n : ℕ) : (h2 n).IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · show |f2 n 1| * Real.sqrt ((1 : ℕ) : ℝ) = 1
    rw [(f2_mult n).map_one]; simp
  · show |f2 n (a * b)| * Real.sqrt ((a * b : ℕ) : ℝ) =
      (|f2 n a| * Real.sqrt (a : ℝ)) * (|f2 n b| * Real.sqrt (b : ℝ))
    rw [(f2_mult n).map_mul_of_coprime hab, abs_mul]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg a)]
    ring

lemma sum_divisors_h2 (n P : ℕ) :
    ∑ d ∈ (primorial P).divisors, h2 n d = ∏ p ∈ Nat.primesLE P, (1 + h2 n p) := by
  rw [← (h2_mult n).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial P),
    primeFactors_primorial]

/-- The weight `w(p) = √p/(p - 1)` of a prime dividing `n`. -/
noncomputable def w (p : ℕ) : ℝ := Real.sqrt p / ((p : ℝ) - 1)

/-- `G(n) = ∏_{p ∣ n} (1 + √p/(p - 1))`. -/
noncomputable def G (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 + w p)

lemma w_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ w p := by
  unfold w
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply div_nonneg (Real.sqrt_nonneg _); linarith

lemma one_add_h2_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    1 + h2 n p ≤ (1 + Real.sqrt p / ((p : ℝ) - 1) ^ 2) * (if p ∣ n then 1 + w p else 1) := by
  rw [h2_apply, f2_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : 0 < (p : ℝ) - 1 := by linarith
  have hs := Real.sqrt_nonneg (p : ℝ)
  have ha : 0 ≤ Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by positivity
  split_ifs
  · have e1 : |((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2| * Real.sqrt p = w p := by
      unfold w
      rw [abs_of_nonneg (by positivity)]
      field_simp
    rw [e1]
    have := w_nonneg hp
    nlinarith
  · have e1 : |(-1 : ℝ) / ((p : ℝ) - 1) ^ 2| * Real.sqrt p = Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by
      rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]; ring
    rw [e1, mul_one]

lemma prod_tele_le (P : ℕ) :
    ∏ p ∈ Nat.primesLE P, (1 + Real.sqrt p / ((p : ℝ) - 1) ^ 2) ≤ Real.exp 8 := by
  calc ∏ p ∈ Nat.primesLE P, (1 + Real.sqrt p / ((p : ℝ) - 1) ^ 2)
      ≤ ∏ p ∈ Nat.primesLE P, Real.exp (Real.sqrt p / ((p : ℝ) - 1) ^ 2) :=
        Finset.prod_le_prod₀ (h0 := fun p hp => by positivity) (h1 := fun p _ => by
          have := Real.add_one_le_exp (Real.sqrt p / ((p : ℝ) - 1) ^ 2); linarith)
    _ = Real.exp (∑ p ∈ Nat.primesLE P, Real.sqrt p / ((p : ℝ) - 1) ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 8 := by
        apply Real.exp_le_exp.2
        refine le_trans ?_ (sum_tele_le P)
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Nat.mem_primesLE] at hp
          rw [mem_Icc]; exact ⟨hp.2.two_le, hp.1⟩
        · intro _ _ _; positivity

lemma euler_h2_le {n : ℕ} (hn : n ≠ 0) (P : ℕ) :
    ∏ p ∈ Nat.primesLE P, (1 + h2 n p) ≤ Real.exp 8 * G n := by
  have hG1 : ∀ p ∈ Nat.primesLE P, 0 ≤ (if p ∣ n then 1 + w p else 1) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have := w_nonneg hp.2
    split_ifs <;> linarith
  calc ∏ p ∈ Nat.primesLE P, (1 + h2 n p)
      ≤ ∏ p ∈ Nat.primesLE P, ((1 + Real.sqrt p / ((p : ℝ) - 1) ^ 2) *
          (if p ∣ n then 1 + w p else 1)) :=
        Finset.prod_le_prod₀ (h0 := fun p _ => by rw [h2_apply]; positivity)
          (h1 := fun p hp => one_add_h2_le (Nat.mem_primesLE.1 hp).2 n)
    _ = (∏ p ∈ Nat.primesLE P, (1 + Real.sqrt p / ((p : ℝ) - 1) ^ 2)) *
          ∏ p ∈ Nat.primesLE P, (if p ∣ n then 1 + w p else 1) := prod_mul_distrib
    _ ≤ Real.exp 8 * G n := by
        apply mul_le_mul (prod_tele_le P) _ (prod_nonneg hG1) (Real.exp_pos 8).le
        rw [← prod_filter]
        unfold G
        apply prod_le_prod_of_subset_of_one_le₀
        · intro p hp
          rw [mem_filter, Nat.mem_primesLE] at hp
          exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, hn⟩
        · intro p hp
          rw [mem_filter, Nat.mem_primesLE] at hp
          have := w_nonneg hp.1.2
          linarith
        · intro p hp _
          have := w_nonneg (Nat.prime_of_mem_primeFactors hp)
          linarith

/-- **The truncated binary singular series off the exceptional set**: for even `n ≠ 0` and
`P ≥ 2`, `∑_{q ≤ P} μ(q)² c_q(n)/φ(q)² ≥ 1 - e⁸ G(n)/√P`. -/
theorem sing2_ge {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) {P : ℕ} (hP : 2 ≤ P) :
    1 - Real.exp 8 * G n / Real.sqrt P ≤ ∑ q ∈ Icc 1 P, f2 n q := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.2 hPr
  rw [sum_Icc_eq_divisors2]
  have hsplit : ∑ d ∈ (primorial P).divisors.filter (fun d => d ≤ P), f2 n d +
      ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), f2 n d =
      ∏ p ∈ Nat.primesLE P, (1 + f2 n p) := by
    rw [sum_filter_add_sum_filter_not, sum_divisors_primorial2]
  have hE := euler2_ge_one hn hP
  have htail : |∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), f2 n d| ≤
      Real.exp 8 * G n / Real.sqrt P := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), |f2 n d|
        ≤ ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), h2 n d / Real.sqrt P := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter] at hd
          rw [h2_apply, le_div_iff₀ hsP]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Real.sqrt_le_sqrt (by exact_mod_cast (not_le.1 hd.2).le)
      _ ≤ ∑ d ∈ (primorial P).divisors, h2 n d / Real.sqrt P := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _; rw [h2_apply]; positivity
      _ = (∏ p ∈ Nat.primesLE P, (1 + h2 n p)) / Real.sqrt P := by
          rw [← sum_div, sum_divisors_h2]
      _ ≤ Real.exp 8 * G n / Real.sqrt P :=
          div_le_div_of_nonneg_right (euler_h2_le hn0 P) hsP.le
  set T := ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), f2 n d with hT
  set H := ∑ d ∈ (primorial P).divisors.filter (fun d => d ≤ P), f2 n d with hH
  have h1 : T ≤ |T| := le_abs_self T
  linarith

/-! ## The exceptional set is small -/

lemma G_eq_sum (n : ℕ) : G n = ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, w p := by
  unfold G
  rw [prod_one_add]

lemma prod_dvd_of_subset {n : ℕ} {t : Finset ℕ} (ht : t ⊆ n.primeFactors) : (∏ p ∈ t, p) ∣ n := by
  have hpr : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  exact (Finset.prod_primes_dvd n (fun p hp => (hpr p hp).prime)
    fun p hp => Nat.dvd_of_mem_primeFactors (ht hp))

lemma w_div_le {p : ℕ} (hp : p.Prime) : w p / p ≤ Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by
  unfold w
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : 0 < (p : ℝ) - 1 := by linarith
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hs := Real.sqrt_nonneg (p : ℝ)
  have : ((p : ℝ) - 1) ^ 2 ≤ (p - 1) * p := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hs]

/-- `∑_{n ≤ x} G(n) ≤ e⁸ x`. -/
theorem sum_G_le (x : ℕ) : ∑ n ∈ Icc 1 x, G n ≤ Real.exp 8 * x := by
  simp_rw [G_eq_sum]
  have key : ∑ n ∈ Icc 1 x, ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, w p =
      ∑ t ∈ (Nat.primesLE x).powerset, ∑ n ∈ (Icc 1 x).filter (fun n => t ⊆ n.primeFactors),
        ∏ p ∈ t, w p := by
    apply sum_comm'
    intro n t
    simp only [mem_Icc, mem_powerset, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨⟨h1, h2⟩, h3⟩, h3.trans fun p hp => ?_⟩
      rw [Nat.mem_primesLE]
      exact ⟨(Nat.le_of_mem_primeFactors hp).trans h2, Nat.prime_of_mem_primeFactors hp⟩
    · rintro ⟨⟨h1, h3⟩, _⟩
      exact ⟨h1, h3⟩
  rw [key]
  have hcount : ∀ t ∈ (Nat.primesLE x).powerset,
      ∑ n ∈ (Icc 1 x).filter (fun n => t ⊆ n.primeFactors), ∏ p ∈ t, w p ≤
        x * ∏ p ∈ t, (w p / p) := by
    intro t ht
    rw [mem_powerset] at ht
    have hpr : ∀ p ∈ t, p.Prime := fun p hp => (Nat.mem_primesLE.1 (ht hp)).2
    set d := ∏ p ∈ t, p with hd
    have hdpos : 0 < d := prod_pos fun p hp => (hpr p hp).pos
    have hsub : (Icc 1 x).filter (fun n => t ⊆ n.primeFactors) ⊆ (Ioc 0 x).filter (d ∣ ·) := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      rw [mem_filter, mem_Ioc]
      exact ⟨⟨by omega, hn.1.2⟩, prod_dvd_of_subset hn.2⟩
    have hc : (((Icc 1 x).filter (fun n => t ⊆ n.primeFactors)).card : ℝ) ≤ (x : ℝ) / d := by
      have h1 := card_le_card hsub
      rw [Nat.Ioc_filter_dvd_card_eq_div] at h1
      calc (((Icc 1 x).filter (fun n => t ⊆ n.primeFactors)).card : ℝ) ≤ ((x / d : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ (x : ℝ) / d := Nat.cast_div_le
    have hw : 0 ≤ ∏ p ∈ t, w p := prod_nonneg fun p hp => w_nonneg (hpr p hp)
    rw [sum_const, nsmul_eq_mul]
    calc (((Icc 1 x).filter (fun n => t ⊆ n.primeFactors)).card : ℝ) * ∏ p ∈ t, w p
        ≤ (x : ℝ) / d * ∏ p ∈ t, w p := mul_le_mul_of_nonneg_right hc hw
      _ = x * ∏ p ∈ t, (w p / p) := by
          rw [prod_div_distrib, hd]
          push_cast
          ring
  calc ∑ t ∈ (Nat.primesLE x).powerset, ∑ n ∈ (Icc 1 x).filter (fun n => t ⊆ n.primeFactors),
        ∏ p ∈ t, w p ≤ ∑ t ∈ (Nat.primesLE x).powerset, x * ∏ p ∈ t, (w p / p) := sum_le_sum hcount
    _ = x * ∏ p ∈ Nat.primesLE x, (1 + w p / p) := by rw [← mul_sum, prod_one_add]
    _ ≤ x * Real.exp 8 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
        refine le_trans ?_ (prod_tele_le x)
        refine Finset.prod_le_prod₀ (h0 := fun p hp => ?_) (h1 := fun p hp => ?_)
        · have hp := (Nat.mem_primesLE.1 hp).2
          have := w_nonneg hp
          have : (0 : ℝ) < p := by exact_mod_cast hp.pos
          positivity
        · have := w_div_le (Nat.mem_primesLE.1 hp).2; linarith
    _ = Real.exp 8 * x := by ring

/-- **The exceptional set**: at most `e⁸ x / T` of the `n ≤ x` have `G(n) > T`. -/
theorem card_G_gt (x : ℕ) {T : ℝ} (hT : 0 < T) :
    (((Icc 1 x).filter (fun n => T < G n)).card : ℝ) ≤ Real.exp 8 * x / T := by
  rw [le_div_iff₀ hT]
  have hG0 : ∀ n ∈ Icc 1 x, 0 ≤ G n := fun n _ =>
    prod_nonneg fun p hp => by have := w_nonneg (Nat.prime_of_mem_primeFactors hp); linarith
  calc (((Icc 1 x).filter (fun n => T < G n)).card : ℝ) * T
      = ∑ n ∈ (Icc 1 x).filter (fun n => T < G n), T := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Icc 1 x).filter (fun n => T < G n), G n :=
        sum_le_sum fun n hn => (mem_filter.1 hn).2.le
    _ ≤ ∑ n ∈ Icc 1 x, G n :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => hG0 n hn
    _ ≤ Real.exp 8 * x := sum_G_le x

end LeanLab.ExceptionalSet.MVMajor
