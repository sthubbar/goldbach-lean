module

public import LeanLab.PNTPort.Vinogradov.SingSeries

/-!
# The ternary singular series: multiplicativity

Lab proof, unit U-5259. AI wrote this file. Known mathematics, no cited input.

* `gDiv n d = d · 1_{d ∣ n}`, multiplicative; `cR n = gDiv n * μ`, the Ramanujan sum
  `c_q(n)` as a Dirichlet convolution, multiplicative, `cR_apply`.
* `fS n q = μ(q) c_q(n) / φ(q)³`, multiplicative, `fS_mult`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `d ↦ d · 1_{d ∣ n}`. -/
noncomputable def gDiv (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ∣ n then (d : ℝ) else 0, by simp⟩

lemma gDiv_apply (n d : ℕ) : gDiv n d = if d ∣ n then (d : ℝ) else 0 := rfl

lemma gDiv_mult (n : ℕ) : (gDiv n).IsMultiplicative := by
  refine ⟨by simp [gDiv_apply], fun {a b} hab => ?_⟩
  simp only [gDiv_apply]
  by_cases ha : a ∣ n
  · by_cases hb : b ∣ n
    · rw [if_pos (hab.mul_dvd_of_dvd_of_dvd ha hb), if_pos ha, if_pos hb]; push_cast; ring
    · rw [if_neg (fun h => hb (dvd_trans (dvd_mul_left b a) h)), if_neg hb, mul_zero]
  · rw [if_neg (fun h => ha (dvd_trans (dvd_mul_right a b) h)), if_neg ha, zero_mul]

/-- The Ramanujan sum as a Dirichlet convolution. -/
noncomputable def cR (n : ℕ) : ArithmeticFunction ℝ := gDiv n * (μ : ArithmeticFunction ℝ)

lemma cR_mult (n : ℕ) : (cR n).IsMultiplicative :=
  (gDiv_mult n).mul isMultiplicative_moebius.intCast

lemma cR_apply {q : ℕ} (hq : 1 ≤ q) (n : ℕ) : cR n q = HeathBrown1985.ramanujan q n := by
  unfold cR HeathBrown1985.ramanujan
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => gDiv n a * (μ : ArithmeticFunction ℝ) b)]
  simp only [gDiv_apply, intCoe_apply, ite_mul, zero_mul]
  rw [← sum_filter]
  apply sum_congr
  · ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, Nat.gcd_ne_zero_right h2⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, by omega⟩, h1⟩
  · intro d _; rfl

/-- `q ↦ 1/φ(q)³`. -/
noncomputable def invPhi3 : ArithmeticFunction ℝ := ⟨fun q => 1 / (q.totient : ℝ) ^ 3, by simp⟩

lemma invPhi3_mult : invPhi3.IsMultiplicative := by
  refine ⟨by simp [invPhi3], fun {a b} hab => ?_⟩
  show 1 / ((a * b).totient : ℝ) ^ 3 = 1 / (a.totient : ℝ) ^ 3 * (1 / (b.totient : ℝ) ^ 3)
  rw [Nat.totient_mul hab]; push_cast; rw [mul_pow, one_div_mul_one_div]

/-- The factor `f(q) = μ(q) c_q(n) / φ(q)³`. -/
noncomputable def fS (n : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).pmul (cR n)).pmul invPhi3

lemma fS_mult (n : ℕ) : (fS n).IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul (cR_mult n)).pmul invPhi3_mult

lemma fS_apply {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    fS n q = (μ q : ℝ) * HeathBrown1985.ramanujan q n / (q.totient : ℝ) ^ 3 := by
  unfold fS
  rw [pmul_apply, pmul_apply, intCoe_apply, cR_apply hq]
  show _ * (1 / (q.totient : ℝ) ^ 3) = _
  ring

lemma moebius_cube (q : ℕ) : (μ q : ℝ) ^ 3 = μ q := by
  rcases moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num

/-- `𝔖_P(n) = ∑_{q ≤ P} f(q)`. -/
theorem singP_eq_fS (P n : ℕ) : singP P n = ((∑ q ∈ Icc 1 P, fS n q : ℝ) : ℂ) := by
  rw [singP_eq]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  rw [fS_apply (mem_Icc.1 hq).1, moebius_cube]

lemma ramanujan_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    HeathBrown1985.ramanujan p n = if p ∣ n then (p : ℝ) - 1 else -1 := by
  unfold HeathBrown1985.ramanujan
  by_cases h : p ∣ n
  · rw [if_pos h, Nat.gcd_eq_right h, hp.divisors, sum_insert (by
      rw [mem_singleton]; exact hp.one_lt.ne), sum_singleton, Nat.div_self hp.pos, Nat.div_one,
      moebius_apply_prime hp, moebius_apply_one]
    push_cast; ring
  · have hg : Nat.gcd n p = 1 := by
      rw [Nat.gcd_comm]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 h
    rw [if_neg h, hg, Nat.divisors_one, sum_singleton, Nat.div_one, moebius_apply_prime hp]
    push_cast; ring

lemma fS_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    fS n p = -(if p ∣ n then (p : ℝ) - 1 else -1) / ((p : ℝ) - 1) ^ 3 := by
  rw [fS_apply hp.one_lt.le, ramanujan_prime hp, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le]
  push_cast; ring

lemma abs_fS_prime_le {p : ℕ} (hp : p.Prime) (n : ℕ) : |fS n p| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  rw [fS_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : 0 < (p : ℝ) - 1 := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 3), abs_neg]
  split_ifs
  · rw [abs_of_pos hq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hq 2]
  · rw [abs_neg, abs_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    nlinarith [pow_pos hq 2]

lemma fS_two_odd {n : ℕ} (hn : Odd n) : fS n 2 = 1 := by
  rw [fS_prime Nat.prime_two, if_neg (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])]
  norm_num

lemma one_add_fS_ge {p : ℕ} (hp : p.Prime) (n : ℕ) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + fS n p := by
  have := abs_fS_prime_le hp n
  have := neg_abs_le (fS n p)
  linarith

lemma tele_prod (P : ℕ) (hP : 2 ≤ P) :
    ∏ m ∈ Icc 3 P, (1 - 1 / ((m : ℝ) - 1) ^ 2) = (P : ℝ) / (2 * ((P : ℝ) - 1)) := by
  induction P, hP using Nat.le_induction with
  | base => norm_num
  | succ P hP ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
    have hP0 : (P : ℝ) ≠ 0 := by linarith
    have hP0' : (P : ℝ) - 1 ≠ 0 := by linarith
    push_cast
    rw [add_sub_cancel_right]
    field_simp
    ring

/-- The Euler product of `1 + f(p)` over primes up to `P` is at least 1 for odd `n`. -/
theorem euler_ge_one {n : ℕ} (hn : Odd n) {P : ℕ} (hP : 2 ≤ P) :
    1 ≤ ∏ p ∈ Nat.primesLE P, (1 + fS n p) := by
  have h2 : 2 ∈ Nat.primesLE P := Nat.mem_primesLE.2 ⟨hP, Nat.prime_two⟩
  rw [← insert_erase h2, prod_insert (notMem_erase 2 _), fS_two_odd hn]
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
  have hB : ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ ∏ p ∈ T, (1 + fS n p) := by
    refine Finset.prod_le_prod₀ (h0 := fun p hp => (hfac p (hTsub hp)).1) (h1 := fun p hp => ?_)
    rw [hT, mem_erase, Nat.mem_primesLE] at hp
    exact one_add_fS_ge hp.2.2 n
  rw [tele_prod P hP] at hA
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hhalf : 1 / 2 ≤ (P : ℝ) / (2 * ((P : ℝ) - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have : (1 : ℝ) + 1 = 2 := by norm_num
  rw [this]
  linarith

/-- The divisor sum over the primorial is the Euler product. -/
lemma sum_divisors_primorial (n P : ℕ) :
    ∑ d ∈ (primorial P).divisors, fS n d = ∏ p ∈ Nat.primesLE P, (1 + fS n p) := by
  rw [← (fS_mult n).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial P),
    primeFactors_primorial]

lemma fS_eq_zero_of_not_sqf {n q : ℕ} (hq : 1 ≤ q) (h : ¬ Squarefree q) : fS n q = 0 := by
  rw [fS_apply hq, moebius_eq_zero_of_not_squarefree h]; simp

lemma dvd_primorial_of_sqf {q P : ℕ} (hq : Squarefree q) (hqP : q ≤ P) : q ∣ primorial P := by
  rw [← Nat.prod_primeFactors_of_squarefree hq, primorial_eq_prod_primesLE]
  apply prod_dvd_prod_of_subset
  intro p hp
  rw [Nat.mem_primesLE]
  have hp' := Nat.mem_primeFactors.1 hp
  exact ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1).trans hqP, hp'.1⟩

/-- The truncated sum as a divisor sum over the primorial. -/
lemma sum_Icc_eq_divisors (n P : ℕ) :
    ∑ q ∈ Icc 1 P, fS n q = ∑ d ∈ (primorial P).divisors.filter (· ≤ P), fS n d := by
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
      by_contra hs; exact hne (fS_eq_zero_of_not_sqf hq.1 hs)
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_primorial_of_sqf hsqf hq.2, (primorial_pos P).ne'⟩, hq.2⟩

/-- `d ↦ |f(d)| √d`, multiplicative. -/
noncomputable def hS (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |fS n d| * Real.sqrt d, by simp⟩

lemma hS_mult (n : ℕ) : (hS n).IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · show |fS n 1| * Real.sqrt ((1 : ℕ) : ℝ) = 1
    rw [(fS_mult n).map_one]; simp
  · show |fS n (a * b)| * Real.sqrt ((a * b : ℕ) : ℝ) =
      (|fS n a| * Real.sqrt (a : ℝ)) * (|fS n b| * Real.sqrt (b : ℝ))
    rw [(fS_mult n).map_mul_of_coprime hab, abs_mul]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg a)]
    ring

/-- The telescoping bound `√m/(m-1)² ≤ 8(1/√(m-1) - 1/√m)` for `m ≥ 2`. -/
lemma tele_term {m : ℝ} (hm : 2 ≤ m) :
    Real.sqrt m / (m - 1) ^ 2 ≤ 8 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by
  set a := Real.sqrt (m - 1) with ha
  set b := Real.sqrt m with hb
  have ha2 : a ^ 2 = m - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = m := Real.sq_sqrt (by linarith)
  have ha1 : 1 ≤ a := by rw [ha, Real.one_le_sqrt]; linarith
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hb15 : b ≤ 3 / 2 * a := by nlinarith
  have hpos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  rw [← ha2]
  rw [div_sub_div _ _ hpos.ne' hbpos.ne', div_le_iff₀ (by positivity)]
  rw [show 8 * ((1 * b - a * 1) / (a * b)) * (a ^ 2) ^ 2 = 8 * (b - a) * a ^ 3 / b by
    field_simp]
  rw [le_div_iff₀ hbpos]
  have hba : b - a = 1 / (a + b) := by
    rw [eq_div_iff (by positivity)]; nlinarith
  rw [hba]
  rw [show 8 * (1 / (a + b)) * a ^ 3 = 8 * a ^ 3 / (a + b) by ring, le_div_iff₀ (by positivity)]
  nlinarith [mul_pos hpos hpos, mul_pos (mul_pos hpos hpos) hpos]

lemma sum_tele_le (P : ℕ) :
    ∑ m ∈ Icc 2 P, Real.sqrt m / ((m : ℝ) - 1) ^ 2 ≤ 8 := by
  have h : ∀ P : ℕ, ∑ m ∈ Icc 2 P, 8 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) ≤ 8 := by
    intro P
    induction P with
    | zero => simp
    | succ P ih =>
      rcases Nat.lt_or_ge P 1 with h0 | h0
      · interval_cases P; simp
      · have hsum : ∑ m ∈ Icc 2 (P + 1), 8 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) =
            8 * (1 - 1 / Real.sqrt ((P + 1 : ℕ) : ℝ)) := by
          clear ih
          induction P, h0 using Nat.le_induction with
          | base => norm_num
          | succ P hP ih =>
            rw [sum_Icc_succ_top (by omega), ih]
            push_cast; ring_nf
        rw [hsum]
        have : 0 ≤ 1 / Real.sqrt ((P + 1 : ℕ) : ℝ) := by positivity
        linarith
  refine le_trans (sum_le_sum fun m hm => ?_) (h P)
  rw [mem_Icc] at hm
  exact tele_term (by exact_mod_cast hm.1)

lemma sum_divisors_hS (n P : ℕ) :
    ∑ d ∈ (primorial P).divisors, hS n d = ∏ p ∈ Nat.primesLE P, (1 + hS n p) := by
  rw [← (hS_mult n).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial P),
    primeFactors_primorial]

lemma hS_apply (n d : ℕ) : hS n d = |fS n d| * Real.sqrt d := rfl

lemma euler_hS_le (n P : ℕ) : ∏ p ∈ Nat.primesLE P, (1 + hS n p) ≤ Real.exp 8 := by
  have h0 : ∀ p ∈ Nat.primesLE P, 0 ≤ 1 + hS n p := fun p _ => by
    rw [hS_apply]; positivity
  calc ∏ p ∈ Nat.primesLE P, (1 + hS n p) ≤ ∏ p ∈ Nat.primesLE P, Real.exp (hS n p) :=
        Finset.prod_le_prod₀ (h0 := h0) (h1 := fun p _ => by
          have := Real.add_one_le_exp (hS n p); linarith)
    _ = Real.exp (∑ p ∈ Nat.primesLE P, hS n p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 8 := by
        apply Real.exp_le_exp.2
        calc ∑ p ∈ Nat.primesLE P, hS n p
            ≤ ∑ p ∈ Nat.primesLE P, Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by
              refine sum_le_sum fun p hp => ?_
              rw [Nat.mem_primesLE] at hp
              rw [hS_apply, mul_comm]
              have := abs_fS_prime_le hp.2 n
              have hs := Real.sqrt_nonneg (p : ℝ)
              calc Real.sqrt p * |fS n p| ≤ Real.sqrt p * (1 / ((p : ℝ) - 1) ^ 2) :=
                    mul_le_mul_of_nonneg_left this hs
                _ = Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by ring
          _ ≤ ∑ m ∈ Icc 2 P, Real.sqrt m / ((m : ℝ) - 1) ^ 2 := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rw [Nat.mem_primesLE] at hp
                rw [mem_Icc]; exact ⟨hp.2.two_le, hp.1⟩
              · intro _ _ _; positivity
          _ ≤ 8 := sum_tele_le P

/-- **The truncated ternary singular series is positive for odd `n`**:
`𝔖_P(n) ≥ 1 - e⁸/√P`. -/
theorem singP_fS_ge {n : ℕ} (hn : Odd n) {P : ℕ} (hP : 2 ≤ P) :
    1 - Real.exp 8 / Real.sqrt P ≤ ∑ q ∈ Icc 1 P, fS n q := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.2 hPr
  rw [sum_Icc_eq_divisors]
  have hsplit : ∑ d ∈ (primorial P).divisors.filter (fun d => d ≤ P), fS n d +
      ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), fS n d =
      ∏ p ∈ Nat.primesLE P, (1 + fS n p) := by
    rw [sum_filter_add_sum_filter_not, sum_divisors_primorial]
  have hE := euler_ge_one hn hP
  have htail : |∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), fS n d| ≤
      Real.exp 8 / Real.sqrt P := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), |fS n d|
        ≤ ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), hS n d / Real.sqrt P := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter] at hd
          rw [hS_apply, le_div_iff₀ hsP]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Real.sqrt_le_sqrt (by exact_mod_cast (not_le.1 hd.2).le)
      _ ≤ ∑ d ∈ (primorial P).divisors, hS n d / Real.sqrt P := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _; rw [hS_apply]; positivity
      _ = (∏ p ∈ Nat.primesLE P, (1 + hS n p)) / Real.sqrt P := by
          rw [← sum_div, sum_divisors_hS]
      _ ≤ Real.exp 8 / Real.sqrt P := by
          apply div_le_div_of_nonneg_right (euler_hS_le n P) hsP.le
  set T := ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ d ≤ P), fS n d with hT
  set H := ∑ d ∈ (primorial P).divisors.filter (fun d => d ≤ P), fS n d with hH
  set E := ∏ p ∈ Nat.primesLE P, (1 + fS n p) with hEdef
  have h1 : T ≤ |T| := le_abs_self T
  have h2 : H = E - T := by linarith
  calc 1 - Real.exp 8 / Real.sqrt P ≤ E - |T| := by linarith
    _ ≤ E - T := by linarith
    _ = H := h2.symm

/-- The same for `𝔖_P(n)` itself: its real part, and it is real. -/
theorem singP_ge {n : ℕ} (hn : Odd n) {P : ℕ} (hP : 2 ≤ P) :
    ∃ s : ℝ, singP P n = (s : ℂ) ∧ 1 - Real.exp 8 / Real.sqrt P ≤ s :=
  ⟨_, singP_eq_fS P n, singP_fS_ge hn hP⟩

end LeanLab.PNTPort.Vinogradov

