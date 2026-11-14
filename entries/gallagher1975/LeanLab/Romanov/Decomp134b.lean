module

public import Mathlib
public import LeanLab.PNTSieve.MertensUpper

/-!
# Gallagher Lemma 7, truncating the reciprocal totient divisor expansion

Gallagher 1975, pages 135 and 136, the written proof of Lemma 7.
The existing cited statement is Linnik.Decomp1532a.lemma7.
The proof uses the odd divisor expansion, a logarithmic moment and a tail estimate.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section


noncomputable section
namespace LeanLab.Romanov.Decomp134b

open Finset Real

/-- The squarefree reciprocal totient weight in Lemma 7, page 135. -/
def totientWeight (q : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient

/-- The complete odd divisor mass in the proof on page 135. -/
def oddMass (n : ℕ) : ℝ := ∑ q ∈ n.divisors with Odd q, totientWeight q

/-- The logarithmic divisor moment on page 136. -/
def logMoment (n : ℕ) : ℝ := ∑ q ∈ n.divisors with Odd q, totientWeight q * log q

/-- Gallagher page 135, expand squarefree divisor weights as subsets of the prime factors. -/
theorem squarefree_divisor_expansion (n : ℕ) (hn : n ≠ 0) (F : ℕ → ℝ) :
    ∑ q ∈ n.divisors, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * F q =
      ∑ s ∈ n.primeFactors.powerset, F (∏ p ∈ s, p) := by
  have hsq (q : ℕ) : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 =
      if Squarefree q then 1 else 0 := by
    exact_mod_cast (ArithmeticFunction.moebius_sq (n := q))
  simp_rw [hsq, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, Nat.sum_divisors_filter_squarefree hn]
  simp only [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
  simp only [Finset.prod_val, Function.id_def]

/-- Gallagher page 135, reciprocal totients of products of distinct primes factor locally. -/
theorem inverse_totient_prime_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 : ℝ) / (Nat.totient (∏ p ∈ s, p) : ℝ) =
      ∏ p ∈ s, 1 / ((p : ℝ) - 1) := by
  have hprod : ∏ p ∈ s, p ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hs p hp).ne_zero)
  have hpf := Nat.primeFactors_prod hs
  have hphi : Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, hpf, Nat.div_self (Nat.pos_of_ne_zero hprod), one_mul]
  have hphiR : (Nat.totient (∏ p ∈ s, p) : ℝ) = ∏ p ∈ s, ((p : ℝ) - 1) := by
    rw [hphi, Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (hs p hp).one_le)
  rw [hphiR, one_div, ← prod_inv_distrib]
  simp only [one_div]


/-- Gallagher page 135, a product of distinct primes is odd exactly when two is absent. -/
theorem odd_prime_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Odd (∏ p ∈ s, p) ↔ 2 ∉ s := by
  have hprod : ∏ p ∈ s, p ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hs p hp).ne_zero)
  have hmem : 2 ∈ (∏ p ∈ s, p).primeFactors ↔ 2 ∣ ∏ p ∈ s, p := by
    constructor
    · exact Nat.dvd_of_mem_primeFactors
    · intro h
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h, hprod⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd, ← hmem, Nat.primeFactors_prod hs]


/-- Gallagher page 135, Euler product for n divided by phi of n. -/
theorem totient_ratio_eq_prod (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / n.totient = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hpred : ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    simpa only [Nat.cast_one] using Nat.cast_sub (R := ℝ) (Nat.prime_of_mem_primeFactors hp).one_le
  have hNat := Nat.totient_mul_prod_primeFactors n
  have hEq : (n.totient : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
      n * (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) hNat
    simp only [Nat.cast_mul] at h
    rw [hpred, Nat.cast_prod] at h
    exact h
  have hphi : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hB : 0 < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    apply prod_pos
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [prod_div_distrib, div_eq_div_iff hphi.ne' hB.ne']
  nlinarith [hEq]

/-- Gallagher pages 135 and 136, the odd squarefree divisor expansion with an arbitrary weight. -/
theorem odd_divisor_product_expansion (n : ℕ) (hn : n ≠ 0) (F : ℕ → ℝ) :
    ∑ q ∈ n.divisors with Odd q, totientWeight q * F q =
      ∑ s ∈ (n.primeFactors.erase 2).powerset,
        (∏ p ∈ s, 1 / ((p : ℝ) - 1)) * F (∏ p ∈ s, p) := by
  classical
  have hsprime (s : Finset ℕ) (hs : s ∈ n.primeFactors.powerset) : ∀ p ∈ s, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors ((mem_powerset.mp hs) hp)
  have hfilter : n.primeFactors.powerset.filter (fun s => 2 ∉ s) =
      (n.primeFactors.erase 2).powerset := by
    ext s
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨hs, h2⟩ p hp
      exact mem_erase.mpr ⟨fun h => h2 (h ▸ hp), hs hp⟩
    · intro hs
      exact ⟨fun p hp => (mem_erase.mp (hs hp)).2,
        fun h => (mem_erase.mp (hs h)).1 rfl⟩
  calc ∑ q ∈ n.divisors with Odd q, totientWeight q * F q
      = ∑ q ∈ n.divisors, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 *
          (if Odd q then F q / (q.totient : ℝ) else 0) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro q _
        by_cases h : Odd q <;> simp only [h, ite_true, ite_false, totientWeight] <;> ring
    _ = ∑ s ∈ n.primeFactors.powerset,
        if Odd (∏ p ∈ s, p) then F (∏ p ∈ s, p) / Nat.totient (∏ p ∈ s, p) else 0 :=
          squarefree_divisor_expansion n hn _
    _ = ∑ s ∈ n.primeFactors.powerset,
        if 2 ∉ s then (∏ p ∈ s, 1 / ((p : ℝ) - 1)) * F (∏ p ∈ s, p) else 0 := by
          apply sum_congr rfl
          intro s hs
          simp only [odd_prime_product s (hsprime s hs)]
          by_cases h2 : 2 ∈ s
          · simp only [h2, not_true_eq_false, ite_false]
          · simp only [h2, not_false_eq_true, ite_true]
            rw [← inverse_totient_prime_product s (hsprime s hs)]
            ring
    _ = _ := by rw [← sum_filter, hfilter]

/-- Gallagher page 135, the complete odd divisor mass is its Euler product. -/
theorem oddMass_eq_prod (n : ℕ) (hn : n ≠ 0) :
    oddMass n = ∏ p ∈ n.primeFactors.erase 2, (1 + 1 / ((p : ℝ) - 1)) := by
  have h := odd_divisor_product_expansion n hn (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  exact h.trans (prod_one_add _).symm


/-- LEAF. Gallagher page 135, the first two displays in the proof of Lemma 7.
Removing the prime two costs at most the factor two. -/
theorem odd_mass_totient_le (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / n.totient ≤ 2 * oddMass n := by
  classical
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
    ring
  calc (n : ℝ) / n.totient = ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
        rw [totient_ratio_eq_prod n (by omega)]
        exact prod_congr rfl hlocal
    _ ≤ 2 * ∏ p ∈ n.primeFactors.erase 2, (1 + 1 / ((p : ℝ) - 1)) := by
        by_cases h2 : 2 ∈ n.primeFactors
        · nth_rw 1 [← insert_erase h2]
          rw [prod_insert (notMem_erase 2 n.primeFactors)]
          norm_num
        · rw [erase_eq_of_notMem h2]
          have h0 : 0 ≤ ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
            apply prod_nonneg
            intro p hp
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
            have : 0 < (p : ℝ) - 1 := by linarith
            positivity
          linarith
    _ = 2 * oddMass n := by rw [oddMass_eq_prod n (by omega)]

/-- Gallagher page 136, the finite weighted subset identity behind the logarithmic moment. -/
theorem weighted_powerset_sum (P : Finset ℕ) (a b : ℕ → ℝ) (ha : ∀ p ∈ P, 1 + a p ≠ 0) :
    ∑ s ∈ P.powerset, (∏ p ∈ s, a p) * (∑ p ∈ s, b p) =
      (∏ p ∈ P, (1 + a p)) * (∑ p ∈ P, (a p * b p) / (1 + a p)) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have haP : ∀ q ∈ P, 1 + a q ≠ 0 := fun q hq => ha q (mem_insert_of_mem hq)
    have hap : 1 + a p ≠ 0 := ha p (mem_insert_self p P)
    have hterm (s : Finset ℕ) (hs : s ∈ P.powerset) :
        (∏ q ∈ insert p s, a q) * (∑ q ∈ insert p s, b q) =
          (a p * b p) * (∏ q ∈ s, a q) + a p * ((∏ q ∈ s, a q) * (∑ q ∈ s, b q)) := by
      have hps : p ∉ s := fun h => hp ((mem_powerset.mp hs) h)
      rw [prod_insert hps, sum_insert hps]
      ring
    have hinsert : ∑ s ∈ P.powerset, (∏ q ∈ insert p s, a q) * (∑ q ∈ insert p s, b q) =
        (a p * b p) * (∏ q ∈ P, (1 + a q)) +
          a p * (∑ s ∈ P.powerset, (∏ q ∈ s, a q) * (∑ q ∈ s, b q)) := by
      rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum, ← prod_one_add]
    rw [sum_powerset_insert hp, hinsert, ih haP, prod_insert hp, sum_insert hp]
    field_simp [hap]
    ring


/-- LEAF. Gallagher page 136, the equality in the first display.
The logarithmic moment is the prime logarithmic mean times the complete mass. -/
theorem odd_log_moment_eq (n : ℕ) (hn : 3 ≤ n) :
    logMoment n = (∑ p ∈ n.primeFactors.erase 2, log p / p) * oddMass n := by
  classical
  let P := n.primeFactors.erase 2
  let a : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2
  have ha : ∀ p ∈ P, 1 + a p ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have : 0 < (p : ℝ) - 1 := by linarith
    exact ne_of_gt (show 0 < 1 + a p by dsimp [a]; positivity)
  have hlogprod (s : Finset ℕ) (hs : s ∈ P.powerset) :
      Real.log ((∏ p ∈ s, p : ℕ) : ℝ) = ∑ p ∈ s, Real.log p := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hprime p ((mem_powerset.mp hs) hp)).ne_zero
  have hratio (p : ℕ) (hp : p ∈ P) :
      (a p * Real.log p) / (1 + a p) = Real.log p / p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    dsimp [a]
    field_simp [show (p : ℝ) - 1 ≠ 0 by linarith, show (p : ℝ) ≠ 0 by linarith]
    ring
  calc logMoment n = ∑ s ∈ P.powerset, (∏ p ∈ s, a p) * Real.log (∏ p ∈ s, p : ℕ) :=
        odd_divisor_product_expansion n (by omega) (fun p : ℕ => Real.log p)
    _ = ∑ s ∈ P.powerset, (∏ p ∈ s, a p) * (∑ p ∈ s, Real.log p) := by
        apply sum_congr rfl
        intro s hs
        rw [hlogprod s hs]
    _ = (∏ p ∈ P, (1 + a p)) * (∑ p ∈ P, (a p * Real.log p) / (1 + a p)) :=
        weighted_powerset_sum P a (fun p : ℕ => Real.log p) ha
    _ = (∏ p ∈ P, (1 + a p)) * (∑ p ∈ P, Real.log p / p) := by
        congr 1
        exact sum_congr rfl hratio
    _ = (∑ p ∈ n.primeFactors.erase 2, Real.log p / p) * oddMass n := by
        rw [oddMass_eq_prod n (by omega)]
        ring

/-- Gallagher page 136, a radical divides n, so the sum of its prime logarithms is at most log n. -/
theorem prime_log_sum_le_log (n : ℕ) (hn : 0 < n) : ∑ p ∈ n.primeFactors, log p ≤ log n := by
  have hpf : ∀ p ∈ n.primeFactors, (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  calc ∑ p ∈ n.primeFactors, log p = log (∏ p ∈ n.primeFactors, (p : ℝ)) :=
        (log_prod (fun p hp => (hpf p hp).ne')).symm
    _ ≤ log n := log_le_log (prod_pos hpf) (by
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))


/-- Gallagher page 136, split the odd prime factors at log n. The lab constant eight absorbs the small primes. -/
theorem prime_log_mean_additive (n : ℕ) (hn : 3 ≤ n) :
    ∑ p ∈ n.primeFactors.erase 2, log p / p ≤ log (log n) + 8 := by
  classical
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 1 < log (n : ℝ) := by
    rw [lt_log_iff_exp_lt (by linarith)]
    have h := exp_one_lt_d9
    linarith
  set P := n.primeFactors.erase 2
  set Q : ℕ := ⌊log (n : ℝ)⌋₊
  have hQ : 1 ≤ Q := Nat.le_floor (a := log (n : ℝ)) (by simpa using hlogn.le)
  have hp (p : ℕ) (h : p ∈ P) : p.Prime := Nat.prime_of_mem_primeFactors (mem_erase.mp h).2
  have hsmall : ∑ p ∈ P with ((p : ℕ) : ℝ) ≤ log n, log p / p ≤ log (log n) + 7 := by
    calc ∑ p ∈ P with ((p : ℕ) : ℝ) ≤ log n, log p / p
        ≤ ∑ p ∈ Nat.primesLE Q, log p / p := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p h
            obtain ⟨hP, hcut⟩ := mem_filter.mp h
            exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hcut, hp p hP⟩
          · intro p h _
            have hprime := (Nat.mem_primesLE.mp h).2
            exact div_nonneg (log_nonneg (by exact_mod_cast hprime.one_le)) (by positivity)
      _ = LeanLab.PNTSieve.Mertens.C Q := (LeanLab.PNTSieve.Mertens.C_eq Q).symm
      _ ≤ log Q + 7 := LeanLab.PNTSieve.Mertens.C_le Q hQ
      _ ≤ log (log n) + 7 := by
          exact add_le_add (log_le_log (by exact_mod_cast (show 0 < Q by omega))
            (Nat.floor_le (by linarith))) le_rfl
  have htail : ∑ p ∈ P with ¬ ((p : ℕ) : ℝ) ≤ log n, log p / p ≤ 1 := by
    calc ∑ p ∈ P with ¬ ((p : ℕ) : ℝ) ≤ log n, log p / p
        ≤ ∑ p ∈ P with ¬ ((p : ℕ) : ℝ) ≤ log n, log p / log n := by
          apply sum_le_sum
          intro p h
          obtain ⟨hP, hcut⟩ := mem_filter.mp h
          apply div_le_div_of_nonneg_left
          · exact log_nonneg (by exact_mod_cast (hp p hP).one_le)
          · linarith
          · linarith
      _ = (∑ p ∈ P with ¬ ((p : ℕ) : ℝ) ≤ log n, log p) / log n := by rw [sum_div]
      _ ≤ (∑ p ∈ n.primeFactors, log p) / log n := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          apply sum_le_sum_of_subset_of_nonneg
          · intro p h
            exact (mem_erase.mp (mem_filter.mp h).1).2
          · intro p h _
            exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_le)
      _ ≤ log n / log n := div_le_div_of_nonneg_right (prime_log_sum_le_log n (by omega)) (by linarith)
      _ = 1 := div_self (by linarith)
  have hsplit := sum_filter_add_sum_filter_not P (fun p : ℕ => ((p : ℕ) : ℝ) ≤ log n) (fun p => log p / p)
  linarith


/-- The reciprocal totient weights are nonnegative, including the zero convention at q zero. -/
theorem totientWeight_nonneg (q : ℕ) : 0 ≤ totientWeight q := by
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- The complete divisor mass is nonnegative. -/
theorem oddMass_nonneg (n : ℕ) : 0 ≤ oddMass n :=
  sum_nonneg (fun q _ => totientWeight_nonneg q)

/-- Gallagher page 136, the logarithmic tail inequality before choosing y. -/
theorem log_tail_le (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) (y : ℝ) (hy : 1 < y) :
    log y * (∑ q ∈ T with y < ((q : ℕ) : ℝ), totientWeight q) ≤
      ∑ q ∈ T, totientWeight q * log q := by
  rw [sum_filter, mul_sum]
  apply sum_le_sum
  intro q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hT q hq
  have hlogq : 0 ≤ log ((q : ℕ) : ℝ) := log_nonneg hq1
  by_cases h : y < ((q : ℕ) : ℝ)
  · rw [ite_eq_left h]
    have hl : log y ≤ log ((q : ℕ) : ℝ) := log_le_log (by linarith) h.le
    nlinarith [mul_le_mul_of_nonneg_left hl (totientWeight_nonneg q)]
  · rw [ite_eq_right h, mul_zero]
    exact mul_nonneg (totientWeight_nonneg q) hlogq

/-- The logarithmic scale used in the printed proof is positive for every n at least three. -/
theorem loglog_pos (n : ℕ) (hn : 3 ≤ n) : 0 < log (log n) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < log (n : ℝ) := by
    rw [lt_log_iff_exp_lt (by linarith)]
    have h := exp_one_lt_d9
    linarith
  exact log_pos hlog

/-- LEAF. Gallagher page 136, the final inequality in the first display.
This standard elementary prime sum bound is uniform over the prime factors of n. -/
theorem prime_log_mean : ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 3 ≤ n →
    ∑ p ∈ n.primeFactors.erase 2, log p / p ≤ A * log (log n) := by
  have hb : 0 < log (log (3 : ℝ)) := loglog_pos 3 (by decide)
  refine ⟨1 + 8 / log (log (3 : ℝ)), by positivity, fun n hn => ?_⟩
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have hmono : log (log (3 : ℝ)) ≤ log (log n) :=
    log_le_log hlog3 (log_le_log (by norm_num) hnR)
  have h := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 8 / log (log (3 : ℝ)) by positivity)
  have heq : (8 / log (log (3 : ℝ))) * log (log (3 : ℝ)) = 8 := div_mul_cancel₀ _ hb.ne'
  have hsum := prime_log_mean_additive n hn
  nlinarith


/-- Gallagher pages 135 and 136, Lemma 7. Assembly from the three proved leaves.
The statement repeats the existing cited statement without changing its quantifiers. -/
theorem lemma7 : ∃ d : ℕ, ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
    (n : ℝ) / n.totient ≤
      C * ∑ q ∈ n.divisors.filter (fun q : ℕ => Odd q ∧ (q : ℝ) ≤ Real.log n ^ d),
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient := by
  classical
  obtain ⟨A, hA, hmean⟩ := prime_log_mean
  obtain ⟨d, hd⟩ := exists_nat_gt (2 * A)
  refine ⟨d, 4, fun n hn => ?_⟩
  have hll := loglog_pos n hn
  have hm0 := oddMass_nonneg n
  have hd0 : (0 : ℝ) < d := by linarith
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 1 < log (n : ℝ) := (log_pos_iff (log_nonneg (by linarith))).mp hll
  set y : ℝ := log n ^ d with hydef
  have hy : 1 < y := one_lt_pow₀ hlogn (by exact_mod_cast hd0.ne')
  set T : Finset ℕ := n.divisors.filter Odd
  set tail : ℝ := ∑ q ∈ T with y < ((q : ℕ) : ℝ), totientWeight q
  set short : ℝ := ∑ q ∈ T with ((q : ℕ) : ℝ) ≤ y, totientWeight q
  have ht0 : 0 ≤ tail := sum_nonneg (fun q _ => totientWeight_nonneg q)
  have hT : ∀ q ∈ T, 1 ≤ q := by
    intro q hq
    exact Nat.pos_of_mem_divisors (mem_filter.mp hq).1
  have ht : log y * tail ≤ logMoment n := log_tail_le T hT y hy
  have hmoment : logMoment n ≤ A * log (log n) * oddMass n := by
    rw [odd_log_moment_eq n hn]
    exact mul_le_mul_of_nonneg_right (hmean n hn) hm0
  have hlogy : log y = d * log (log n) := by rw [hydef, log_pow]
  have hdt : (d : ℝ) * tail ≤ A * oddMass n := by
    have h := ht.trans hmoment
    rw [hlogy] at h
    have h' : log (log n) * ((d : ℝ) * tail) ≤ log (log n) * (A * oddMass n) := by
      nlinarith [h]
    exact (mul_le_mul_iff_right₀ hll).mp h'
  have hhalf : 2 * tail ≤ oddMass n := by nlinarith
  have hsplit : short + tail = oddMass n := by
    have h := sum_filter_add_sum_filter_not T (fun q => ((q : ℕ) : ℝ) ≤ y) totientWeight
    simpa only [not_le, short, tail, oddMass, T] using h
  have hsmall : oddMass n ≤ 2 * short := by linarith
  have hshort : short = ∑ q ∈ n.divisors.filter
      (fun q : ℕ => Odd q ∧ ((q : ℕ) : ℝ) ≤ log n ^ d),
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient := by
    dsimp [short, T, y, totientWeight]
    rw [filter_filter]
  rw [← hshort]
  exact (odd_mass_totient_le n hn).trans (by linarith)

end LeanLab.Romanov.Decomp134b
