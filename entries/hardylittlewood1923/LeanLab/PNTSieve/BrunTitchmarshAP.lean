module

public import LeanLab.PNTSieve.BrunTitchmarsh
public import LeanLab.PNTPort.BVMax.CoprimeHarm

/-!
# Brun-Titchmarsh in arithmetic progressions

Lab proof, unit U-5305, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code, on the Selberg sieve
ported from PrimeNumberTheoremAnd in this folder. Known mathematics, Titchmarsh 1930, with the
constant 2 of Montgomery-Vaughan 1973 in the main term.

`brunTitchmarsh_ap`: for `x, y > 0`, `z > 1`, `q ≥ 1` and any `a`,
`#{p prime : x ≤ p ≤ x + y, p ≡ a mod q} ≤ 2y/(φ(q) log z) + 4z(1 + log z)³`.
Sieve the integers of `[x, x + y]` in the class `a mod q` by the primes `p ≤ z` with `p ∤ q`;
the Selberg bounding sum is at least `Σ_{m ≤ √z, (m,q)=1} 1/m ≥ (φ(q)/q) log √z` by
`BVMax.coprime_harm_ge`, and every remainder is at most `3` in absolute value by the Chinese
remainder theorem and an exact count of a residue class in an interval.
-/

@[expose] public section


open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open scoped ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section

section BoundingSum
open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
namespace LeanLab.PNTSieve.Sieve

/-- Adapted from `selbergBoundingSum_ge_sum_div` in SelbergBounds.lean, ported from
PrimeNumberTheoremAnd, Apache 2.0, by Arend Mellendijk; CLOUD 20261019T0814Z-cloud20 changed the sum
to a filtered range whose members have all prime factors dividing the sifting product. -/
theorem boundingSum_ge_sum_filter (s : SelbergSieve) (P : ℕ → Prop)
  (hP : ∀ m, P m → ∀ p : ℕ, p.Prime → p ∣ m → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    (selbergBoundingSum s) ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter P, s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter P, s.nu m := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hm, hmP⟩ := hm
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · exact hP m hmP p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

open ArithmeticFunction in
/-- `rem_sum_le_of_const` of SelbergBounds.lean with the remainder bound asked only at divisors of
the sifting product. -/
theorem rem_sum_le_of_const_dvd (s : SelbergSieve) (C : ℝ)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    exact hrem d (Finset.mem_filter.mp hd).1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1,
      hrem 1 (Nat.one_mem_divisors.mpr prodPrimes_ne_zero)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

end LeanLab.PNTSieve.Sieve
end BoundingSum

namespace LeanLab.PNTSieve.BrunTitchmarshAP

open Finset

/-- Exact count of a residue class in `[A, B]` up to `2`. -/
lemma card_Icc_modEq (A B c m : ℕ) (hm : 0 < m) (hAB : A ≤ B + 1) :
    |(((Icc A B).filter (fun n => n ≡ c [MOD m])).card : ℝ) - ((B : ℝ) + 1 - A) / m| ≤ 2 := by
  have hsplit : ((range (B + 1)).filter (fun n => n ≡ c [MOD m])).card =
      ((range A).filter (fun n => n ≡ c [MOD m])).card +
        ((Icc A B).filter (fun n => n ≡ c [MOD m])).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      rw [← filter_union]; congr 1
      ext n; simp only [mem_range, mem_union, mem_Icc]; omega
    · rw [disjoint_left]; intro n h1 h2
      simp only [mem_filter, mem_range, mem_Icc] at h1 h2; omega
  have hc1 := Nat.count_modEq_card (B + 1) hm c
  have hc2 := Nat.count_modEq_card A hm c
  rw [Nat.count_eq_card_filter_range] at hc1 hc2
  rw [hc1, hc2] at hsplit
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set K := ((Icc A B).filter (fun n => n ≡ c [MOD m])).card
  have hK : (K : ℝ) = ((B + 1) / m : ℕ) - ((A / m : ℕ) : ℝ) +
      ((if c % m < (B + 1) % m then 1 else 0 : ℕ) : ℝ) -
      ((if c % m < A % m then 1 else 0 : ℕ) : ℝ) := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hsplit
    push_cast at this ⊢
    linarith
  have f1 : (((B + 1) / m : ℕ) : ℝ) ≤ ((B : ℝ) + 1) / m := by
    have := Nat.cast_div_le (α := ℝ) (m := B + 1) (n := m); push_cast at this; exact this
  have f2 : ((B : ℝ) + 1) / m - 1 < (((B + 1) / m : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add hm (a := B + 1)
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hm']
    have : ((B + 1 : ℕ) : ℝ) < (((B + 1) / m : ℕ) : ℝ) * m + m := by exact_mod_cast h
    push_cast at this; linarith
  have g1 : ((A / m : ℕ) : ℝ) ≤ (A : ℝ) / m := Nat.cast_div_le
  have g2 : (A : ℝ) / m - 1 < ((A / m : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add hm (a := A)
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hm']
    have : (A : ℝ) < ((A / m : ℕ) : ℝ) * m + m := by exact_mod_cast h
    linarith
  have i1 : (0 : ℝ) ≤ ((if c % m < (B + 1) % m then 1 else 0 : ℕ) : ℝ) ∧
      ((if c % m < (B + 1) % m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by split_ifs <;> norm_num
  have i2 : (0 : ℝ) ≤ ((if c % m < A % m then 1 else 0 : ℕ) : ℝ) ∧
      ((if c % m < A % m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by split_ifs <;> norm_num
  have e : ((B : ℝ) + 1 - A) / m = ((B : ℝ) + 1) / m - (A : ℝ) / m := by ring
  rw [abs_le, e, hK]
  constructor <;> linarith [i1.1, i1.2, i2.1, i2.2]

/-- The Chinese remainder step: for `(q, d) = 1`, `d ∣ n ∧ n ≡ a (q)` is one class mod `qd`. -/
lemma crt_class (q d a : ℕ) (hqd : Nat.Coprime q d) : ∃ c : ℕ, ∀ n : ℕ,
    (d ∣ n ∧ n % q = a % q) ↔ n ≡ c [MOD q * d] := by
  obtain ⟨c, hcq, hcd⟩ := Nat.chineseRemainder hqd a 0
  refine ⟨c, fun n => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hqd]
  constructor
  · rintro ⟨hdn, hnq⟩
    exact ⟨(show n ≡ a [MOD q] from hnq).trans hcq.symm,
      ((Nat.modEq_zero_iff_dvd.mpr hdn)).trans hcd.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.modEq_zero_iff_dvd.mp (h2.trans hcd), h1.trans hcq⟩

/-- The primes `p ≤ z` with `p ∤ q`. -/
def coprimePrimes (q : ℕ) (z : ℝ) : Finset ℕ :=
  (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q)

lemma coprimePrimes_prime {q : ℕ} {z : ℝ} {p : ℕ} (hp : p ∈ coprimePrimes q z) : p.Prime :=
  (mem_filter.mp hp).2.1

/-- Sifting the integers of `[x, x + y]` in the class `a mod q` by the primes `p ≤ z`, `p ∤ q`. -/
def apSieve (x y z : ℝ) (q a : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := Icc ⌈x⌉₊ ⌊x + y⌋₊
  prodPrimes := ∏ p ∈ coprimePrimes q z, p
  prodPrimes_squarefree := prodDistinctPrimes_squarefree _ (fun _ hp => coprimePrimes_prime hp)
  weights := fun n => if n % q = a % q then 1 else 0
  weights_nonneg := fun n => by split_ifs <;> norm_num
  totalMass := y / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

variable (x y z : ℝ) (q a : ℕ)

lemma dvd_prod_coprimePrimes {d : ℕ} (hd : d ∣ ∏ p ∈ coprimePrimes q z, p) : Nat.Coprime q d := by
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro k hk hkd hkq
  obtain ⟨r, hr, hkr⟩ := (Prime.dvd_finsetProd_iff hk.prime _).mp (hkd.trans hd)
  have := (Nat.prime_dvd_prime_iff_eq hk (coprimePrimes_prime hr)).mp hkr
  subst this
  exact (mem_filter.mp hr).2.2 hkq

/-- Every remainder of `apSieve` at a divisor of the sifting product is at most `3`. -/
lemma abs_rem_le (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z) (hq : 0 < q) {d : ℕ}
    (hd : d ∈ (apSieve x y z q a hz).prodPrimes.divisors) :
    |rem (s := (apSieve x y z q a hz).toBoundingSieve) d| ≤ 3 := by
  have hdP : d ∣ ∏ p ∈ coprimePrimes q z, p := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors hd)
  obtain ⟨c, hc⟩ := crt_class q d a (dvd_prod_coprimePrimes z q hdP)
  have hqd : 0 < q * d := Nat.mul_pos hq (Nat.pos_of_ne_zero hd0)
  have hA : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  have hAB : ⌈x⌉₊ ≤ ⌊x + y⌋₊ + 1 := by
    have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
    have h2 : x + y - 1 < (⌊x + y⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have : (⌈x⌉₊ : ℝ) < ⌊x + y⌋₊ + 2 := by linarith
    have h : ⌈x⌉₊ < ⌊x + y⌋₊ + 2 := by exact_mod_cast this
    omega
  have hcount := card_Icc_modEq ⌈x⌉₊ ⌊x + y⌋₊ c (q * d) hqd hAB
  have hms : multSum (s := (apSieve x y z q a hz).toBoundingSieve) d =
      (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => n ≡ c [MOD q * d])).card : ℝ) := by
    unfold multSum
    simp only [apSieve]
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun n _ => ?_)
    have := hc n
    by_cases h1 : d ∣ n <;> by_cases h2 : n % q = a % q <;> simp_all
  have hnu : (apSieve x y z q a hz).nu d * (apSieve x y z q a hz).totalMass = y / (q * d) := by
    simp only [apSieve, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hd0, ↓reduceIte, Nat.cast_one, ArithmeticFunction.id_apply]
    field_simp
  unfold rem
  rw [hms, hnu]
  have hqd' : (0 : ℝ) < (q : ℝ) * d := by exact_mod_cast hqd
  have hqd1 : (1 : ℝ) ≤ (q : ℝ) * d := by exact_mod_cast hqd
  have hlen : |((⌊x + y⌋₊ : ℝ) + 1 - ⌈x⌉₊) - y| ≤ 1 := by
    have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
    have h1' : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have h2 : x + y - 1 < (⌊x + y⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have h2' : (⌊x + y⌋₊ : ℝ) ≤ x + y := Nat.floor_le (by linarith)
    rw [abs_le]; constructor <;> linarith
  have hlen' : |((⌊x + y⌋₊ : ℝ) + 1 - ⌈x⌉₊) / ((q * d : ℕ) : ℝ) - y / (q * d)| ≤ 1 := by
    push_cast
    rw [← sub_div, abs_div, abs_of_pos hqd', div_le_one hqd']
    linarith
  push_cast at hcount
  calc _ = |((((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => n ≡ c [MOD q * d])).card : ℝ) -
        ((⌊x + y⌋₊ : ℝ) + 1 - ⌈x⌉₊) / ((q : ℝ) * d)) +
        (((⌊x + y⌋₊ : ℝ) + 1 - ⌈x⌉₊) / ((q : ℝ) * d) - y / (q * d))| := by ring_nf
    _ ≤ 2 + 1 := by
        refine (abs_add_le _ _).trans (add_le_add hcount ?_)
        push_cast at hlen'; exact hlen'
    _ = 3 := by norm_num

/-- Brun-Titchmarsh in arithmetic progressions: for `x, y > 0`, `z > 1`, `q ≥ 1` and any `a`,
`#{p prime : x ≤ p ≤ x + y, p ≡ a mod q} ≤ 2y/(φ(q) log z) + 4z(1 + log z)³`. -/
theorem brunTitchmarsh_ap (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) (hq : 0 < q) :
    (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      2 * y / (q.totient * Real.log z) + 4 * z * (1 + Real.log z) ^ 3 := by
  classical
  set s := apSieve x y z q a hz.le with hs
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  set P := ∏ p ∈ coprimePrimes q z, p with hPdef
  -- (i) primes in the class are sifted survivors or at most z
  have hsift : siftedSum (s := s.toBoundingSieve) =
      (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => Nat.Coprime P n ∧ n % q = a % q)).card : ℝ) := by
    unfold siftedSum
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun n _ => ?_)
    simp only [hs, apSieve]
    by_cases h1 : Nat.Coprime P n <;> by_cases h2 : n % q = a % q <;> simp_all [hPdef]
  have hsub : (Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p % q = a % q) ⊆
      (Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => Nat.Coprime P n ∧ n % q = a % q) ∪ Icc 1 ⌊z⌋₊ := by
    intro p hp
    simp only [mem_filter] at hp
    rw [mem_union]
    by_cases hpz : p ≤ ⌊z⌋₊
    · right; rw [mem_Icc]; exact ⟨hp.2.1.one_lt.le, hpz⟩
    · left
      simp only [mem_filter]
      refine ⟨hp.1, ?_, hp.2.2⟩
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.2.1]
      intro hdvd
      obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.2.1.prime _).mp hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp.2.1 (coprimePrimes_prime hr)).mp hpr
      subst this
      have := (mem_filter.mp hr).1
      rw [mem_range] at this
      omega
  have hcount : (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      siftedSum (s := s.toBoundingSieve) + z := by
    rw [hsift]
    have h1 := card_le_card hsub
    have h2 := card_union_le ((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => Nat.Coprime P n ∧ n % q = a % q))
      (Icc 1 ⌊z⌋₊)
    have h3 : ((Icc 1 ⌊z⌋₊).card : ℝ) ≤ z := by
      rw [Nat.card_Icc, add_tsub_cancel_right]; exact Nat.floor_le hz0.le
    have : (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
        (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => Nat.Coprime P n ∧ n % q = a % q)).card : ℝ) +
        ((Icc 1 ⌊z⌋₊).card : ℝ) := by exact_mod_cast h1.trans h2
    linarith
  -- (ii) the Selberg bound
  have hsel := LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple s
  -- (iii) the bounding sum
  have hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id := rfl
  have hbs := LeanLab.PNTSieve.Sieve.boundingSum_ge_sum_filter s
    (fun m => 1 ≤ m ∧ Nat.Coprime m q ∧ m ≤ ⌊Real.sqrt z⌋₊)
    (by
      intro m hm p hp hpm
      have hm1 : 1 ≤ m := hm.1
      replace hm := hm.2
      have hpm' : p ≤ m := Nat.le_of_dvd hm1 hpm
      have hmz : (m : ℝ) ≤ z := by
        have : (m : ℝ) ≤ ⌊Real.sqrt z⌋₊ := by exact_mod_cast hm.2
        exact this.trans ((Nat.floor_le (Real.sqrt_nonneg z)).trans
          (LeanLab.PNTSieve.Sieve.sqrt_le_self z hz.le))
      have hpz : p ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast (show (p : ℝ) ≤ z by
        exact (by exact_mod_cast hpm' : (p : ℝ) ≤ m).trans hmz))
      have hpq : ¬ p ∣ q := by
        intro h
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpm hm.1) h
      exact dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpq⟩))
    (by rw [hnu]; exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id)
    (by
      intro n; rw [hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp [h]
      simp)
    (by
      intro p hpp _
      rw [hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [ite_eq_right, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero)
  have hfilt : ∑ m ∈ (Icc 1 ⌊Real.sqrt s.level⌋₊).filter
        (fun m => 1 ≤ m ∧ Nat.Coprime m q ∧ m ≤ ⌊Real.sqrt z⌋₊), s.nu m =
      ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m := by
    have hl : s.level = z := rfl
    rw [hl]
    apply sum_congr
    · ext m; simp only [mem_filter, mem_Icc]; constructor
      · rintro ⟨⟨h1, h2⟩, _, h3, _⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h1, h3, h2⟩
    · intro m hm
      simp only [mem_filter, mem_Icc] at hm
      rw [hnu]
      simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
        ArithmeticFunction.id_apply]
  have hharm := LeanLab.PNTPort.BVMax.coprime_harm_ge q ⌊Real.sqrt z⌋₊ hq
  have hlogsq : Real.log z / 2 ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℝ) + 1) := by
    rw [← Real.log_sqrt hz0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hz0) (Nat.lt_floor_add_one _).le
  have hS : (q.totient : ℝ) / q * (Real.log z / 2) ≤ selbergBoundingSum s := by
    have h1 : (q.totient : ℝ) / q * (Real.log z / 2) ≤
        (q.totient : ℝ) / q * Real.log ((⌊Real.sqrt z⌋₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlogsq (by positivity)
    have h2 : ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m ≤
        selbergBoundingSum s := by
      have := hbs
      rw [ge_iff_le] at this
      convert this using 1
      convert hfilt.symm using 3
    linarith
  have hSpos : 0 < (q.totient : ℝ) / q * (Real.log z / 2) := by positivity
  have hmain : s.totalMass / selbergBoundingSum s ≤ 2 * y / (q.totient * Real.log z) := by
    have hX : s.totalMass = y / q := rfl
    rw [hX]
    calc y / q / selbergBoundingSum s ≤ y / q / ((q.totient : ℝ) / q * (Real.log z / 2)) :=
          div_le_div_of_nonneg_left (by positivity) hSpos hS
      _ = 2 * y / (q.totient * Real.log z) := by field_simp
  -- (iv) the remainders
  have herr := LeanLab.PNTSieve.Sieve.rem_sum_le_of_const_dvd s 3
    (fun d hd => abs_rem_le x y z q a hx hy hz.le hq hd)
  have hl : s.level = z := rfl
  rw [hl] at herr
  have hsel' : siftedSum (s := s.toBoundingSieve) ≤ s.totalMass / selbergBoundingSum s +
      3 * z * (1 + Real.log z) ^ 3 := hsel.trans (add_le_add le_rfl herr)
  have hz3 : z ≤ z * (1 + Real.log z) ^ 3 := by
    apply le_mul_of_one_le_right hz0.le
    exact one_le_pow₀ (by linarith)
  linarith

end LeanLab.PNTSieve.BrunTitchmarshAP

