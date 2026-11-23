module

public import Mathlib

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.

This file contains the standard divisor extraction step of the van der Corput 1939 and
Landreau 1989 argument for divisor sums over polynomial values, used here in place of the
cited Nair 1992 sieve: every m >= 1 has coprime d1, d2 with d2 squarefree, d1^r * d2 dividing m,
(d1 * d2)^r <= m and tau(m) <= r^r * tau(d1 * d2)^(r^2).

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Nair103

/-- From a finite set of positive naturals with at least `r * t` elements one can pick `t`
elements whose product, raised to the power `r`, is at most the product of the whole set. -/
theorem exists_subset_prod_pow_le (r : ℕ) (hr : 1 ≤ r) :
    ∀ (t : ℕ) (S : Finset ℕ), (∀ x ∈ S, 1 ≤ x) → r * t ≤ S.card →
      ∃ T ⊆ S, T.card = t ∧ (∏ x ∈ T, x) ^ r ≤ ∏ x ∈ S, x := by
  intro t
  induction t with
  | zero =>
    intro S hS _
    refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
    rw [Finset.prod_empty, one_pow]
    exact Nat.succ_le_of_lt (Finset.prod_pos fun x hx => hS x hx)
  | succ t ih =>
    intro S hS hcard
    have hmul : r * (t + 1) = r * t + r := by ring
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨a, haS, hamin⟩ : ∃ a ∈ S, ∀ x ∈ S, a ≤ x :=
      ⟨S.min' hne, S.min'_mem hne, fun x hx => S.min'_le x hx⟩
    have hcE : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem haS
    obtain ⟨R, hRsub, hRcard⟩ :=
      Finset.exists_subset_card_eq (s := S.erase a) (n := r - 1) (by omega)
    have hcD : ((S.erase a) \ R).card + R.card = (S.erase a).card :=
      Finset.card_sdiff_add_card_eq_card hRsub
    obtain ⟨T', hT'sub, hT'card, hT'prod⟩ := ih ((S.erase a) \ R)
      (fun x hx => hS x (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hx).1)) (by omega)
    have haT' : a ∉ T' := fun h =>
      Finset.notMem_erase a S (Finset.mem_sdiff.mp (hT'sub h)).1
    refine ⟨insert a T', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hx
      · rw [hxa]; exact haS
      · exact Finset.mem_of_mem_erase (Finset.mem_sdiff.mp (hT'sub hx)).1
    · rw [Finset.card_insert_of_notMem haT', hT'card]
    · have e1 : a * ∏ x ∈ S.erase a, x = ∏ x ∈ S, x :=
        Finset.mul_prod_erase S (fun x => x) haS
      have e2 : (∏ x ∈ (S.erase a) \ R, x) * ∏ x ∈ R, x = ∏ x ∈ S.erase a, x :=
        Finset.prod_sdiff hRsub
      have hR : a ^ (r - 1) ≤ ∏ x ∈ R, x := by
        have h : ∏ _x ∈ R, a ≤ ∏ x ∈ R, x :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
            (fun x hx => hamin x (Finset.mem_of_mem_erase (hRsub hx)))
        rwa [Finset.prod_const, hRcard] at h
      have har : a ^ r = a * a ^ (r - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [Finset.prod_insert haT', mul_pow, ← e1, ← e2, har]
      calc a * a ^ (r - 1) * (∏ x ∈ T', x) ^ r
          ≤ a * (∏ x ∈ R, x) * ∏ x ∈ (S.erase a) \ R, x :=
            Nat.mul_le_mul (Nat.mul_le_mul_left a hR) hT'prod
        _ = a * ((∏ x ∈ (S.erase a) \ R, x) * ∏ x ∈ R, x) := by ring

/-- A prime power is coprime to a product of powers of other primes. -/
theorem coprime_prime_pow_prod (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (e : ℕ → ℕ) (a k : ℕ)
    (ha : a.Prime) (haQ : a ∉ Q) : Nat.Coprime (a ^ k) (∏ p ∈ Q, p ^ e p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes ha (hQ p hp)).2 (fun h => haQ (h ▸ hp))

/-- Divisor count of a product of powers of distinct primes. -/
theorem card_divisors_prod_prime_pow (e : ℕ → ℕ) :
    ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∏ p ∈ Q, p ^ e p).divisors.card = ∏ p ∈ Q, (e p + 1) := by
  intro Q
  induction Q using Finset.induction_on with
  | empty => intro _; simp
  | insert a s has ih =>
    intro hQ
    have ha : a.Prime := hQ a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hQ p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert has, Finset.prod_insert has,
      Nat.Coprime.card_divisors_mul (coprime_prime_pow_prod s hs e a (e a) ha has), ih hs,
      Nat.divisors_prime_pow ha, Finset.card_map, Finset.card_range]

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes :
    ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → Squarefree (∏ p ∈ Q, p) := by
  intro Q
  induction Q using Finset.induction_on with
  | empty => intro _; rw [Finset.prod_empty]; exact squarefree_one
  | insert a s has ih =>
    intro hQ
    have ha : a.Prime := hQ a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hQ p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert has, Nat.squarefree_mul_iff]
    refine ⟨?_, (Nat.prime_iff.mp ha).squarefree, ih hs⟩
    apply Nat.Coprime.prod_right
    intro p hp
    exact (Nat.coprime_primes ha (hs p hp)).2 (fun h => has (h ▸ hp))

theorem divisor_extract (r : ℕ) (hr : 2 ≤ r) (m : ℕ) (hm : 1 ≤ m) :
    ∃ d₁ d₂ : ℕ, Nat.Coprime d₁ d₂ ∧ Squarefree d₂ ∧ d₁ ^ r * d₂ ∣ m ∧ (d₁ * d₂) ^ r ≤ m ∧
      m.divisors.card ≤ r ^ r * (d₁ * d₂).divisors.card ^ (r ^ 2) := by
  have hm0 : m ≠ 0 := by omega
  have hr0 : 0 < r := by omega
  have hPprime : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hmprod : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m :=
    (Nat.prod_factorization_eq_prod_primeFactors (n := m) (fun p k => p ^ k)).symm.trans
      (Nat.prod_factorization_pow_eq_self hm0)
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ,
      S = m.primeFactors.filter (fun p => m.factorization p < r) := ⟨_, rfl⟩
  have hSsub : S ⊆ m.primeFactors := by rw [hSdef]; exact Finset.filter_subset _ _
  have hSlt : ∀ p ∈ S, m.factorization p < r := by
    intro p hp
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = S.card / r := ⟨_, rfl⟩
  obtain ⟨T, hTS, hTcard, hTprod⟩ := exists_subset_prod_pow_le r (by omega) t S
    (fun x hx => (hPprime x (hSsub hx)).one_lt.le) (by rw [htdef]; exact Nat.mul_div_le S.card r)
  obtain ⟨d₁, hd1⟩ : ∃ d₁ : ℕ, d₁ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p / r) :=
    ⟨_, rfl⟩
  -- coprimality of d₁ with any product over a subset of S
  have hcopU : ∀ U ⊆ S, Nat.Coprime d₁ (∏ q ∈ U, q) := by
    intro U hU
    rw [hd1]
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    by_cases hpq : p = q
    · have hlt : m.factorization p < r := by rw [hpq]; exact hSlt q (hU hq)
      rw [Nat.div_eq_of_lt hlt, pow_zero]
      exact Nat.coprime_one_left _
    · exact Nat.Coprime.pow_left _
        ((Nat.coprime_primes (hPprime p hp) (hPprime q (hSsub (hU hq)))).2 hpq)
  have hd1r : d₁ ^ r ∣ m := by
    have h := Finset.prod_dvd_prod_of_dvd (s := m.primeFactors)
      (fun p => (p ^ (m.factorization p / r)) ^ r) (fun p => p ^ m.factorization p)
      (fun p _ => by
        show (p ^ (m.factorization p / r)) ^ r ∣ p ^ m.factorization p
        rw [← pow_mul]
        exact pow_dvd_pow p (Nat.div_mul_le_self _ _))
    rw [Finset.prod_pow, hmprod, ← hd1] at h
    exact h
  have hd2U : ∀ U ⊆ S, (∏ q ∈ U, q) ∣ m := fun U hU =>
    (Finset.prod_dvd_prod_of_subset U m.primeFactors (fun q => q) (hU.trans hSsub)).trans
      (Nat.prod_primeFactors_dvd m)
  have hdvdU : ∀ U ⊆ S, d₁ ^ r * (∏ q ∈ U, q) ∣ m := fun U hU =>
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left r (hcopU U hU)) hd1r (hd2U U hU)
  have hr2 : r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
  -- pointwise bound on the divisor count factors
  have hpt : ∀ p ∈ m.primeFactors, m.factorization p + 1 ≤
      (if m.factorization p < r then r else 1) * (m.factorization p / r + 1) ^ (r ^ 2) := by
    intro p _
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, zero_add, one_pow, mul_one]
      omega
    · rw [one_mul]
      have hq : 1 ≤ m.factorization p / r := (Nat.one_le_div_iff hr0).2 (not_lt.mp h)
      have hmod := Nat.div_add_mod (m.factorization p) r
      have hlt := Nat.mod_lt (m.factorization p) hr0
      generalize m.factorization p / r = q at hq hmod ⊢
      have h1 : m.factorization p + 1 ≤ r * (q + 1) := by
        rw [mul_add, mul_one]
        omega
      have hg2 : 2 ≤ q + 1 := by omega
      have h2 : r ≤ (q + 1) ^ r := hr2.trans (Nat.pow_le_pow_left hg2 r)
      have h3 : r + 1 ≤ r ^ 2 := by nlinarith
      calc m.factorization p + 1 ≤ r * (q + 1) := h1
        _ ≤ (q + 1) ^ r * (q + 1) := Nat.mul_le_mul_right _ h2
        _ = (q + 1) ^ (r + 1) := (pow_succ _ _).symm
        _ ≤ (q + 1) ^ (r ^ 2) := Nat.pow_le_pow_right (by omega) h3
  have hSprod : ∏ p ∈ m.primeFactors, (if m.factorization p < r then r else 1) = r ^ S.card := by
    rw [hSdef, ← Finset.prod_const]
    exact (Finset.prod_filter (fun p => m.factorization p < r) (fun _ => r)).symm
  have hrS : r ^ S.card ≤ r ^ r * (2 ^ t) ^ (r ^ 2) := by
    have h1 := Nat.div_add_mod S.card r
    have h2 := Nat.mod_lt S.card hr0
    rw [← htdef] at h1
    have hlt : S.card ≤ r * t + r := by omega
    calc r ^ S.card ≤ r ^ (r * t + r) := Nat.pow_le_pow_right hr0 hlt
      _ = r ^ r * r ^ (r * t) := by rw [pow_add, mul_comm]
      _ ≤ r ^ r * (2 ^ r) ^ (r * t) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr2 _)
      _ = r ^ r * (2 ^ t) ^ (r ^ 2) := by
        rw [← pow_mul, ← pow_mul]
        have he : r * (r * t) = t * r ^ 2 := by ring
        rw [he]
  have hτm : m.divisors.card = ∏ p ∈ m.primeFactors, (m.factorization p + 1) :=
    Nat.card_divisors hm0
  have hτ1 : d₁.divisors.card = ∏ p ∈ m.primeFactors, (m.factorization p / r + 1) := by
    rw [hd1]
    exact card_divisors_prod_prime_pow (fun p => m.factorization p / r) m.primeFactors hPprime
  have hτ2 : (∏ q ∈ T, q).divisors.card = 2 ^ t := by
    have h := card_divisors_prod_prime_pow (fun _ => 1) T
      (fun p hp => hPprime p (hSsub (hTS hp)))
    simp only [pow_one, Nat.reduceAdd, Finset.prod_const, hTcard] at h
    exact h
  refine ⟨d₁, ∏ q ∈ T, q, hcopU T hTS,
    squarefree_prod_primes T (fun p hp => hPprime p (hSsub (hTS hp))), hdvdU T hTS, ?_, ?_⟩
  · rw [mul_pow]
    calc d₁ ^ r * (∏ q ∈ T, q) ^ r ≤ d₁ ^ r * ∏ q ∈ S, q := Nat.mul_le_mul_left _ hTprod
      _ ≤ m := Nat.le_of_dvd (by omega) (hdvdU S (Finset.Subset.refl S))
  · rw [Nat.Coprime.card_divisors_mul (hcopU T hTS), hτm, hτ1, hτ2]
    calc ∏ p ∈ m.primeFactors, (m.factorization p + 1)
        ≤ ∏ p ∈ m.primeFactors, ((if m.factorization p < r then r else 1) *
            (m.factorization p / r + 1) ^ (r ^ 2)) :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) hpt
      _ = r ^ S.card * (∏ p ∈ m.primeFactors, (m.factorization p / r + 1)) ^ (r ^ 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hSprod]
      _ ≤ r ^ r * (2 ^ t) ^ (r ^ 2) *
            (∏ p ∈ m.primeFactors, (m.factorization p / r + 1)) ^ (r ^ 2) :=
          Nat.mul_le_mul_right _ hrS
      _ = r ^ r * ((∏ p ∈ m.primeFactors, (m.factorization p / r + 1)) * 2 ^ t) ^ (r ^ 2) := by
          rw [mul_pow]; ring

end LeanLab.Perelli1996.Nair103
