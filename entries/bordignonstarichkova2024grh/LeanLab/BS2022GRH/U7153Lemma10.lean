module

public import Mathlib

/-!
BS2022GRH, P0021, unit U-7153: Lemma 10 of arXiv v1, Lemma 9 of the journal version,
Chen [Theorem 10.2], the weighted sieve inequality

  π₂(N) > S(A,P,z) − 1/2 Σ_{z ≤ q < y} S(A_q,P,z) − 1/2 S(B,P,y) − 2N^{7/8} − N^{1/3},

with z = N^{1/8}, y = N^{1/3}, ℙ = {p ∤ N}, A = {N − p : p ≤ N, p ∈ ℙ}, A_q = {a ∈ A : q ∣ a},
B = {N − p₁p₂p₃ : z ≤ p₁ < y ≤ p₂ ≤ p₃, p₁p₂p₃ < N, (p₁p₂p₃, N) = 1}, S(X,ℙ,w) the number of
elements of X with no prime factor p < w, p ∈ ℙ, as on journal page 1227, and π₂(N) the number of primes p < N with N − p a
prime or a product of two primes. Proved here for every natural N ≥ 2^24, elementary,
no sieve and no GRH: Chen's weights 1 − 1/2 #{q ∣ a, z ≤ q < y} − 1/2 [a = p₁p₂p₃] and the
switching a = N − p ↦ N − p₁p₂p₃ = p.

AI-written Lean code, Claude, session MANUAL-N1, unit U-7153. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.U7153
open Real Finset Classical

/-- `a` has no prime factor below `x`, i.e. `(a, P(x)) = 1`. -/
def NoSmall (x : ℝ) (a : ℕ) : Prop := ∀ r : ℕ, r.Prime → (r : ℝ) < x → ¬ r ∣ a

/-- `z = N^{1/8}`. -/
noncomputable def zz (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)
/-- `y = N^{1/3}`. -/
noncomputable def yy (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)

/-- `a` has no prime factor `r < x` with `r ∤ N`, i.e. `(a, P(x)) = 1` for
`P(x) = ∏_{p < x, p ∈ ℙ} p`, `ℙ = {p ∤ N}`, as on the journal page 1227. -/
def NoSmallP (n : ℕ) (x : ℝ) (a : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → (r : ℝ) < x → ¬ r ∣ n → ¬ r ∣ a

/-- `A = {N − p : p ≤ N, p ∈ ℙ}`, `ℙ` the primes `p ∤ N`. -/
noncomputable def Aset (n : ℕ) : Finset ℕ :=
  ((range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n)).image (fun p => n - p)

/-- `S(A,P,z)`. -/
noncomputable def SA (n : ℕ) : ℕ := ((Aset n).filter (NoSmallP n (zz n))).card

/-- `S(A_q,P,z)`. -/
noncomputable def SAq (n q : ℕ) : ℕ :=
  ((Aset n).filter (fun a => q ∣ a ∧ NoSmallP n (zz n) a)).card

/-- The primes `q` with `z ≤ q < y`, all `≤ N`. -/
noncomputable def Qset (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun q => q.Prime ∧ zz n ≤ q ∧ (q : ℝ) < yy n)

/-- The triples `(p₁, p₂, p₃)` of primes defining `B`. -/
noncomputable def Triples (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((range n ×ˢ range n) ×ˢ range n).filter (fun t =>
    t.1.1.Prime ∧ t.1.2.Prime ∧ t.2.Prime ∧ zz n ≤ t.1.1 ∧ (t.1.1 : ℝ) < yy n ∧
    yy n ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧ t.1.1 * t.1.2 * t.2 < n ∧ Nat.Coprime (t.1.1 * t.1.2 * t.2) n)

/-- `B = {N − p₁p₂p₃ : z ≤ p₁ < y ≤ p₂ ≤ p₃, p₁p₂p₃ < N, (p₁p₂p₃, N) = 1}`. -/
noncomputable def Bset (n : ℕ) : Finset ℕ :=
  (Triples n).image (fun t => n - t.1.1 * t.1.2 * t.2)

/-- `S(B,P,y)`. -/
noncomputable def SB (n : ℕ) : ℕ := ((Bset n).filter (NoSmallP n (yy n))).card

/-- `m` is a prime or a product of two primes. -/
def IsP2 (m : ℕ) : Prop := m.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ m = p₁ * p₂

/-- `π₂(N)`: primes `p < N` with `N − p` a prime or a product of two primes. -/
noncomputable def pi2 (n : ℕ) : ℕ := ((range n).filter (fun p => p.Prime ∧ IsP2 (n - p))).card

/-- `a = p₁p₂p₃` with `z ≤ p₁ < y ≤ p₂ ≤ p₃`. -/
def IsB (z y : ℝ) (a : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z ≤ p₁ ∧ (p₁ : ℝ) < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
    a = p₁ * p₂ * p₃

/-! ### Real powers, `t = N^{1/24}` -/

lemma rpow_t {n : ℕ} (k : ℕ) (r : ℝ) (hr : r = k / 24) :
    (n : ℝ) ^ r = ((n : ℝ) ^ (1 / 24 : ℝ)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), hr]; ring_nf

/-! ### The pointwise weight inequality -/

lemma pointwise {z y : ℝ} {n a : ℕ} (hz : 2 < z) (hy1 : 1 ≤ y) (hyn : y ^ 3 = n) (han : a < n)
    (hC : NoSmall z a) (hsq : Squarefree a) (h1 : a ≠ 1) (hP2 : ¬ IsP2 a) :
    2 ≤ ((range (n + 1)).filter (fun q : ℕ => q.Prime ∧ z ≤ q ∧ (q : ℝ) < y ∧ q ∣ a)).card +
      (if IsB z y a then 1 else 0) := by
  have ha0 : a ≠ 0 := by
    rintro rfl; exact hC 2 Nat.prime_two (by norm_num; linarith) (dvd_zero _)
  set F := a.primeFactors with hF
  have hprod : (∏ p ∈ F, p : ℕ) = a := Nat.prod_primeFactors_of_squarefree hsq
  set Fs := F.filter (fun p : ℕ => (p : ℝ) < y)
  set Fb := F.filter (fun p : ℕ => ¬ (p : ℝ) < y)
  have hcard : Fs.card + Fb.card = F.card := Finset.card_filter_add_card_filter_not _
  have hsplit : (∏ p ∈ Fs, p : ℕ) * (∏ p ∈ Fb, p : ℕ) = a := by
    rw [Finset.prod_filter_mul_prod_filter_not]; exact hprod
  -- at most two large factors
  have hFb : Fb.card ≤ 2 := by
    by_contra hc
    push Not at hc
    have hdvd : (∏ p ∈ Fb, p : ℕ) ∣ a := ⟨_, by rw [← hsplit, mul_comm]⟩
    have hle : (∏ p ∈ Fb, p : ℕ) ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdvd
    have hge : y ^ Fb.card ≤ ((∏ p ∈ Fb, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, ← Finset.prod_const]
      apply Finset.prod_le_prod₀
      · intro _ _; linarith
      · intro p hp; exact not_lt.1 (Finset.mem_filter.1 hp).2
    have h3 : y ^ 3 ≤ y ^ Fb.card := pow_le_pow_right₀ hy1 hc
    have : (a : ℝ) < n := by exact_mod_cast han
    have : ((∏ p ∈ Fb, p : ℕ) : ℝ) ≤ a := by exact_mod_cast hle
    linarith
  -- at least three prime factors
  have hF3 : 3 ≤ F.card := by
    by_contra hc
    push Not at hc
    interval_cases hk : F.card
    · rw [Finset.card_eq_zero] at hk
      rw [hk, Finset.prod_empty] at hprod; exact h1 hprod.symm
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hk
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hp ▸ Finset.mem_singleton_self p)
      rw [hp, Finset.prod_singleton] at hprod
      exact hP2 (Or.inl (hprod ▸ hpp))
    · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.1 hk
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [← hF, hpq]; simp)
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [← hF, hpq]; simp)
      have : a = p * q := by
        rw [← hprod, hpq, Finset.prod_pair hne]
      exact hP2 (Or.inr ⟨p, q, hpp, hqp, this⟩)
  -- small factors lie in [z, y)
  have hsub : Fs ⊆ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧ z ≤ q ∧ (q : ℝ) < y ∧ q ∣ a) := by
    intro q hq
    obtain ⟨hqF, hqy⟩ := Finset.mem_filter.1 hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqF
    have hqa : q ∣ a := Nat.dvd_of_mem_primeFactors hqF
    have hqle : q ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hqa
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hqp, ?_, hqy, hqa⟩
    by_contra hlt; exact hC q hqp (not_le.1 hlt) hqa
  have hk := Finset.card_le_card hsub
  by_cases h2 : 2 ≤ Fs.card
  · omega
  · have hs1 : Fs.card = 1 := by omega
    have hb2 : Fb.card = 2 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hs1
    obtain ⟨u, v, huv, huvE⟩ := Finset.card_eq_two.1 hb2
    have hqFs : q ∈ Fs := by rw [hq]; exact Finset.mem_singleton_self q
    have huFb : u ∈ Fb := by rw [huvE]; simp
    have hvFb : v ∈ Fb := by rw [huvE]; simp
    have hqs := hsub hqFs
    obtain ⟨-, hqp, hzq, hqy, -⟩ := Finset.mem_filter.1 hqs
    obtain ⟨huF, huy⟩ := Finset.mem_filter.1 huFb
    obtain ⟨hvF, hvy⟩ := Finset.mem_filter.1 hvFb
    have hup : u.Prime := Nat.prime_of_mem_primeFactors huF
    have hvp : v.Prime := Nat.prime_of_mem_primeFactors hvF
    have haE : a = q * u * v := by
      rw [← hsplit, hq, huvE, Finset.prod_singleton, Finset.prod_pair huv, mul_assoc]
    have hB : IsB z y a := by
      rcases le_total u v with h | h
      · exact ⟨q, u, v, hqp, hup, hvp, hzq, hqy, not_lt.1 huy, h, haE⟩
      · exact ⟨q, v, u, hqp, hvp, hup, hzq, hqy, not_lt.1 hvy, h, by rw [haE]; ring⟩
    rw [if_pos hB]; omega

/-! ### Counting -/

lemma mem_Aset {n a : ℕ} : a ∈ Aset n ↔ ∃ p, p ≤ n ∧ p.Prime ∧ ¬ p ∣ n ∧ a = n - p := by
  simp only [Aset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨p, ⟨hp, hpp, hpn⟩, rfl⟩; exact ⟨p, by omega, hpp, hpn, rfl⟩
  · rintro ⟨p, hp, hpp, hpn, rfl⟩; exact ⟨p, ⟨by omega, hpp, hpn⟩, rfl⟩

/-- On `A`, sifting by `ℙ = {p ∤ N}` is sifting by all primes. -/
lemma noSmallP_iff_A {n a : ℕ} (x : ℝ) (h : a ∈ Aset n) : NoSmallP n x a ↔ NoSmall x a := by
  obtain ⟨p, hp, hpp, hpn, rfl⟩ := mem_Aset.1 h
  refine ⟨fun H r hr hrx hra => ?_, fun H r hr hrx _ => H r hr hrx⟩
  by_cases hrn : r ∣ n
  · have hrp : r ∣ p := by
      have := Nat.dvd_sub hrn hra
      rwa [show n - (n - p) = p by omega] at this
    exact hpn ((Nat.prime_dvd_prime_iff_eq hr hpp).1 hrp ▸ hrn)
  · exact H r hr hrx hrn hra

/-- On `B`, sifting by `ℙ = {p ∤ N}` is sifting by all primes. -/
lemma noSmallP_iff_B {n b : ℕ} (x : ℝ) (h : b ∈ Bset n) : NoSmallP n x b ↔ NoSmall x b := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
  obtain ⟨-, -, -, -, -, -, -, -, hlt, hcop⟩ := Finset.mem_filter.1 ht
  refine ⟨fun H r hr hrx hra => ?_, fun H r hr hrx _ => H r hr hrx⟩
  by_cases hrn : r ∣ n
  · have hrm : r ∣ t.1.1 * t.1.2 * t.2 := by
      have := Nat.dvd_sub hrn hra
      rwa [show n - (n - t.1.1 * t.1.2 * t.2) = t.1.1 * t.1.2 * t.2 by omega] at this
    exact hr.ne_one (Nat.dvd_one.1 (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd hrm hrn))
  · exact H r hr hrx hrn hra

lemma SA_eq (n : ℕ) : SA n = ((Aset n).filter (NoSmall (zz n))).card := by
  unfold SA; congr 1; exact Finset.filter_congr (fun a ha => noSmallP_iff_A _ ha)

lemma SAq_eq (n q : ℕ) : SAq n q = ((Aset n).filter (fun a => q ∣ a ∧ NoSmall (zz n) a)).card := by
  unfold SAq; congr 1
  exact Finset.filter_congr (fun a ha => and_congr_right fun _ => noSmallP_iff_A _ ha)

lemma SB_eq (n : ℕ) : SB n = ((Bset n).filter (NoSmall (yy n))).card := by
  unfold SB; congr 1; exact Finset.filter_congr (fun a ha => noSmallP_iff_B _ ha)

/-- `C`, the elements of `A` with no prime factor below `z`. -/
noncomputable def Cset (n : ℕ) : Finset ℕ := (Aset n).filter (NoSmall (zz n))

/-- The number of primes `q ∣ a` with `z ≤ q < y`. -/
noncomputable def kq (n a : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun q : ℕ => q.Prime ∧ zz n ≤ q ∧ (q : ℝ) < yy n ∧ q ∣ a)).card

lemma sum_SAq (n : ℕ) : ∑ q ∈ Qset n, SAq n q = ∑ a ∈ Cset n, kq n a := by
  calc ∑ q ∈ Qset n, SAq n q = ∑ q ∈ Qset n, ∑ a ∈ Cset n, (if q ∣ a then 1 else 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_boole, Cset, Finset.filter_filter, SAq_eq]
        simp only [Nat.cast_id]
        congr 1; exact Finset.filter_congr (fun a _ => and_comm)
    _ = ∑ a ∈ Cset n, ∑ q ∈ Qset n, (if q ∣ a then 1 else 0) := Finset.sum_comm
    _ = ∑ a ∈ Cset n, kq n a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_boole, Qset, Finset.filter_filter, kq]
        simp only [Nat.cast_id]
        congr 1; exact Finset.filter_congr (fun q _ => by simp only [and_assoc])

lemma lt_of_mem_Aset {n a : ℕ} (h : a ∈ Aset n) : a < n := by
  obtain ⟨p, hp, hpp, -, rfl⟩ := mem_Aset.1 h
  have := hpp.two_le; omega

/-- The weighted sum, pointwise inequality summed over `C`. -/
lemma weighted_sum {n : ℕ} (hz : 2 < zz n) (hy1 : 1 ≤ yy n) (hyn : yy n ^ 3 = n) :
    ((Cset n).card : ℝ) - 1 / 2 * ∑ a ∈ Cset n, (kq n a : ℝ)
        - 1 / 2 * ((Cset n).filter (IsB (zz n) (yy n))).card ≤
      ((Cset n).filter IsP2).card + ((Cset n).filter (fun a => ¬ Squarefree a)).card +
        ((Cset n).filter (fun a => a = 1)).card := by
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_boole,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨hA, hC⟩ := Finset.mem_filter.1 ha
  have han := lt_of_mem_Aset hA
  have hk0 : (0 : ℝ) ≤ kq n a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ if IsB (zz n) (yy n) a then 1 else 0 := by split_ifs <;> norm_num
  by_cases h1 : IsP2 a
  · rw [if_pos h1]; push_cast
    have : (0 : ℝ) ≤ (if ¬ Squarefree a then 1 else 0) := by split_ifs <;> norm_num
    have : (0 : ℝ) ≤ (if a = 1 then 1 else 0) := by split_ifs <;> norm_num
    linarith
  by_cases h2 : ¬ Squarefree a
  · rw [if_pos h2]; push_cast
    have : (0 : ℝ) ≤ (if IsP2 a then 1 else 0) := by split_ifs <;> norm_num
    have : (0 : ℝ) ≤ (if a = 1 then 1 else 0) := by split_ifs <;> norm_num
    linarith
  by_cases h3 : a = 1
  · rw [if_pos h3]; push_cast
    have : (0 : ℝ) ≤ (if IsP2 a then 1 else 0) := by split_ifs <;> norm_num
    have : (0 : ℝ) ≤ (if ¬ Squarefree a then 1 else 0) := by split_ifs <;> norm_num
    linarith
  rw [if_neg h1, if_neg h2, if_neg h3]
  have hp := pointwise hz hy1 hyn han hC (not_not.1 h2) h3 h1
  have hp' : (2 : ℝ) ≤ (kq n a : ℝ) + (if IsB (zz n) (yy n) a then 1 else 0) := by
    have : ((2 : ℕ) : ℝ) ≤ ((kq n a + (if IsB (zz n) (yy n) a then 1 else 0) : ℕ) : ℝ) := by
      exact_mod_cast hp
    push_cast at this; split_ifs at this ⊢ <;> linarith
  split_ifs at hp' ⊢ <;> push_cast <;> linarith

lemma card_P2_le (n : ℕ) : ((Cset n).filter IsP2).card ≤ pi2 n := by
  unfold pi2
  apply Finset.card_le_card_of_injOn (fun a => n - a)
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    obtain ⟨ha, hP⟩ := ha
    obtain ⟨p, hp, hpp, -, rfl⟩ := mem_Aset.1 (Finset.mem_filter.1 ha).1
    have h0 : n - p ≠ 0 := by
      intro h; rw [h] at hP
      rcases hP with h | ⟨p₁, p₂, h₁, h₂, h⟩
      · exact Nat.not_prime_zero h
      · rcases Nat.mul_eq_zero.1 h.symm with h | h
        · exact Nat.not_prime_zero (h ▸ h₁)
        · exact Nat.not_prime_zero (h ▸ h₂)
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨by omega, by rwa [show n - (n - p) = p by omega], by rwa [show n - (n - (n - p)) = n - p by omega]⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    have := lt_of_mem_Aset (Finset.mem_filter.1 ha.1).1
    have := lt_of_mem_Aset (Finset.mem_filter.1 hb.1).1
    simp only at hab; omega

lemma card_one_le (n : ℕ) : ((Cset n).filter (fun a => a = 1)).card ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb => by
    rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]

/-- Telescoping, `Σ_{M ≤ m < K} 1/((m − 1)m) ≤ 1/(M − 1)`. -/
lemma tele (M : ℕ) (hM : 2 ≤ M) (K : ℕ) :
    ∑ m ∈ Ico M K, (1 : ℝ) / (((m : ℝ) - 1) * m) ≤ 1 / ((M : ℝ) - 1) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  rcases lt_or_ge K M with hK | hK
  · rw [Finset.Ico_eq_empty_of_le hK.le, Finset.sum_empty]
    exact le_of_lt (by apply div_pos <;> linarith)
  have key : ∀ K, M ≤ K → ∑ m ∈ Ico M K, (1 : ℝ) / (((m : ℝ) - 1) * m) =
      1 / ((M : ℝ) - 1) - 1 / ((K : ℝ) - 1) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => simp
    | succ K hK ih =>
      rw [Finset.sum_Ico_succ_top hK, ih]
      have hK1 : (1 : ℝ) < K := by
        have : (M : ℝ) ≤ K := by exact_mod_cast hK
        linarith
      push_cast
      have h0 : (K : ℝ) ≠ 0 := by linarith
      have h1 : (K : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (M : ℝ) - 1 ≠ 0 := by linarith
      rw [show (K : ℝ) + 1 - 1 = K by ring]
      field_simp
      ring
  rw [key K hK]
  have hK1 : (1 : ℝ) < K := by
    have : (M : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have : 0 < 1 / ((K : ℝ) - 1) := by apply div_pos <;> linarith
  linarith

lemma card_nsq_le {n : ℕ} (hz : 2 < zz n) :
    (((Cset n).filter (fun a => ¬ Squarefree a)).card : ℝ) ≤ n / (zz n - 1) := by
  set M := ⌈zz n⌉₊
  have hzM : zz n ≤ M := Nat.le_ceil _
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) < M := lt_of_lt_of_le hz hzM
    exact_mod_cast this.le
  have hsub : (Cset n).filter (fun a => ¬ Squarefree a) ⊆
      (Ico M (n + 1)).biUnion (fun m => (Ioc 0 n).filter (fun a => m * m ∣ a)) := by
    intro a ha
    obtain ⟨haC, hns⟩ := Finset.mem_filter.1 ha
    obtain ⟨hA, hC⟩ := Finset.mem_filter.1 haC
    have han := lt_of_mem_Aset hA
    have ha0 : a ≠ 0 := by
      rintro rfl; exact hC 2 Nat.prime_two (by norm_num; linarith) (dvd_zero _)
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push Not at hns
    obtain ⟨r, hr, hrr⟩ := hns
    have hra : r ∣ a := Dvd.dvd.trans (Dvd.intro r rfl) hrr
    have hrz : zz n ≤ r := by
      by_contra h; exact hC r hr (not_le.1 h) hra
    have hrM : M ≤ r := Nat.ceil_le.2 hrz
    have hrle : r ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hra
    simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨r, ⟨hrM, by omega⟩, ⟨by omega, by omega⟩, hrr⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := Ico M (n + 1))
    (t := fun m => (Ioc 0 n).filter (fun a => m * m ∣ a))
  simp only [Nat.Ioc_filter_dvd_card_eq_div] at h2
  have h3 : (((Cset n).filter (fun a => ¬ Squarefree a)).card : ℝ) ≤
      ∑ m ∈ Ico M (n + 1), ((n / (m * m) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast h1.trans h2
  have h4 : ∑ m ∈ Ico M (n + 1), ((n / (m * m) : ℕ) : ℝ) ≤
      ∑ m ∈ Ico M (n + 1), (n : ℝ) * (1 / (((m : ℝ) - 1) * m)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hmM : M ≤ m := (Finset.mem_Ico.1 hm).1
    have hm1 : (1 : ℝ) < m := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hM2.trans hmM
      linarith
    refine (Nat.cast_div_le).trans ?_
    push_cast
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by nlinarith)
    nlinarith
  have h5 := tele M hM2 (n + 1)
  rw [← Finset.mul_sum] at h4
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h6 : (n : ℝ) * (1 / ((M : ℝ) - 1)) ≤ n / (zz n - 1) := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hn0 (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left h5 hn0
  linarith

/-- The switching step: elements `N − p = p₁p₂p₃` of `C` map to `p ∈ B` with no prime factor
below `y`, except when `p < y` or `p ∣ N`. -/
lemma card_T_le {n : ℕ} (hn0 : 0 < n) (hy0 : 0 < yy n) :
    (((Cset n).filter (IsB (zz n) (yy n))).card : ℝ) ≤ SB n + (yy n + 1) + n / yy n := by
  set T := (Cset n).filter (IsB (zz n) (yy n))
  set good : ℕ → Prop := fun a => ¬ (n - a) ∣ n ∧ yy n ≤ ((n - a : ℕ) : ℝ)
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) good
  have hg : (T.filter good).card ≤ SB n := by
    rw [SB_eq]
    apply Finset.card_le_card_of_injOn (fun a => n - a)
    · intro a ha
      rw [Finset.mem_coe] at ha
      obtain ⟨haT, hgd⟩ := Finset.mem_filter.1 ha
      obtain ⟨haC, hB⟩ := Finset.mem_filter.1 haT
      obtain ⟨hA, -⟩ := Finset.mem_filter.1 haC
      have han := lt_of_mem_Aset hA
      obtain ⟨p, hp, hpp, -, hap⟩ := mem_Aset.1 hA
      have hnp : n - a = p := by omega
      obtain ⟨p₁, p₂, p₃, h₁, h₂, h₃, hz1, hy1, hy2, h23, haE⟩ := hB
      have ha0 : a ≠ 0 := by
        rw [haE]; exact Nat.mul_ne_zero (Nat.mul_ne_zero h₁.ne_zero h₂.ne_zero) h₃.ne_zero
      have hd1 : p₁ ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨p₂ * p₃, by rw [haE]; ring⟩
      have hd2 : p₂ ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨p₁ * p₃, by rw [haE]; ring⟩
      have hd3 : p₃ ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨p₁ * p₂, by rw [haE]; ring⟩
      have hcop : Nat.Coprime (p₁ * p₂ * p₃) n := by
        rw [← haE, hap, Nat.coprime_self_sub_left hp]
        exact (Nat.Prime.coprime_iff_not_dvd hpp).2 (by rw [← hnp]; exact hgd.1)
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨Finset.mem_image.2 ⟨((p₁, p₂), p₃), Finset.mem_filter.2 ⟨?_, h₁, h₂, h₃, hz1, hy1,
        hy2, h23, by rw [← haE]; exact han, hcop⟩, by rw [← haE]⟩, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]; omega
      · intro r hr hry hrd
        rw [hnp] at hrd
        have hgd2 : yy n ≤ (p : ℝ) := by have := hgd.2; rwa [hnp] at this
        have := (Nat.prime_dvd_prime_iff_eq hr hpp).1 hrd
        subst this; linarith
    · intro a ha b hb hab
      have := lt_of_mem_Aset (Finset.mem_filter.1 (Finset.mem_filter.1
        (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1).1).1
      have := lt_of_mem_Aset (Finset.mem_filter.1 (Finset.mem_filter.1
        (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1).1).1
      simp only at hab; omega
  set D := (range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n ∧ yy n ≤ p)
  have hb : (T.filter (fun a => ¬ good a)).card ≤ (range ⌈yy n⌉₊ ∪ D).card := by
    apply Finset.card_le_card_of_injOn (fun a => n - a)
    · intro a ha
      rw [Finset.mem_coe] at ha
      obtain ⟨haT, hgd⟩ := Finset.mem_filter.1 ha
      obtain ⟨haC, -⟩ := Finset.mem_filter.1 haT
      obtain ⟨hA, -⟩ := Finset.mem_filter.1 haC
      obtain ⟨p, hp, hpp, -, hap⟩ := mem_Aset.1 hA
      have hnp : n - a = p := by omega
      have hgd' : ¬ (¬ p ∣ n ∧ yy n ≤ (p : ℝ)) := fun h =>
        hgd (by show ¬ (n - a) ∣ n ∧ yy n ≤ ((n - a : ℕ) : ℝ); rw [hnp]; exact h)
      rw [Finset.mem_coe, Finset.mem_union]
      show n - a ∈ range ⌈yy n⌉₊ ∨ n - a ∈ D
      rw [hnp]
      by_cases hpy : (p : ℝ) < yy n
      · exact Or.inl (Finset.mem_range.2 (Nat.lt_ceil.2 hpy))
      · right
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hpp, ?_, not_lt.1 hpy⟩
        by_contra hd; exact hgd' ⟨hd, not_lt.1 hpy⟩
    · intro a ha b hb hab
      have := lt_of_mem_Aset (Finset.mem_filter.1 (Finset.mem_filter.1
        (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1).1).1
      have := lt_of_mem_Aset (Finset.mem_filter.1 (Finset.mem_filter.1
        (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1).1).1
      simp only at hab; omega
  have hD : D.card ≤ ⌊(n : ℝ) / yy n⌋₊ := by
    have := Finset.card_le_card_of_injOn (s := D) (t := Icc 1 ⌊(n : ℝ) / yy n⌋₊) (fun p => n / p)
      ?_ ?_
    · simpa using this
    · intro p hp
      simp only [D, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp
      obtain ⟨-, hpp, hpn, hyp⟩ := hp
      simp only [Finset.coe_Icc, Set.mem_Icc]
      have hple : p ≤ n := Nat.le_of_dvd hn0 hpn
      refine ⟨Nat.div_pos hple hpp.pos, Nat.le_floor ?_⟩
      rw [Nat.cast_div hpn (by exact_mod_cast hpp.ne_zero)]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hy0 hyp
    · intro p hp q hq hpq
      simp only [D, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp hq
      simp only at hpq
      rw [← Nat.div_div_self hp.2.2.1 hn0.ne', hpq, Nat.div_div_self hq.2.2.1 hn0.ne']
  have hU := Finset.card_union_le (range ⌈yy n⌉₊) D
  rw [Finset.card_range] at hU
  have hc1 : (⌈yy n⌉₊ : ℝ) < yy n + 1 := Nat.ceil_lt_add_one hy0.le
  have hc2 : (⌊(n : ℝ) / yy n⌋₊ : ℝ) ≤ n / yy n := Nat.floor_le (by positivity)
  have e1 : (T.card : ℝ) = (T.filter good).card + (T.filter (fun a => ¬ good a)).card := by
    exact_mod_cast hsplit.symm
  have e2 : ((T.filter good).card : ℝ) ≤ SB n := by exact_mod_cast hg
  have e3 : ((T.filter (fun a => ¬ good a)).card : ℝ) ≤ ⌈yy n⌉₊ + ⌊(n : ℝ) / yy n⌋₊ := by
    exact_mod_cast hb.trans (hU.trans (by omega))
  linarith

/-! ### Lemma 10 -/

/-- **Lemma 10 of arXiv v1, Lemma 9 of the journal, Chen [Theorem 10.2], PROVED** for every
natural `N ≥ 2^24`, with `z = N^{1/8}`, `y = N^{1/3}`:
`π₂(N) > S(A,P,z) − 1/2 Σ_{z ≤ q < y} S(A_q,P,z) − 1/2 S(B,P,y) − 2N^{7/8} − N^{1/3}`. -/
theorem lemma10 (n : ℕ) (hn : (2 : ℝ) ^ 24 ≤ n) :
    (SA n : ℝ) - 1 / 2 * ∑ q ∈ Qset n, (SAq n q : ℝ) - 1 / 2 * (SB n : ℝ)
      - 2 * (n : ℝ) ^ (7 / 8 : ℝ) - (n : ℝ) ^ (1 / 3 : ℝ) < pi2 n := by
  set t := (n : ℝ) ^ (1 / 24 : ℝ) with ht
  have hn24 : (n : ℝ) = t ^ 24 := by rw [← rpow_t 24 1 (by norm_num), Real.rpow_one]
  have hz : zz n = t ^ 3 := rpow_t 3 _ (by norm_num)
  have hy : yy n = t ^ 8 := rpow_t 8 _ (by norm_num)
  have h78 : (n : ℝ) ^ (7 / 8 : ℝ) = t ^ 21 := rpow_t 21 _ (by norm_num)
  have h13 : (n : ℝ) ^ (1 / 3 : ℝ) = t ^ 8 := rpow_t 8 _ (by norm_num)
  have ht0 : 0 ≤ t := by positivity
  have ht2 : 2 ≤ t := by
    by_contra h
    have : t ^ 24 < 2 ^ 24 := pow_lt_pow_left₀ (not_le.1 h) ht0 (by norm_num)
    linarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith [show (0 : ℝ) < 2 ^ 24 by norm_num]
    exact_mod_cast this
  have ht3 : 8 ≤ t ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 3]
  have hzz : 2 < zz n := by rw [hz]; linarith
  have hy1 : 1 ≤ yy n := by rw [hy]; exact one_le_pow₀ (by linarith)
  have hyn : yy n ^ 3 = n := by rw [hy, hn24]; ring
  have hy0 : 0 < yy n := by linarith
  have hW := weighted_sum hzz hy1 hyn
  have hP : (((Cset n).filter IsP2).card : ℝ) ≤ pi2 n := by exact_mod_cast card_P2_le n
  have h1 : (((Cset n).filter (fun a => a = 1)).card : ℝ) ≤ 1 := by exact_mod_cast card_one_le n
  have hNS := card_nsq_le hzz
  have hT := card_T_le hn0 hy0
  have hK : ∑ q ∈ Qset n, (SAq n q : ℝ) = ∑ a ∈ Cset n, (kq n a : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_SAq]
  have hSA : (SA n : ℝ) = (Cset n).card := by rw [SA_eq]; rfl
  rw [hK, hSA, h78, h13]
  rw [hz, hn24] at hNS
  have hq : t ^ 24 / (t ^ 3 - 1) ≤ 8 / 7 * t ^ 21 := by
    rw [div_le_iff₀ (by linarith)]
    have : t ^ 24 = t ^ 21 * t ^ 3 := by ring
    nlinarith [pow_nonneg ht0 21]
  have hq2 : (n : ℝ) / yy n = t ^ 16 := by
    rw [hy, hn24, div_eq_iff (by positivity)]; ring
  rw [hq2] at hT
  have h16 : 1 ≤ t ^ 16 := one_le_pow₀ (by linarith)
  have h21 : 32 * t ^ 16 ≤ t ^ 21 := by
    have : t ^ 21 = t ^ 16 * t ^ 5 := by ring
    rw [this]
    have : (32 : ℝ) ≤ t ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 5]
    nlinarith
  linarith


end LeanLab.BS2022GRH.U7153
