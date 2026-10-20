module

public import LeanLab.ChenExplicit.Statements

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
The combinatorial skeleton of Bordignon, Johnston, Starichkova, arXiv 2207.09452 (P0009), v6:
Lemma 37, quoted there from Nathanson, Additive Number Theory: The Classical Bases, Theorem 10.2,
  "π₂(N) > S(A, P(z)) − (1/2) Σ_{z⩽q<y, q∤N} S(A_q, P(z)) − (1/2) S(B, P(y)) − 2N^{7/8} − N^{1/3}",
with the sets of equations (104)-(109):
  (104) z = N^{1/8}, y = N^{1/3};
  (105) A := {N − p : p ⩽ N, p ∤ N}, A_p := {a ∈ A : p ∣ a};
  (108) B := {N − p₁p₂p₃ : z ⩽ p₁ < y ⩽ p₂ ⩽ p₃, p₁p₂p₃ < N, (p₁p₂p₃, N) = 1};
  (109) P(x) := ∏_{p<x, p∤N} p.
BJS do not reprove Lemma 37. Its proof, in Nathanson, is the pointwise Chen weighting:
for `n = N − p` sifted by `P(z)`, `1 − k(n)/2 − j(n)/2 ≤ [Ω n ≤ 2]` unless `n` is not squarefree,
where `k(n)` counts primes `q ∣ n` with `z ⩽ q < y` and `j(n) = 1` iff `n = p₁p₂p₃` as in (108).
Everything here is PROVED, no sorry and no axiom beyond Lean's standard three. All counts are
`Finset` cardinalities; `z, y` are real.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega Classical

noncomputable section
namespace LeanLab.ChenExplicit

/-- `k(m)`: the number of primes `q ∣ m` with `z ⩽ q < y`. Summed over the sifted set this is
`Σ_{z⩽q<y} S(A_q, P(z))`. -/
def kCount (z y : ℝ) (m : ℕ) : ℕ := #(m.primeFactors.filter fun q : ℕ => z ≤ (q : ℝ) ∧ (q : ℝ) < y)

/-- `m = p₁p₂p₃` with `z ⩽ p₁ < y ⩽ p₂ ⩽ p₃`, the shape of the elements switched to `B`, (108). -/
def IsChenTriple (z y : ℝ) (m : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z ≤ p₁ ∧ (p₁ : ℝ) < y ∧ y ≤ p₂ ∧
    p₂ ≤ p₃ ∧ m = p₁ * p₂ * p₃

lemma card_big_le_two {y : ℝ} {m : ℕ} (hsq : Squarefree m) (hy : (m : ℝ) < y ^ 3) :
    #(m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ)) ≤ 2 := by
  by_contra h
  push Not at h
  set B := (m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ))
  have hm0 : m ≠ 0 := hsq.ne_zero
  have hy1 : 1 < y := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    by_contra hc; push Not at hc
    have : y ^ 3 ≤ 1 := by
      rcases le_or_gt 0 y with h0 | h0
      · exact pow_le_one₀ h0 hc
      · nlinarith [sq_nonneg y]
    linarith
  have hdvd : (∏ q ∈ B, q : ℕ) ∣ m := by
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
  have hle : ((∏ q ∈ B, q : ℕ) : ℝ) ≤ m := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  have hge : y ^ #B ≤ ((∏ q ∈ B, q : ℕ) : ℝ) := by
    push_cast
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun q hq => (mem_filter.mp hq).2)
  have : y ^ 3 ≤ y ^ #B := pow_le_pow_right₀ hy1.le h
  linarith

/-- **Pointwise Chen weight inequality.** If every prime factor of `m ≠ 0` is at least `z` and
`m < y³`, then `1 − k(m)/2 − j(m)/2 ≤ [Ω m ≤ 2] + [m not squarefree]`. This is the step in the
proof of Nathanson's Theorem 10.2, BJS Lemma 37, that holds for each element `n = N − p` of `A`.
Proof: at most two prime factors are `⩾ y` since `m < y³`; if `Ω m ⩾ 3` and `m` is squarefree,
then either `k(m) ⩾ 2`, or `k(m) = 1` and `m = p₁p₂p₃`, `j(m) = 1`. -/
theorem chen_weight (z y : ℝ) (m : ℕ) (hm0 : m ≠ 0) (hz : ∀ q ∈ m.primeFactors, z ≤ (q : ℝ))
    (hy : (m : ℝ) < y ^ 3) :
    1 - (kCount z y m : ℝ) / 2 - (if IsChenTriple z y m then 1 else 0) / 2 ≤
      (if Ω m ≤ 2 then 1 else 0) + (if Squarefree m then 0 else 1) := by
  have hj0 : (0 : ℝ) ≤ (if IsChenTriple z y m then 1 else 0) := by split_ifs <;> norm_num
  have hk0 : (0 : ℝ) ≤ kCount z y m := by positivity
  by_cases hsq : Squarefree m
  swap
  · simp only [hsq, ite_false]; split_ifs <;> linarith
  simp only [hsq, ite_true, add_zero]
  by_cases hΩ : Ω m ≤ 2
  · simp only [hΩ, ite_true]; linarith
  simp only [hΩ, ite_false]
  -- now `m` is squarefree with at least three prime factors
  have hωΩ : ω m = Ω m := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
    hm0).mpr hsq
  have hcard : #m.primeFactors = ω m := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]
  have h3 : 3 ≤ #m.primeFactors := by omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := m.primeFactors) (fun q : ℕ => (q : ℝ) < y)
  have hbig := card_big_le_two (y := y) hsq hy
  have hbig' : #(m.primeFactors.filter fun q : ℕ => ¬ (q : ℝ) < y) = #(m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ)) := by
    congr 1; ext q; simp [not_lt]
  have hk : kCount z y m = #(m.primeFactors.filter fun q : ℕ => (q : ℝ) < y) := by
    unfold kCount; congr 1; ext q
    simp only [mem_filter, and_congr_right_iff, and_iff_right_iff_imp]
    intro hq _; exact hz q hq
  rcases Nat.lt_or_ge (kCount z y m) 2 with hk2 | hk2
  swap
  · have : (2 : ℝ) ≤ kCount z y m := by exact_mod_cast hk2
    linarith
  -- exactly one small prime and two big ones
  have hk1 : kCount z y m = 1 := by omega
  have hb2 : #(m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ)) = 2 := by omega
  have htr : IsChenTriple z y m := by
    rw [hk] at hk1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hk1
    obtain ⟨b, c, hbc, hBc⟩ := Finset.card_eq_two.mp hb2
    have haF : a ∈ (m.primeFactors.filter fun q : ℕ => (q : ℝ) < y) := ha ▸ mem_singleton_self a
    have haS : a ∈ m.primeFactors := (mem_filter.mp haF).1
    have hay : (a : ℝ) < y := (mem_filter.mp haF).2
    have hbS : b ∈ (m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ)) := hBc ▸ by simp
    have hcS : c ∈ (m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ)) := hBc ▸ by simp
    simp only [mem_filter] at hbS hcS
    have hS : m.primeFactors = insert a {b, c} := by
      have hfe : (m.primeFactors.filter fun q : ℕ => ¬ (q : ℝ) < y) =
          (m.primeFactors.filter fun q : ℕ => y ≤ (q : ℝ)) := by
        ext q; simp [not_lt]
      rw [← Finset.filter_union_filter_not_eq (fun q : ℕ => (q : ℝ) < y) m.primeFactors, ha,
        hfe, hBc]
      rfl
    have hab : a ∉ ({b, c} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton, not_or]
      constructor <;> rintro rfl <;> linarith
    have hm : m = a * (b * c) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq, hS]
      rw [Finset.prod_insert hab, Finset.prod_pair hbc]
    rcases le_total b c with hle | hle
    · exact ⟨a, b, c, Nat.prime_of_mem_primeFactors haS, Nat.prime_of_mem_primeFactors hbS.1,
        Nat.prime_of_mem_primeFactors hcS.1, hz a haS, hay, hbS.2, hle, by rw [hm, mul_assoc]⟩
    · exact ⟨a, c, b, Nat.prime_of_mem_primeFactors haS, Nat.prime_of_mem_primeFactors hcS.1,
        Nat.prime_of_mem_primeFactors hbS.1, hz a haS, hay, hcS.2, hle, by rw [hm]; ring⟩
  simp only [htr, ite_true, hk1]; norm_num


/-- `(n, P(w)) = 1` with `P(w) = ∏_{p < w, p ∤ N} p`, equation (109) of BJS. -/
def SiftedBy (N : ℕ) (w : ℝ) (n : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → (r : ℝ) < w → ¬ r ∣ N → ¬ r ∣ n

/-- Index set of `S(A, P(z))`: primes `p < N`, `p ∤ N`, with `(N − p, P(z)) = 1`. The map
`p ↦ N − p` is injective, so `A` of (105) as a set and this index set have the same size;
`p = N` is excluded by `p ∤ N`. -/
def idxA (N : ℕ) (z : ℝ) : Finset ℕ :=
  (range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ SiftedBy N z (N - p)

/-- `S(A, P(z))`, (105), (107), (109). -/
def SA (N : ℕ) (z : ℝ) : ℕ := #(idxA N z)

/-- The primes `q` with `z ⩽ q < y`, `q ∤ N`, the range of the sum in Lemma 37. -/
def qSet (N : ℕ) (z y : ℝ) : Finset ℕ :=
  (range ⌈y⌉₊).filter fun q => q.Prime ∧ z ≤ (q : ℝ) ∧ ¬ q ∣ N

/-- `S(A_q, P(z))`: sifted elements of `A` divisible by `q`. -/
def SAq (N : ℕ) (z : ℝ) (q : ℕ) : ℕ := #((idxA N z).filter fun p => q ∣ N - p)

/-- `Σ_{z⩽q<y, q∤N} S(A_q, P(z))`. -/
def sumSAq (N : ℕ) (z y : ℝ) : ℕ := ∑ q ∈ qSet N z y, SAq N z q

/-- Membership in `B`, equation (108). -/
def InB (N : ℕ) (z y : ℝ) (b : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z ≤ p₁ ∧ (p₁ : ℝ) < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
    p₁ * p₂ * p₃ < N ∧ Nat.Coprime (p₁ * p₂ * p₃) N ∧ b = N - p₁ * p₂ * p₃

/-- The set `B` of (108); its elements are `< N`. Distinct triples give distinct elements, by
unique factorisation, so the set and the multiset agree. -/
def BSet (N : ℕ) (z y : ℝ) : Finset ℕ := (range N).filter (InB N z y)

/-- `S(B, P(y))`. -/
def SB (N : ℕ) (z y : ℝ) : ℕ := #((BSet N z y).filter (SiftedBy N y))

lemma not_dvd_N_of_dvd_sub {N p q : ℕ} (hp : p.Prime) (hpN : p < N) (hndvd : ¬ p ∣ N)
    (hq : q.Prime) (hqd : q ∣ N - p) : ¬ q ∣ N := by
  intro hqN
  have : q ∣ p := by
    have := Nat.dvd_sub hqN hqd
    rwa [Nat.sub_sub_self hpN.le] at this
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp this
  exact hndvd (hqp ▸ hqN)

lemma mem_idxA {N : ℕ} {z : ℝ} {p : ℕ} :
    p ∈ idxA N z ↔ p < N ∧ p.Prime ∧ ¬ p ∣ N ∧ SiftedBy N z (N - p) := by
  simp [idxA]

lemma factors_ge_of_mem_idxA {N : ℕ} {z : ℝ} {p : ℕ} (h : p ∈ idxA N z) :
    ∀ q ∈ (N - p).primeFactors, z ≤ (q : ℝ) := by
  obtain ⟨hpN, hp, hnd, hs⟩ := mem_idxA.mp h
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  by_contra hlt; push Not at hlt
  exact hs q hqp hlt (not_dvd_N_of_dvd_sub hp hpN hnd hqp hqd) hqd

/-- The sum over `q` of `S(A_q, P(z))` counts each sifted `n = N - p` once for each of its prime
factors in `[z, y)`. -/
lemma sumSAq_eq (N : ℕ) (z y : ℝ) :
    sumSAq N z y = ∑ p ∈ idxA N z, kCount z y (N - p) := by
  unfold sumSAq SAq
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.card_filter]
  unfold kCount
  obtain ⟨hpN, hpp, hnd, _⟩ := mem_idxA.mp hp
  congr 1
  ext q
  simp only [qSet, mem_filter, mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hqc, hq, hzq, _⟩, hqd⟩
    exact ⟨⟨hq, hqd, by omega⟩, hzq, Nat.lt_ceil.mp hqc⟩
  · rintro ⟨⟨hq, hqd, _⟩, hzq, hqy⟩
    exact ⟨⟨Nat.lt_ceil.mpr hqy, hq, hzq, not_dvd_N_of_dvd_sub hpp hpN hnd hq hqd⟩, hqd⟩


/-- Telescoping: `∑_{a ≤ m < a+n} 1/m² ≤ 1/(a-1) - 1/(a+n-1)`. -/
lemma sum_inv_sq_Ico_le (a : ℕ) (ha : 2 ≤ a) (n : ℕ) :
    ∑ m ∈ Ico a (a + n), 1 / ((m : ℝ) * m) ≤ 1 / ((a : ℝ) - 1) - 1 / ((a : ℝ) + n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have key : 1 / (((a + n : ℕ) : ℝ) * ((a + n : ℕ) : ℝ)) ≤
        1 / ((a : ℝ) + n - 1) - 1 / ((a : ℝ) + (n + 1 : ℕ) - 1) := by
      push_cast
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have h1 : (0 : ℝ) < (a : ℝ) + n - 1 := by linarith
      have h2 : (0 : ℝ) < (a : ℝ) + n := by linarith
      rw [show (a : ℝ) + (n + 1) - 1 = a + n by ring, div_sub_div _ _ h1.ne' h2.ne',
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le (a b : ℕ) (ha : 2 ≤ a) :
    ∑ m ∈ Ico a b, 1 / ((m : ℝ) * m) ≤ 1 / ((a : ℝ) - 1) := by
  have hsub : Ico a b ⊆ Ico a (a + b) := Finset.Ico_subset_Ico_right (by omega)
  have h := sum_inv_sq_Ico_le a ha b
  have h0 : 0 ≤ 1 / ((a : ℝ) + b - 1) := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have : (0 : ℝ) ≤ b := by positivity
    apply div_nonneg zero_le_one; linarith
  calc ∑ m ∈ Ico a b, 1 / ((m : ℝ) * m) ≤ ∑ m ∈ Ico a (a + b), 1 / ((m : ℝ) * m) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := by linarith

/-- The non-squarefree sifted `N - p` number at most `2N/z`; in the paper this is the term
`2 N^{7/8}` of Lemma 37. -/
lemma card_nonsqf_le (N : ℕ) (z : ℝ) (hz : 2 ≤ z) :
    (#((idxA N z).filter fun p => ¬ Squarefree (N - p)) : ℝ) ≤ 2 * N / z := by
  set a := ⌈z⌉₊ with ha
  have haz : z ≤ a := Nat.le_ceil z
  have ha2 : 2 ≤ a := by
    have : (2 : ℝ) ≤ a := le_trans hz haz
    exact_mod_cast this
  set Qs := (Ico a (N + 1)).filter Nat.Prime
  set T := Qs.biUnion fun q => (Ioc 0 N).filter fun n => q * q ∣ n
  have hmaps : ∀ p ∈ (idxA N z).filter (fun p => ¬ Squarefree (N - p)), N - p ∈ T := by
    intro p hp
    rw [mem_filter] at hp
    obtain ⟨hpA, hsq⟩ := hp
    have hpN := (mem_idxA.mp hpA).1
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨q, hq, hqq⟩ := hsq
    have hn0 : N - p ≠ 0 := by omega
    have hqd : q ∣ N - p := Dvd.dvd.trans (Dvd.intro q rfl) hqq
    have hzq := factors_ge_of_mem_idxA hpA q (Nat.mem_primeFactors.mpr ⟨hq, hqd, hn0⟩)
    have hqle : q * q ≤ N - p := Nat.le_of_dvd (by omega) hqq
    have hq1 : q ≤ q * q := Nat.le_mul_self q
    simp only [T, Qs, mem_biUnion, mem_filter, mem_Ico, mem_Ioc]
    exact ⟨q, ⟨⟨Nat.ceil_le.mpr hzq, by omega⟩, hq⟩, ⟨by omega, by omega⟩, hqq⟩
  have hinj : Set.InjOn (fun p => N - p) ((idxA N z).filter (fun p => ¬ Squarefree (N - p))) := by
    intro p₁ h₁ p₂ h₂ he
    have := (mem_idxA.mp (mem_filter.mp h₁).1).1
    have := (mem_idxA.mp (mem_filter.mp h₂).1).1
    simp only at he; omega
  have hcard1 : #((idxA N z).filter fun p => ¬ Squarefree (N - p)) ≤ #T := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card (fun n hn => by
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
      exact hmaps p hp)
  have hcard2 : #T ≤ ∑ q ∈ Qs, N / (q * q) := by
    refine (Finset.card_biUnion_le).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun q _ => ?_
    exact Nat.Ioc_filter_dvd_card_eq_div N (q * q)
  have hz1 : (0 : ℝ) < z - 1 := by linarith
  have hz0 : (0 : ℝ) < z := by linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  calc (#((idxA N z).filter fun p => ¬ Squarefree (N - p)) : ℝ)
      ≤ ((∑ q ∈ Qs, N / (q * q) : ℕ) : ℝ) := by exact_mod_cast hcard1.trans hcard2
    _ ≤ ∑ q ∈ Qs, (N : ℝ) * (1 / ((q : ℝ) * q)) := by
        push_cast
        refine Finset.sum_le_sum fun q _ => ?_
        rw [mul_one_div]
        exact_mod_cast Nat.cast_div_le
    _ ≤ ∑ q ∈ Ico a (N + 1), (N : ℝ) * (1 / ((q : ℝ) * q)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (N : ℝ) * ∑ q ∈ Ico a (N + 1), 1 / ((q : ℝ) * q) := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (1 / ((a : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le a (N + 1) ha2) hN0
    _ ≤ (N : ℝ) * (1 / (z - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hN0
        exact one_div_le_one_div_of_le hz1 (by linarith)
    _ ≤ 2 * N / z := by
        rw [mul_one_div, div_le_div_iff₀ hz1 hz0]
        nlinarith

/-- Primes `p ∈ A` with `N - p = p₁p₂p₃` are switched to elements `p = N - p₁p₂p₃` of `B`; those
not sifted by `P(y)` have `p < y`, the term `N^{1/3}` of Lemma 37. -/
lemma card_triple_lt (N : ℕ) (z y : ℝ) (hy : 0 < y) :
    (#((idxA N z).filter fun p => IsChenTriple z y (N - p)) : ℝ) < SB N z y + y := by
  have hsub : (idxA N z).filter (fun p => IsChenTriple z y (N - p)) ⊆
      ((BSet N z y).filter (SiftedBy N y)) ∪ (range ⌈y⌉₊).filter Nat.Prime := by
    intro p hp
    rw [mem_filter] at hp
    obtain ⟨hpA, p₁, p₂, p₃, h1, h2, h3, hz1, hy1, hy2, h23, he⟩ := hp
    obtain ⟨hpN, hpp, hnd, _⟩ := mem_idxA.mp hpA
    rw [mem_union]
    by_cases hpy : (p : ℝ) < y
    · right; simp only [mem_filter, mem_range]; exact ⟨Nat.lt_ceil.mpr hpy, hpp⟩
    left
    push Not at hpy
    have hpos : 0 < p := hpp.pos
    simp only [BSet, mem_filter, mem_range]
    refine ⟨⟨hpN, p₁, p₂, p₃, h1, h2, h3, hz1, hy1, hy2, h23, by omega, ?_, by omega⟩, ?_⟩
    · rw [← he]
      exact Nat.coprime_of_dvd fun k hk hk1 hk2 =>
        not_dvd_N_of_dvd_sub hpp hpN hnd hk hk1 hk2
    · intro r hr hry _ hrp
      have := (Nat.prime_dvd_prime_iff_eq hr hpp).mp hrp
      subst this; linarith
  have hprimes : (#((range ⌈y⌉₊).filter Nat.Prime) : ℝ) < y := by
    have hs : (range ⌈y⌉₊).filter Nat.Prime ⊆ (range ⌈y⌉₊).erase 0 := by
      intro p hp
      rw [mem_filter] at hp
      exact mem_erase.mpr ⟨hp.2.ne_zero, hp.1⟩
    have hc := Finset.card_le_card hs
    rcases Nat.eq_zero_or_pos ⌈y⌉₊ with h0 | h0
    · rw [h0]; simpa using hy
    rw [Finset.card_erase_of_mem (by simp [h0]), card_range] at hc
    have hlt := Nat.ceil_lt_add_one hy.le
    have : ((#((range ⌈y⌉₊).filter Nat.Prime) : ℕ) : ℝ) ≤ ((⌈y⌉₊ - 1 : ℕ) : ℝ) := by
      exact_mod_cast hc
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    linarith
  have := Finset.card_le_card hsub
  have h2 := (this.trans (Finset.card_union_le _ _))
  have h3 : (#((idxA N z).filter fun p => IsChenTriple z y (N - p)) : ℝ) ≤
      (SB N z y : ℝ) + #((range ⌈y⌉₊).filter Nat.Prime) := by
    unfold SB; exact_mod_cast h2
  linarith

lemma card_omega_le_chenCount (N : ℕ) (z : ℝ) :
    #((idxA N z).filter fun p => Ω (N - p) ≤ 2) ≤ chenCount N := by
  unfold chenCount
  apply Finset.card_le_card
  intro p hp
  simp only [mem_filter, mem_range] at hp ⊢
  obtain ⟨hpA, hΩ⟩ := hp
  obtain ⟨hpN, hpp, _, _⟩ := mem_idxA.mp hpA
  exact ⟨hpN, hpp, by omega, hΩ⟩

/-- **The Chen inequality** with general cut-offs: for `z ⩾ 2`, `y > 0`, `N ⩽ y³`,
`π₂(N) > S(A,P(z)) − ½ Σ_q S(A_q,P(z)) − ½ S(B,P(y)) − 2N/z − y`. -/
theorem chen_inequality (N : ℕ) (z y : ℝ) (hz : 2 ≤ z) (hy : 0 < y) (hNy : (N : ℝ) ≤ y ^ 3) :
    (SA N z : ℝ) - (sumSAq N z y : ℝ) / 2 - (SB N z y : ℝ) / 2 - 2 * N / z - y <
      chenCount N := by
  set I := idxA N z
  have hpt : ∀ p ∈ I, 1 - (kCount z y (N - p) : ℝ) / 2 -
      (if IsChenTriple z y (N - p) then 1 else 0) / 2 ≤
      (if Ω (N - p) ≤ 2 then 1 else 0) + (if Squarefree (N - p) then 0 else 1) := by
    intro p hp
    have hpN := (mem_idxA.mp hp).1
    have hp0 := (mem_idxA.mp hp).2.1.pos
    apply chen_weight z y (N - p) (by omega) (factors_ge_of_mem_idxA hp)
    have : ((N - p : ℕ) : ℝ) < N := by exact_mod_cast (show N - p < N by omega)
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.sum_div] at hsum
  have e1 : ∑ p ∈ I, (if Ω (N - p) ≤ 2 then (1 : ℝ) else 0) =
      #(I.filter fun p => Ω (N - p) ≤ 2) := Finset.sum_boole _ _
  have e2 : ∑ p ∈ I, (if Squarefree (N - p) then (0 : ℝ) else 1) =
      #(I.filter fun p => ¬ Squarefree (N - p)) := by
    rw [← Finset.sum_boole]; refine Finset.sum_congr rfl fun p _ => ?_; split_ifs <;> simp_all
  have e3 : ∑ p ∈ I, (if IsChenTriple z y (N - p) then (1 : ℝ) else 0) =
      #(I.filter fun p => IsChenTriple z y (N - p)) := Finset.sum_boole _ _
  have e4 : ∑ p ∈ I, (kCount z y (N - p) : ℝ) = sumSAq N z y := by
    rw [sumSAq_eq]; push_cast; rfl
  rw [e1, e2, e3, e4] at hsum
  have h1 : (#(I.filter fun p => Ω (N - p) ≤ 2) : ℝ) ≤ chenCount N := by
    exact_mod_cast card_omega_le_chenCount N z
  have h2 := card_nonsqf_le N z hz
  have h3 := card_triple_lt N z y hy
  have hSA : (SA N z : ℝ) = #I := rfl
  rw [hSA]
  linarith

/-- `(256 : ℝ)^(1/8) = 2`. -/
lemma rpow_256_eighth : (256 : ℝ) ^ ((1 : ℝ) / 8) = 2 := by
  rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **BJS Lemma 37** ([40, Theorem 10.2]), exactly in the paper's form, with `z = N^{1/8}`,
`y = N^{1/3}` as in (104), for `N ⩾ 256` (so that `z ⩾ 2`), and with `chenCount` for `π₂`:
`π₂(N) > S(A,P(z)) − ½ Σ_{z⩽q<y, q∤N} S(A_q,P(z)) − ½ S(B,P(y)) − 2N^{7/8} − N^{1/3}`. -/
theorem lemma37 (N : ℕ) (hN : 256 ≤ N) :
    (SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) : ℝ)
      - (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      - (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      - 2 * (N : ℝ) ^ ((7 : ℝ) / 8) - (N : ℝ) ^ ((1 : ℝ) / 3) < chenCount N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← rpow_256_eighth]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)
  have hy : 0 < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN0 _
  have hy3 : (N : ℝ) ≤ ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have h78 : 2 * (N : ℝ) ^ ((7 : ℝ) / 8) = 2 * N / (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [show (7 : ℝ) / 8 = 1 - 1 / 8 by norm_num, Real.rpow_sub hN0, Real.rpow_one, mul_div_assoc]
  rw [h78]
  exact chen_inequality N _ _ hz hy hy3

end LeanLab.ChenExplicit
