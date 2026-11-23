module

public import Mathlib
public import LeanLab.Linnik.Statements

/-!
P0093 Linnik 1951, Trudy Mat. Inst. Steklov 38, 152-169, "Prime numbers and powers of two".
Convention check for VERIFY: whether a power of 2 may be `2^0 = 1` does not change Linnik's
statement "every sufficiently large even integer is two primes and at most K powers of 2".
* `atMost_of_atMost0`: for even `N`, two primes plus at most `K` powers of 2 with exponents
  `≥ 0` gives the same with exponents `≥ 1`: pair the ones into twos, and a single left over
  one forces one prime to be 2, and `2 + 1 = 3` is prime.
* `allLargeEven_atMost_iff`, `linnik1951_iff_conv0`: the lab's statement `Linnik.linnik1951`
  is the same Prop under either convention.
Elementary; AI-written Lean code, Claude, run 20261020T1914Z-cloud49, unit U-6714.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- Two primes plus exactly `K` powers of 2, exponents allowed to be `0`. -/
def LinnikExact0 (K N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin K → ℕ, N = p + q + ∑ i, 2 ^ ν i

/-- Two primes plus at most `K` powers of 2, exponents allowed to be `0`. -/
def LinnikAtMost0 (K N : ℕ) : Prop := ∃ k, k ≤ K ∧ LinnikExact0 k N

/-- The lab's statement of Linnik 1951 from `Linnik/Statements.lean`, as a Prop. -/
def Linnik1951Main : Prop := GRH → ∃ K, AllLargeEven (LinnikAtMost K)

theorem exact_of_list {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (l : List ℕ)
    (hl : ∀ x ∈ l, 1 ≤ x) (hN : N = p + q + (l.map (2 ^ ·)).sum) : LinnikExact l.length N := by
  refine ⟨p, q, hp, hq, fun i => l.get i, fun i => hl _ (List.get_mem l i), ?_⟩
  rw [hN, ← List.sum_ofFn]
  congr 2
  apply List.ext_get <;> simp

theorem exact_of_multiset {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (s : Multiset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) (hN : N = p + q + (s.map (2 ^ ·)).sum) :
    LinnikExact (Multiset.card s) N := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep s
  exact exact_of_list hp hq l hs hN

/-- Exponents `≥ 0` to exponents `≥ 1`, for even `N`, without increasing the count. -/
theorem atMost_of_exact0 {K N : ℕ} (hev : Even N) (h : LinnikExact0 K N) :
    LinnikAtMost K N := by
  obtain ⟨p, q, hp, hq, ν, hN⟩ := h
  set s : Multiset ℕ := Finset.univ.val.map ν with hs
  have hsum : ∑ i, 2 ^ ν i = (s.map (2 ^ ·)).sum := by
    rw [Finset.sum_eq_multiset_sum, hs, Multiset.map_map]; rfl
  have hcard : Multiset.card s = K := by simp [hs]
  set t := s.filter (fun x => ¬ x = 0) with ht
  set z := s.count 0 with hz
  have hsplit : s = Multiset.replicate z 0 + t := by
    rw [ht, hz, ← Multiset.filter_eq' s 0]; exact (Multiset.filter_add_not _ s).symm
  have hsum2 : (s.map (2 ^ ·)).sum = z + (t.map (2 ^ ·)).sum := by
    conv_lhs => rw [hsplit]
    simp [Multiset.map_replicate, Multiset.sum_replicate]
  have hcard2 : Multiset.card s = z + Multiset.card t := by
    conv_lhs => rw [hsplit]
    simp
  have ht1 : ∀ x ∈ t, 1 ≤ x := by
    intro x hx; rw [ht, Multiset.mem_filter] at hx; omega
  have hE : 2 ∣ (t.map (2 ^ ·)).sum := by
    apply Multiset.dvd_sum
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
    exact dvd_pow_self 2 (by have := ht1 a ha; omega)
  set u := t + Multiset.replicate (z / 2) 1 with hu
  have hu1 : ∀ x ∈ u, 1 ≤ x := by
    intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact ht1 x h
    · rw [Multiset.eq_of_mem_replicate h]
  have husum : (u.map (2 ^ ·)).sum = (t.map (2 ^ ·)).sum + 2 * (z / 2) := by
    simp [hu, Multiset.map_replicate, Multiset.sum_replicate, mul_comm]
  have hucard : Multiset.card u = Multiset.card t + z / 2 := by simp [hu]
  obtain ⟨e, he⟩ := hE
  obtain ⟨n, hn⟩ := hev
  rw [hsum, hsum2] at hN
  rcases Nat.even_or_odd z with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨Multiset.card u, by omega, exact_of_multiset hp hq u hu1 ?_⟩
    omega
  · have p2 := hp.eq_two_or_odd
    have q2 := hq.eq_two_or_odd
    have hpq : p = 2 ∨ q = 2 := by omega
    rcases hpq with rfl | rfl
    · refine ⟨Multiset.card u, by omega, exact_of_multiset Nat.prime_three hq u hu1 ?_⟩
      omega
    · refine ⟨Multiset.card u, by omega, exact_of_multiset hp Nat.prime_three u hu1 ?_⟩
      omega

theorem exact0_of_exact {K N : ℕ} (h : LinnikExact K N) : LinnikExact0 K N := by
  obtain ⟨p, q, hp, hq, ν, -, hN⟩ := h
  exact ⟨p, q, hp, hq, ν, hN⟩

theorem atMost_of_atMost0 {K N : ℕ} (hev : Even N) (h : LinnikAtMost0 K N) :
    LinnikAtMost K N := by
  obtain ⟨k, hk, h⟩ := h
  exact atMost_mono hk (atMost_of_exact0 hev h)

theorem atMost0_of_atMost {K N : ℕ} (h : LinnikAtMost K N) : LinnikAtMost0 K N := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk, exact0_of_exact h⟩

/-- For all large even `N` the two conventions on exponents agree, for each `K`. -/
theorem allLargeEven_atMost_iff (K : ℕ) :
    AllLargeEven (LinnikAtMost K) ↔ AllLargeEven (LinnikAtMost0 K) := by
  constructor
  · exact allLargeEven_mono (fun _ => atMost0_of_atMost)
  · rintro ⟨N0, h⟩
    exact ⟨N0, fun N he hN => atMost_of_atMost0 he (h N he hN)⟩

/-- The lab's `Linnik.linnik1951` statement does not depend on the exponent convention. -/
theorem linnik1951_iff_conv0 :
    Linnik1951Main ↔ (GRH → ∃ K, AllLargeEven (LinnikAtMost0 K)) := by
  unfold Linnik1951Main
  simp only [allLargeEven_atMost_iff]

/-- Not vacuous and the convention matters pointwise only for odd `N`: `7 = 2 + 3 + 2^1`
needs no `2^0`, while `9 = 3 + 5 + 2^0` uses one. -/
example : LinnikExact0 1 9 := ⟨3, 5, Nat.prime_three, Nat.prime_five, fun _ => 0, by simp⟩

end LeanLab.Linnik1951
