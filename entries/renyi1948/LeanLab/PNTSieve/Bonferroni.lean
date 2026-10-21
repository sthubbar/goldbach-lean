module

public import Mathlib

/-!
# Bonferroni truncations and Brun's pure sieve inequalities

Lab proof, unit U-5322, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Bonferroni 1936 and Brun 1915 to 1920; the smallest Lean lemma of IDEAS I-5051, the route to Rényi's
theorem `N = p + P_K` through a lower bound sieve on `{N - p}` with the lab's Bombieri-Vinogradov.

* `trunc_sum_eq`: `Σ_{T ⊆ X, |T| ≤ r} (-1)^{|T|} = (-1)^r C(m, r)` when `|X| = m + 1`;
* `bonferroni_even`, `bonferroni_odd`: the truncation at even `r` is `≥ [X = ∅]`, at odd `r` it is
  `≤ [X = ∅]`;
* `dvd_iff_subset`: for a finset `P` of primes, `∏ T ∣ n ↔ T ⊆ P.filter (· ∣ n)` for `T ⊆ P`, `n ≠ 0`;
* `brun_lower`, `brun_upper`: for a finite set of positive integers `A` and a finset `P` of
  primes, with `S(A, P) = #{a ∈ A : no p ∈ P divides a}` and `A_d = #{a ∈ A : d ∣ a}`,
  `Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} A_{∏T}` is `≤ S(A, P)` for odd `r` and `≥ S(A, P)` for even `r`.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

variable {α : Type*} [DecidableEq α]

/-- The truncated alternating sum over subsets. -/
def trunc (X : Finset α) (r : ℕ) : ℤ :=
  ∑ T ∈ X.powerset.filter (fun T => T.card ≤ r), (-1 : ℤ) ^ T.card

lemma trunc_eq_range (X : Finset α) (r : ℕ) :
    trunc X r = ∑ j ∈ range (X.card + 1), (X.card).choose j • (if j ≤ r then (-1 : ℤ) ^ j else 0) := by
  unfold trunc
  rw [sum_filter, ← sum_powerset_apply_card (fun j => if j ≤ r then (-1 : ℤ) ^ j else 0)]

lemma trunc_sum_eq (X : Finset α) (m r : ℕ) (hX : X.card = m + 1) :
    trunc X r = (-1) ^ r * (m.choose r : ℤ) := by
  rw [trunc_eq_range, hX]
  rcases le_or_gt (m + 1) r with h | h
  · -- every j ≤ m + 1 ≤ r is kept
    have : ∀ j ∈ range (m + 1 + 1), (m + 1).choose j • (if j ≤ r then (-1 : ℤ) ^ j else 0) =
        (-1) ^ j * ((m + 1).choose j : ℤ) := by
      intro j hj
      rw [mem_range] at hj
      rw [if_pos (by omega), nsmul_eq_mul]; ring
    rw [sum_congr rfl this, Int.alternating_sum_range_choose_eq_choose (n := m) (m := m + 1)]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · -- only j ≤ r < m + 1 survive
    have hsub : range (r + 1) ⊆ range (m + 1 + 1) := range_subset_range.mpr (by omega)
    rw [← sum_subset hsub]
    · rw [← Int.alternating_sum_range_choose_eq_choose (n := m) (m := r)]
      refine sum_congr rfl (fun j hj => ?_)
      rw [mem_range] at hj
      rw [if_pos (by omega), nsmul_eq_mul]; ring
    · intro j _ hj
      rw [mem_range] at hj
      rw [if_neg (by omega), smul_zero]

lemma trunc_empty (r : ℕ) : trunc (∅ : Finset α) r = 1 := by
  simp [trunc, Finset.filter_singleton]

/-- Even truncation: `[X = ∅] ≤ Σ_{T ⊆ X, |T| ≤ r} (-1)^{|T|}`. -/
theorem bonferroni_even (X : Finset α) {r : ℕ} (hr : Even r) :
    (if X = ∅ then 1 else 0 : ℤ) ≤ trunc X r := by
  by_cases h : X = ∅
  · subst h; simp [trunc_empty]
  · rw [if_neg h]
    obtain ⟨m, hm⟩ : ∃ m, X.card = m + 1 :=
      ⟨X.card - 1, by have := card_pos.mpr (nonempty_iff_ne_empty.mpr h); omega⟩
    rw [trunc_sum_eq X m r hm, hr.neg_one_pow, one_mul]
    exact_mod_cast Nat.zero_le _

/-- Odd truncation: `Σ_{T ⊆ X, |T| ≤ r} (-1)^{|T|} ≤ [X = ∅]`. -/
theorem bonferroni_odd (X : Finset α) {r : ℕ} (hr : Odd r) :
    trunc X r ≤ (if X = ∅ then 1 else 0 : ℤ) := by
  by_cases h : X = ∅
  · subst h; simp [trunc_empty]
  · rw [if_neg h]
    obtain ⟨m, hm⟩ : ∃ m, X.card = m + 1 :=
      ⟨X.card - 1, by have := card_pos.mpr (nonempty_iff_ne_empty.mpr h); omega⟩
    rw [trunc_sum_eq X m r hm, hr.neg_one_pow, neg_one_mul, neg_nonpos]
    exact_mod_cast Nat.zero_le _

/-- For a finset `P` of primes, `T ⊆ P` and `n ≠ 0`: `∏ T ∣ n ↔ T ⊆ P.filter (· ∣ n)`. -/
lemma dvd_iff_subset (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {T : Finset ℕ} (hT : T ⊆ P) (n : ℕ) :
    (∏ p ∈ T, p) ∣ n ↔ T ⊆ P.filter (· ∣ n) := by
  constructor
  · intro h p hp
    exact mem_filter.mpr ⟨hT hp, (dvd_prod_of_mem _ hp).trans h⟩
  · intro h
    exact Finset.prod_primes_dvd n (fun p hp => (hP p (hT hp)).prime)
      (fun p hp => (mem_filter.mp (h hp)).2)

/-- The pointwise identity: the truncated Möbius sum over `T ⊆ P` with `∏ T ∣ n` is `trunc` of the
primes of `P` dividing `n`. -/
lemma pointwise (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r n : ℕ) :
    ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      (if (∏ p ∈ T, p) ∣ n then (-1 : ℤ) ^ T.card else 0) = trunc (P.filter (· ∣ n)) r := by
  unfold trunc
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext T
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨⟨hTP, hr⟩, hd⟩; exact ⟨(dvd_iff_subset P hP hTP n).mp hd, hr⟩
  · rintro ⟨hTX, hr⟩
    have hTP : T ⊆ P := hTX.trans (filter_subset _ _)
    exact ⟨⟨hTP, hr⟩, (dvd_iff_subset P hP hTP n).mpr hTX⟩

/-- `S(A, P)`, the number of `a ∈ A` with no prime factor in `P`. -/
def sifted (A : Finset ℕ) (P : Finset ℕ) : ℤ := (A.filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card

/-- The truncated Brun sum `Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} A_{∏T}`. -/
def brunSum (A : Finset ℕ) (P : Finset ℕ) (r : ℕ) : ℤ :=
  ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r),
    (-1 : ℤ) ^ T.card * (A.filter (fun a => (∏ p ∈ T, p) ∣ a)).card

lemma brunSum_eq (A : Finset ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    brunSum A P r = ∑ a ∈ A, trunc (P.filter (· ∣ a)) r := by
  unfold brunSum
  have : ∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      (-1 : ℤ) ^ T.card * (A.filter (fun a => (∏ p ∈ T, p) ∣ a)).card =
      ∑ a ∈ A, (if (∏ p ∈ T, p) ∣ a then (-1 : ℤ) ^ T.card else 0) := by
    intro T _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [sum_congr rfl this, sum_comm]
  exact sum_congr rfl (fun a _ => pointwise P hP r a)

lemma sifted_eq (A : Finset ℕ) (P : Finset ℕ) :
    sifted A P = ∑ a ∈ A, (if P.filter (· ∣ a) = ∅ then (1 : ℤ) else 0) := by
  unfold sifted
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  apply filter_congr
  intro a _
  rw [filter_eq_empty_iff]

/-- Brun's pure sieve, lower bound: for odd `r`, `Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} A_{∏T} ≤ S(A, P)`. -/
theorem brun_lower (A : Finset ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (hr : Odd r) :
    brunSum A P r ≤ sifted A P := by
  rw [brunSum_eq A P hP, sifted_eq]
  exact sum_le_sum (fun a _ => bonferroni_odd _ hr)

/-- Brun's pure sieve, upper bound: for even `r`, `S(A, P) ≤ Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} A_{∏T}`. -/
theorem brun_upper (A : Finset ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (hr : Even r) :
    sifted A P ≤ brunSum A P r := by
  rw [brunSum_eq A P hP, sifted_eq]
  exact sum_le_sum (fun a _ => bonferroni_even _ hr)

/-- Vacuity test: `A = {1, …, 30}`, `P = {2, 3, 5}`: eight survivors; the first truncation gives
`30 - 15 - 10 - 6 = -1 ≤ 8`, the second `-1 + 5 + 3 + 2 = 9 ≥ 8`. -/
theorem example_30 : sifted (Icc 1 30) {2, 3, 5} = 8 ∧ brunSum (Icc 1 30) {2, 3, 5} 1 = -1 ∧
    brunSum (Icc 1 30) {2, 3, 5} 2 = 9 := by
  decide

end LeanLab.PNTSieve.Bonferroni

