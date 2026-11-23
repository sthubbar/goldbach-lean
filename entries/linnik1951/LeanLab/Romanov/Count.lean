module

public import Mathlib

/-!
# Romanov's theorem, step 2: Cauchy-Schwarz and the collision count for `p + 2^k`

Lab proof, unit U-5602, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics.
Binary Goldbach is OPEN; this is the Linnik-Goldbach line, IDEAS I-5052.

For a finite set `A` of naturals and `L`, let `T = A × {0, …, L - 1}`, `f(p, k) = p + 2^k` and
`I = f(T)`. Then

* `card_sq_le`: `#T² ≤ #I · coll`, `coll = #{(a, b) ∈ T × T : f a = f b}`, Cauchy-Schwarz;
* `coll_le`: `coll ≤ L · #A + 2 Q`, `Q = Σ_{k < k' < L} G(k, k')`, where
  `G(k, k') = #{q ∈ [0, M) : q ∈ P, q + 2^k' - 2^k ∈ P}` for any `M` and `P` containing `A`
  below `M`; so the off-diagonal collisions are prime pairs with gap `2^k' - 2^k`.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset

/-- `f(p, k) = p + 2^k`. -/
def f (a : ℕ × ℕ) : ℕ := a.1 + 2 ^ a.2

/-- The collisions of `f` on `T`. -/
def coll (T : Finset (ℕ × ℕ)) : ℕ := #{ab ∈ T ×ˢ T | f ab.1 = f ab.2}

theorem card_sq_le (T : Finset (ℕ × ℕ)) : #T ^ 2 ≤ #(T.image f) * coll T := by
  have h1 : #T = ∑ n ∈ T.image f, #{a ∈ T | f a = n} := card_eq_sum_card_image f T
  have h2 : coll T = ∑ n ∈ T.image f, #{a ∈ T | f a = n} ^ 2 := by
    unfold coll
    rw [card_eq_sum_card_fiberwise (f := fun ab : (ℕ × ℕ) × (ℕ × ℕ) => f ab.1) (t := T.image f)]
    · refine sum_congr rfl fun n _ => ?_
      rw [sq, ← card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hn⟩
        exact ⟨⟨ha, hn⟩, hb, hab ▸ hn⟩
      · rintro ⟨⟨ha, hn⟩, hb, hbn⟩
        exact ⟨⟨⟨ha, hb⟩, hn.trans hbn.symm⟩, hn⟩
    · intro ab hab
      simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hab
      exact mem_coe.2 (mem_image_of_mem f hab.1.1)
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- The prime pair count `G = #{q < M : q ∈ P, q + h ∈ P}`. -/
def gap (P : Finset ℕ) (h M : ℕ) : ℕ := #{q ∈ range M | q ∈ P ∧ q + h ∈ P}

/-- Pairs `(p, p') ∈ A × A` with `p + 2^k = p' + 2^k'`. -/
def pc (A : Finset ℕ) (k k' : ℕ) : ℕ := #{pp ∈ A ×ˢ A | pp.1 + 2 ^ k = pp.2 + 2 ^ k'}

lemma pc_diag (A : Finset ℕ) (k : ℕ) : pc A k k ≤ #A := by
  unfold pc
  refine card_le_card_of_injOn (fun pp => pp.1) (fun pp hpp => ?_) (fun a ha b hb hab => ?_)
  · simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpp
    exact mem_coe.2 hpp.1.1
  · simp only [coe_filter, mem_product, Set.mem_setOf_eq] at ha hb
    have h1 : a.2 = a.1 := by omega
    have h2 : b.2 = b.1 := by omega
    exact Prod.ext hab (by simp only at hab; omega)

lemma pc_lt (A P : Finset ℕ) (M : ℕ) (hA : ∀ p ∈ A, p < M ∧ p ∈ P) {k k' : ℕ} (hkk : k < k') :
    pc A k k' ≤ gap P (2 ^ k' - 2 ^ k) M := by
  have hle : 2 ^ k ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) hkk.le
  unfold pc gap
  refine card_le_card_of_injOn (fun pp => pp.2) (fun pp hpp => ?_) (fun a ha b hb hab => ?_)
  · simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpp
    simp only [coe_filter, mem_range, Set.mem_setOf_eq]
    refine ⟨(hA _ hpp.1.2).1, (hA _ hpp.1.2).2, ?_⟩
    have : pp.2 + (2 ^ k' - 2 ^ k) = pp.1 := by omega
    rw [this]; exact (hA _ hpp.1.1).2
  · simp only [coe_filter, mem_product, Set.mem_setOf_eq] at ha hb
    simp only at hab
    exact Prod.ext (by omega) hab

lemma pc_gt (A P : Finset ℕ) (M : ℕ) (hA : ∀ p ∈ A, p < M ∧ p ∈ P) {k k' : ℕ} (hkk : k' < k) :
    pc A k k' ≤ gap P (2 ^ k - 2 ^ k') M := by
  have hle : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkk.le
  unfold pc gap
  refine card_le_card_of_injOn (fun pp => pp.1) (fun pp hpp => ?_) (fun a ha b hb hab => ?_)
  · simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpp
    simp only [coe_filter, mem_range, Set.mem_setOf_eq]
    refine ⟨(hA _ hpp.1.1).1, (hA _ hpp.1.1).2, ?_⟩
    have : pp.1 + (2 ^ k - 2 ^ k') = pp.2 := by omega
    rw [this]; exact (hA _ hpp.1.2).2
  · simp only [coe_filter, mem_product, Set.mem_setOf_eq] at ha hb
    simp only at hab
    exact Prod.ext hab (by omega)

/-- The collision count splits by the pair of exponents. -/
lemma coll_le_sum (A : Finset ℕ) (L : ℕ) :
    coll (A ×ˢ range L) ≤ ∑ k ∈ range L, ∑ k' ∈ range L, pc A k k' := by
  unfold coll
  rw [← sum_product']
  rw [card_eq_sum_card_fiberwise (f := fun ab : (ℕ × ℕ) × (ℕ × ℕ) => (ab.1.2, ab.2.2))
    (t := range L ×ˢ range L)]
  · refine sum_le_sum fun kk _ => ?_
    unfold pc
    refine card_le_card_of_injOn (fun ab => (ab.1.1, ab.2.1)) (fun ab hab => ?_)
      (fun a ha b hb hab => ?_)
    · simp only [mem_coe, mem_filter, mem_product, mem_range] at hab
      simp only [mem_coe, mem_filter, mem_product]
      obtain ⟨⟨⟨⟨h1, _⟩, h3, _⟩, h5⟩, h6⟩ := hab
      refine ⟨⟨h1, h3⟩, ?_⟩
      rw [← h6]; exact h5
    · simp only [mem_coe, mem_filter, mem_product, mem_range] at ha hb
      simp only [Prod.mk.injEq] at hab
      obtain ⟨_, e1⟩ := ha
      obtain ⟨_, e2⟩ := hb
      rw [Prod.ext_iff] at e1 e2
      ext
      · exact hab.1
      · simp only at e1 e2; omega
      · exact hab.2
      · simp only at e1 e2; omega
  · intro ab hab
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at hab
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
    exact ⟨hab.1.1.2, hab.1.2.2⟩

/-- **Collision bound**: `coll ≤ L · #A + 2 Σ_{k < k' < L} G(2^k' - 2^k)`. -/
theorem coll_le (A P : Finset ℕ) (M L : ℕ) (hA : ∀ p ∈ A, p < M ∧ p ∈ P) :
    coll (A ×ˢ range L) ≤ L * #A + 2 * ∑ k ∈ range L, ∑ k' ∈ range L,
      if k < k' then gap P (2 ^ k' - 2 ^ k) M else 0 := by
  refine le_trans (coll_le_sum A L) ?_
  have hpt : ∀ k k', pc A k k' ≤ (if k = k' then #A else 0) +
      (if k < k' then gap P (2 ^ k' - 2 ^ k) M else 0) +
      (if k' < k then gap P (2 ^ k - 2 ^ k') M else 0) := by
    intro k k'
    rcases lt_trichotomy k k' with h | h | h
    · rw [if_neg h.ne, if_pos h, if_neg (by omega)]; simpa using pc_lt A P M hA h
    · subst h; simpa using pc_diag A k
    · rw [if_neg h.ne', if_neg (by omega), if_pos h]; simpa using pc_gt A P M hA h
  calc ∑ k ∈ range L, ∑ k' ∈ range L, pc A k k'
      ≤ ∑ k ∈ range L, ∑ k' ∈ range L, ((if k = k' then #A else 0) +
        (if k < k' then gap P (2 ^ k' - 2 ^ k) M else 0) +
        (if k' < k then gap P (2 ^ k - 2 ^ k') M else 0)) :=
        sum_le_sum fun k _ => sum_le_sum fun k' _ => hpt k k'
    _ = L * #A + 2 * ∑ k ∈ range L, ∑ k' ∈ range L,
          if k < k' then gap P (2 ^ k' - 2 ^ k) M else 0 := by
        simp only [sum_add_distrib]
        rw [sum_comm (f := fun k k' => if k' < k then gap P (2 ^ k - 2 ^ k') M else 0)]
        have hd : ∑ k ∈ range L, ∑ k' ∈ range L, (if k = k' then #A else 0) = L * #A := by
          simp only [sum_ite_eq, mem_range]
          rw [sum_congr rfl (fun x hx => if_pos (mem_range.1 hx))]
          simp
        rw [hd]
        ring

end LeanLab.Romanov
