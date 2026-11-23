module

public import LeanLab.Romanov.Theorem
public import LeanLab.Romanov.PositiveK

/-!
# The full Romanov second moment

AI wrote the Lean code. Known mathematics. Gallagher 1975, page 138, display 2.
The proof uses the uniform Brun bound through `Q_le` and Romanov's lemma.
Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset Real

/-- The number of representations of `n` in a finite set of pairs. -/
def fiberCount (T : Finset (ℕ × ℕ)) (n : ℕ) : ℕ := #{a ∈ T | f a = n}

/-- The sum of squared fiber sizes is the collision count. -/
theorem sum_fiberCount_sq (T : Finset (ℕ × ℕ)) (I : Finset ℕ)
    (hT : ∀ a ∈ T, f a ∈ I) :
    ∑ n ∈ I, fiberCount T n ^ 2 = coll T := by
  unfold coll fiberCount
  rw [card_eq_sum_card_fiberwise
    (f := fun ab : (ℕ × ℕ) × (ℕ × ℕ) => f ab.1) (t := I)]
  · refine sum_congr rfl fun n _ => ?_
    rw [sq, ← card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨ha, hn⟩, hb, hbn⟩
      exact ⟨⟨⟨ha, hb⟩, hn.trans hbn.symm⟩, hn⟩
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hn⟩
      exact ⟨⟨ha, hn⟩, hb, hab ▸ hn⟩
  · intro ab hab
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hab
    exact mem_coe.mpr (hT _ hab.1.1)

/-- Restricting a set of pairs cannot increase its collision count. -/
theorem coll_mono {T U : Finset (ℕ × ℕ)} (h : T ⊆ U) : coll T ≤ coll U := by
  unfold coll
  exact card_le_card (filter_subset_filter _ (product_subset_product h h))

/-- A dyadic upper bound for the diagonal term. -/
theorem diagonal_le (L : ℕ) :
    (Nat.primeCounting (2 ^ (L + 1)) : ℝ) * L ≤ 9 * 2 ^ (L + 1) := by
  set N : ℝ := 2 ^ (L + 1) with hN
  have hN1 : 1 < N := by
    dsimp [N]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hN0 : 0 ≤ N := by linarith
  have hNnat : (Nat.primeCounting (2 ^ (L + 1)) : ℝ) ≤
      log 4 * N / log (sqrt N) + sqrt N := by
    have h := Chebyshev.pi_le_log4_mul_div hN1
    have hf : ⌊N⌋₊ = 2 ^ (L + 1) := by
      dsimp [N]
      exact_mod_cast Nat.floor_natCast (2 ^ (L + 1))
    rw [hf] at h
    exact h
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog : log (sqrt N) = (L + 1) * log 2 / 2 := by
    rw [Real.log_sqrt hN0, hN, Real.log_pow]
    push_cast
    ring
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hmain : (log 4 * N / log (sqrt N)) * L ≤ 8 * N := by
    rw [hlog, hlog4]
    have hden : 0 < ((L : ℝ) + 1) * log 2 / 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [show (0 : ℝ) ≤ L by positivity]
  have hsq : (L : ℝ) ^ 2 ≤ N := by
    dsimp [N]
    exact_mod_cast sq_le_two_pow L
  have hroot : (L : ℝ) ≤ sqrt N := (Real.le_sqrt (Nat.cast_nonneg L) hN0).mpr hsq
  have hrem : sqrt N * L ≤ N := by
    calc sqrt N * L ≤ sqrt N * sqrt N := mul_le_mul_of_nonneg_left hroot (sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN0
  have h := mul_le_mul_of_nonneg_right hNnat (Nat.cast_nonneg L)
  dsimp [N] at *
  nlinarith

/-- Any partial sum of squared fiber sizes is at most the collision count. -/
theorem sum_fiberCount_sq_le (T : Finset (ℕ × ℕ)) (I : Finset ℕ) :
    ∑ n ∈ I, fiberCount T n ^ 2 ≤ coll T := by
  calc ∑ n ∈ I, fiberCount T n ^ 2 ≤ ∑ n ∈ I ∪ T.image f, fiberCount T n ^ 2 :=
        sum_le_sum_of_subset (subset_union_left)
    _ = coll T := sum_fiberCount_sq T _ (fun a ha => mem_union_right _ (mem_image_of_mem f ha))

/-- A box of prime and exponent pairs containing every relevant representation. -/
def primeBox (L : ℕ) : Finset (ℕ × ℕ) :=
  Nat.primesBelow (2 ^ (L + 1) + 1) ×ˢ range L

/-- The complete collision bound on a dyadic box. -/
theorem primeBox_coll_le (L : ℕ) (hL : 1 ≤ L) :
    (coll (primeBox L) : ℝ) ≤ (9 + 2 * R₁) * 2 ^ (L + 1) := by
  set A := Nat.primesBelow (2 ^ (L + 1) + 1)
  have hA : ∀ p ∈ A, p < 2 ^ (L + 1) + 1 ∧ p ∈ A := by
    intro p hp
    exact ⟨(Nat.mem_primesBelow.mp hp).1, hp⟩
  have hcoll := coll_le A A (2 ^ (L + 1) + 1) L hA
  have hQ := Q_le A (fun p hp => Nat.prime_of_mem_primesBelow hp) L hL
  have hdiag := diagonal_le L
  have hcard : #A = Nat.primeCounting (2 ^ (L + 1)) := by
    rw [Nat.primesBelow_card_eq_primeCounting']
    rfl
  have hr : (coll (primeBox L) : ℝ) ≤
      (L : ℝ) * #A + 2 * ((∑ k ∈ range L, ∑ k' ∈ range L,
        if k < k' then gap A (2 ^ k' - 2 ^ k) (2 ^ (L + 1) + 1) else 0 : ℕ) : ℝ) := by
    exact_mod_cast hcoll
  rw [hcard] at hr
  nlinarith

/-- All pairs representing `n` with positive exponent. -/
def representations (n : ℕ) : Finset (ℕ × ℕ) :=
  {a ∈ range (n + 1) ×ˢ range (n + 1) | a.1.Prime ∧ 1 ≤ a.2 ∧ f a = n}

/-- This finite set contains every prime and positive exponent representation. -/
theorem mem_representations (a : ℕ × ℕ) (n : ℕ) :
    a ∈ representations n ↔ a.1.Prime ∧ 1 ≤ a.2 ∧ f a = n := by
  unfold representations
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hpow : 2 ^ a.2 ≤ n := by dsimp [f] at h; omega
    have hk := Nat.lt_two_pow_self (n := a.2)
    have hp : a.1 ≤ n := by dsimp [f] at h; omega
    exact ⟨⟨by omega, by omega⟩, h⟩

/-- Romanov's representation count with exponent at least one. -/
def repCount (n : ℕ) : ℕ := #(representations n)

/-- Every representation below `x` lies in a single dyadic box. -/
theorem repCount_le_box {n x : ℕ} (hn : n ≤ x) :
    repCount n ≤ fiberCount (primeBox (Nat.log 2 x + 1)) n := by
  unfold repCount fiberCount
  apply card_le_card
  intro a ha
  have h := (mem_representations a n).mp ha
  have hp : a.1 ≤ n := by
    calc a.1 ≤ a.1 + 2 ^ a.2 := Nat.le_add_right _ _
      _ = n := h.2.2
  have hpow : 2 ^ a.2 ≤ x := by
    calc 2 ^ a.2 ≤ a.1 + 2 ^ a.2 := Nat.le_add_left _ _
      _ = n := h.2.2
      _ ≤ x := hn
  have hk := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  have hx := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
  have hb : 2 ^ (Nat.log 2 x + 1) ≤ 2 ^ (Nat.log 2 x + 1 + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [mem_filter, primeBox, mem_product, Nat.mem_primesBelow, mem_range]
  exact ⟨⟨⟨by omega, h.1⟩, by omega⟩, h.2.2⟩

/-- Gallagher page 138, display 2, with an explicit absolute constant. -/
theorem romanov_second_moment (x : ℕ) :
    ∑ n ∈ range (x + 1), (repCount n : ℝ) ^ 2 ≤ 4 * (9 + 2 * R₁) * x := by
  by_cases hx : x = 0
  · subst x
    norm_num [repCount, representations, f]
  have hsum : ∑ n ∈ range (x + 1), repCount n ^ 2 ≤ coll (primeBox (Nat.log 2 x + 1)) := by
    calc ∑ n ∈ range (x + 1), repCount n ^ 2
        ≤ ∑ n ∈ range (x + 1), fiberCount (primeBox (Nat.log 2 x + 1)) n ^ 2 := by
          apply sum_le_sum
          intro n hn
          exact Nat.pow_le_pow_left (repCount_le_box (by have := mem_range.mp hn; omega)) 2
      _ ≤ _ := sum_fiberCount_sq_le _ _
  have hsumr : ∑ n ∈ range (x + 1), (repCount n : ℝ) ^ 2 ≤
      (coll (primeBox (Nat.log 2 x + 1)) : ℝ) := by exact_mod_cast hsum
  have hbox := primeBox_coll_le (Nat.log 2 x + 1) (by omega)
  have hpow : (2 : ℝ) ^ (Nat.log 2 x + 1 + 1) ≤ 4 * x := by
    have h := Nat.pow_log_le_self 2 hx
    have hr : (2 : ℝ) ^ Nat.log 2 x ≤ x := by exact_mod_cast h
    calc (2 : ℝ) ^ (Nat.log 2 x + 1 + 1) = 4 * 2 ^ Nat.log 2 x := by ring
      _ ≤ 4 * x := by gcongr
  have hR := R₁_pos
  calc ∑ n ∈ range (x + 1), (repCount n : ℝ) ^ 2
      ≤ (9 + 2 * R₁) * 2 ^ (Nat.log 2 x + 1 + 1) := hsumr.trans hbox
    _ ≤ (9 + 2 * R₁) * (4 * x) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 4 * (9 + 2 * R₁) * x := by ring

/-- The second moment bound for every nonnegative real cutoff. -/
theorem romanov_second_moment_real (x : ℝ) (hx : 0 ≤ x) :
    ∑ n ∈ range (⌊x⌋₊ + 1), (repCount n : ℝ) ^ 2 ≤ 4 * (9 + 2 * R₁) * x := by
  have hR := R₁_pos
  exact (romanov_second_moment ⌊x⌋₊).trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le hx) (by positivity))

/-- Positivity of the count means exactly a prime plus a positive power of two. -/
theorem repCount_pos_iff (n : ℕ) : 0 < repCount n ↔
    ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 ^ k := by
  rw [repCount, card_pos]
  constructor
  · rintro ⟨⟨p, k⟩, hpk⟩
    have h := (mem_representations (p, k) n).mp hpk
    exact ⟨p, k, h.1, h.2.1, h.2.2.symm⟩
  · rintro ⟨p, k, hp, hk, hn⟩
    exact ⟨(p, k), (mem_representations (p, k) n).mpr ⟨hp, hk, hn.symm⟩⟩

/-- The positive lower density corollary in the same representation count notation. -/
theorem romanov_repCount_density : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    c * x ≤ (#((range x).filter (fun n => 0 < repCount n)) : ℝ) := by
  obtain ⟨c, hc, X₀, h⟩ := romanov_pos
  refine ⟨c, hc, X₀, fun x hx => ?_⟩
  obtain ⟨I, hI, hcard⟩ := h x hx
  have hs : I ⊆ (range x).filter (fun n => 0 < repCount n) := by
    intro n hn
    obtain ⟨hnx, hrep⟩ := hI n hn
    exact mem_filter.mpr ⟨mem_range.mpr hnx, (repCount_pos_iff n).mpr hrep⟩
  exact hcard.trans (Nat.cast_le.mpr (card_le_card hs))

end LeanLab.Romanov
