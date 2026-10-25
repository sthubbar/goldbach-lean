module

public import Mathlib

/-!
P0047 Alsetri, Shao 2024, arXiv 2405.18576v?, Theorem 2.1, the local theorem: for m squarefree and
A, B ⊆ ℤ_m^* with |A| + |B| > φ(m)(2 - ∏_{p∣m} (p-2)/(p-1)), A + B = ℤ_m. Unit U-5054.
The paper assumes m odd; the proof below needs only squarefree. Since φ(m) ∏ (p-2)/(p-1) = ∏ (p-2) for
squarefree m, the hypothesis is stated as |A| + |B| > 2 |ℤ_m^*| - ∏_{p∣m} (p-2), in integers.
PROVED, no cited input: `card_X_prime`, `card_X_mul`, `card_X_ge`, |{x unit : n - x unit}| ≥ ∏ (p-2),
and `local_theorem`. Binary Goldbach is OPEN; this is the local obstruction count.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.DensityGoldbach.AlsetriShaoLocal
open Finset

/-- `X(n) = {x ∈ ℤ_m : x and n - x are units}`. -/
def Xset (m : ℕ) [NeZero m] (n : ZMod m) : Finset (ZMod m) :=
  univ.filter (fun x => IsUnit x ∧ IsUnit (n - x))

/-- The units of `ℤ_m` as a finset. -/
def U (m : ℕ) [NeZero m] : Finset (ZMod m) := univ.filter IsUnit

lemma card_X_prime (p : ℕ) [hp : Fact p.Prime] (n : ZMod p) : p - 2 ≤ (Xset p n).card := by
  have hX : Xset p n = univ \ {0, n} := by
    ext x
    simp only [Xset, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert, mem_singleton,
      isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
    tauto
  rw [hX, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
  have : ({0, n} : Finset (ZMod p)).card ≤ 2 := card_insert_le _ _
  omega

lemma card_X_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] (h : Nat.Coprime a b)
    (n : ZMod (a * b)) :
    (Xset (a * b) n).card =
      (Xset a (ZMod.chineseRemainder h n).1).card * (Xset b (ZMod.chineseRemainder h n).2).card := by
  set e := ZMod.chineseRemainder h
  rw [← card_product, ← card_map e.toEquiv.toEmbedding]
  congr 1
  ext ⟨y1, y2⟩
  simp only [Xset, mem_map, mem_filter, mem_univ, true_and, mem_product, Equiv.toEmbedding_apply,
    RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
  constructor
  · rintro ⟨x, ⟨hx, hnx⟩, hxe⟩
    have h1 := (isUnit_map_iff e x).mpr hx
    have h2 := (isUnit_map_iff e (n - x)).mpr hnx
    rw [map_sub, hxe] at h2
    rw [hxe] at h1
    rw [Prod.isUnit_iff] at h1 h2
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  · rintro ⟨⟨h11, h12⟩, ⟨h21, h22⟩⟩
    refine ⟨e.symm (y1, y2), ⟨?_, ?_⟩, by simp⟩
    · rw [← isUnit_map_iff e, RingEquiv.apply_symm_apply, Prod.isUnit_iff]; exact ⟨h11, h21⟩
    · rw [← isUnit_map_iff e, map_sub, RingEquiv.apply_symm_apply, Prod.isUnit_iff]
      exact ⟨h12, h22⟩

/-- `|X(n)| ≥ ∏_{p ∣ m} (p - 2)` for squarefree `m`. -/
theorem card_X_ge (m : ℕ) (hm : 0 < m) (hsq : Squarefree m) (n : ZMod m) :
    haveI : NeZero m := ⟨hm.ne'⟩
    ∏ p ∈ m.primeFactors, (p - 2) ≤ (Xset m n).card := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hpp hk =>
    -- squarefree prime power: k = 1
    have hk1 : k = 1 := by
      by_contra hne
      have h2 : 2 ≤ k := by omega
      have : p * p ∣ p ^ k := by
        rw [← pow_two]; exact pow_dvd_pow p h2
      have := hsq p this
      exact hpp.one_lt.ne' (Nat.isUnit_iff.mp this)
    subst hk1
    haveI : Fact (p ^ 1).Prime := ⟨by simpa using hpp⟩
    rw [show (p ^ 1).primeFactors = {p} by simp [hpp.primeFactors], prod_singleton]
    have := card_X_prime (p ^ 1) n
    simpa using this
  | zero => exact absurd hm (lt_irrefl 0)
  | one =>
    simp only [Nat.primeFactors_one, prod_empty]
    have : NeZero 1 := ⟨one_ne_zero⟩
    exact card_pos.mpr ⟨0, by
      simp only [Xset, mem_filter, mem_univ, true_and]
      exact ⟨isUnit_of_subsingleton _, isUnit_of_subsingleton _⟩⟩
  | coprime a b ha hb hab iha ihb =>
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    haveI : NeZero (a * b) := ⟨hm.ne'⟩
    have hsa : Squarefree a := hsq.of_mul_left
    have hsb : Squarefree b := hsq.of_mul_right
    rw [card_X_mul a b hab n, Nat.Coprime.primeFactors_mul hab,
      prod_union (Nat.Coprime.disjoint_primeFactors hab)]
    exact Nat.mul_le_mul (iha (by omega) hsa _) (ihb (by omega) hsb _)

/-- **Alsetri-Shao 2024, Theorem 2.1.** For squarefree `m` and `A, B ⊆ ℤ_m^*` with
`|A| + |B| > 2 |ℤ_m^*| - ∏_{p∣m} (p - 2)`, every `n ∈ ℤ_m` is `a + b` with `a ∈ A`, `b ∈ B`. -/
theorem local_theorem (m : ℕ) [NeZero m] (hsq : Squarefree m) (A B : Finset (ZMod m))
    (hA : A ⊆ U m) (hB : B ⊆ U m)
    (hcard : 2 * ((U m).card : ℤ) - ∏ p ∈ m.primeFactors, ((p : ℤ) - 2) < A.card + B.card) :
    ∀ n : ZMod m, ∃ a ∈ A, ∃ b ∈ B, a + b = n := by
  intro n
  by_contra hno
  push Not at hno
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hX := card_X_ge m hm hsq n
  -- X ⊆ (U \ A) ∪ (n - (U \ B))
  have hsub : Xset m n ⊆ (U m \ A) ∪ ((U m \ B).image (fun y => n - y)) := by
    intro x hx
    simp only [Xset, mem_filter, mem_univ, true_and] at hx
    by_cases hxA : x ∈ A
    · apply mem_union_right
      rw [mem_image]
      refine ⟨n - x, ?_, by ring⟩
      rw [mem_sdiff]
      refine ⟨by simp [U, hx.2], fun hb => hno x hxA (n - x) hb (by ring)⟩
    · apply mem_union_left
      rw [mem_sdiff]; exact ⟨by simp [U, hx.1], hxA⟩
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 := card_image_le (s := U m \ B) (f := fun y => n - y)
  rw [card_sdiff_of_subset hA] at h1
  rw [card_sdiff_of_subset hB] at h2
  have hAU := card_le_card hA
  have hBU := card_le_card hB
  -- cast the product of natural subtractions: each p ≥ 2
  have hprod : ((∏ p ∈ m.primeFactors, (p - 2) : ℕ) : ℤ) = ∏ p ∈ m.primeFactors, ((p : ℤ) - 2) := by
    push_cast [Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    push_cast [Nat.cast_sub this]; ring
  have hXz : (∏ p ∈ m.primeFactors, ((p : ℤ) - 2)) ≤ (Xset m n).card := by
    rw [← hprod]; exact_mod_cast hX
  have : ((Xset m n).card : ℤ) ≤ ((U m).card - A.card : ℕ) + ((U m).card - B.card : ℕ) := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  push_cast [Nat.cast_sub hAU, Nat.cast_sub hBU] at this
  linarith

/-- `|ℤ_m^*| = φ(m)`. -/
lemma card_U (m : ℕ) [NeZero m] : (U m).card = Nat.totient m := by
  rw [← ZMod.card_units_eq_totient m]
  have : U m = (univ : Finset (ZMod m)ˣ).map ⟨Units.val, Units.val_injective⟩ := by
    ext x
    simp only [U, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    exact ⟨fun h => ⟨h.unit, rfl⟩, fun ⟨u, hu⟩ => hu ▸ u.isUnit⟩
  rw [this, card_map, card_univ]

/-- `φ(m) = ∏_{p∣m} (p - 1)` for squarefree `m`. -/
lemma totient_squarefree {m : ℕ} (hm : 0 < m) (hsq : Squarefree m) :
    Nat.totient m = ∏ p ∈ m.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors m
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  have hpos : 0 < ∏ p ∈ m.primeFactors, p :=
    prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])

/-- **Theorem 2.1 in the paper's form**: `|A| + |B| > φ(m) (2 - ∏_{p∣m} (p-2)/(p-1))` gives `A + B = ℤ_m`. -/
theorem local_theorem_phi (m : ℕ) [NeZero m] (hsq : Squarefree m) (A B : Finset (ZMod m))
    (hA : A ⊆ U m) (hB : B ⊆ U m)
    (hcard : (Nat.totient m : ℝ) * (2 - ∏ p ∈ m.primeFactors, (((p : ℝ) - 2) / ((p : ℝ) - 1))) <
      A.card + B.card) :
    ∀ n : ZMod m, ∃ a ∈ A, ∃ b ∈ B, a + b = n := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  apply local_theorem m hsq A B hA hB
  have ht : (Nat.totient m : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_squarefree hm hsq]; push_cast
    apply prod_congr rfl; intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [Nat.cast_sub this]; ring
  have hprod : (Nat.totient m : ℝ) * ∏ p ∈ m.primeFactors, (((p : ℝ) - 2) / ((p : ℝ) - 1)) =
      ∏ p ∈ m.primeFactors, ((p : ℝ) - 2) := by
    rw [ht, ← prod_mul_distrib]
    apply prod_congr rfl; intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast this
      linarith
    field_simp
  rw [card_U] at *
  have hz : ((2 * (Nat.totient m : ℤ) - ∏ p ∈ m.primeFactors, ((p : ℤ) - 2) : ℤ) : ℝ) <
      ((A.card + B.card : ℤ) : ℝ) := by
    push_cast; nlinarith [hprod]
  exact_mod_cast hz

end LeanLab.DensityGoldbach.AlsetriShaoLocal

namespace LeanLab.DensityGoldbach.AlsetriShaoLocal

/-- Sharpness instance after Theorem 2.1 at `m = 105 = 3 · 5 · 7`, `X₁ = Y₁ = X₂ = Y₂ = {1}`,
`X₃ = Y₃ = {1, 2, 3}`: the set `A` has `39 = φ(105)(1 - ½ · ½ · ¾)` elements and `1 ∉ A + A`;
with `Y₃ = {1, …, 4}`, `|A| + |B| = 81 = 2 φ(105) - ∏(p - 2)` and still `1 ∉ A + B`, so the bound of
Theorem 2.1 cannot be lowered here. Kernel-checked by `decide`. -/
def sharpA : Finset ℕ := (Finset.range 105).filter
  (fun a => Nat.Coprime a 105 ∧ (a % 3 = 1 ∨ a % 5 = 1 ∨ a % 7 ∈ ({1, 2, 3} : Finset ℕ)))
def sharpB : Finset ℕ := (Finset.range 105).filter
  (fun a => Nat.Coprime a 105 ∧ (a % 3 = 1 ∨ a % 5 = 1 ∨ a % 7 ∈ ({1, 2, 3, 4} : Finset ℕ)))

theorem sharp_105 : sharpA.card = 39 ∧ sharpA.card + sharpB.card = 81 ∧
    ∀ a ∈ sharpA, ∀ b ∈ sharpB, (a + b) % 105 ≠ 1 := by
  decide +kernel

end LeanLab.DensityGoldbach.AlsetriShaoLocal

