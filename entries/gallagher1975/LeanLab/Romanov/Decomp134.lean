module

public import Mathlib

/-!
# Gallagher Lemma 9, the conductor of a real primitive character

Gallagher 1975, page 136, display 7 and its written proof.
The existing cited statement is Linnik.Decomp1532b.lemma9.
The proof counts real characters and removes a redundant prime from a bad conductor.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section


noncomputable section
namespace LeanLab.Romanov.Decomp134

open Finset

/-- The number of real characters modulo r, used in the proof on page 136. -/
def realCharacterCount (r : ℕ) : ℕ :=
  Nat.card {χ : DirichletCharacter ℂ r // χ ^ 2 = 1}

/-- The exponent of two in the number of real characters on page 136. -/
def realCharacterRank (r : ℕ) : ℕ :=
  (r.primeFactors.erase 2).card + (if 4 ∣ r then 1 else 0) + (if 8 ∣ r then 1 else 0)

/-- Gallagher page 136, finite abelian group duality identifies the two torsion counts. -/
theorem count_eq_unit_roots (r : ℕ) (hr : 0 < r) :
    realCharacterCount r = Nat.card {u : (ZMod r)ˣ // u ^ 2 = 1} := by
  letI : NeZero r := ⟨hr.ne'⟩
  let e := (MulChar.mulEquiv_units (ZMod r) ℂ).some
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun χ => by
    change χ ^ 2 = 1 ↔ (e χ) ^ 2 = 1
    rw [← map_pow, e.map_eq_one_iff])


/-- Gallagher page 136, Chinese remaindering makes the real character count multiplicative. -/
theorem count_coprime_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    realCharacterCount (a * b) = realCharacterCount a * realCharacterCount b := by
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  let e : (ZMod (a * b))ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hab).toMulEquiv).trans MulEquiv.prodUnits
  rw [count_eq_unit_roots (a * b) (Nat.mul_pos ha hb), count_eq_unit_roots a ha,
    count_eq_unit_roots b hb]
  let e1 : {u : (ZMod (a * b))ˣ // u ^ 2 = 1} ≃
      {u : (ZMod a)ˣ × (ZMod b)ˣ // u ^ 2 = 1} :=
    e.toEquiv.subtypeEquiv (fun u => by
      change u ^ 2 = 1 ↔ (e u) ^ 2 = 1
      rw [← map_pow, e.map_eq_one_iff])
  let e2 : {u : (ZMod a)ˣ × (ZMod b)ˣ // u ^ 2 = 1} ≃
      {u : (ZMod a)ˣ // u ^ 2 = 1} × {u : (ZMod b)ˣ // u ^ 2 = 1} :=
    { toFun := fun u => (⟨u.val.1, congrArg Prod.fst u.property⟩,
                         ⟨u.val.2, congrArg Prod.snd u.property⟩)
      invFun := fun u => ⟨(u.1.val,u.2.val), Prod.ext u.1.property u.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr (e1.trans e2)).trans (Nat.card_prod _ _)

/-- Gallagher page 136, standard prime power fact behind the real character count.
At odd prime powers a unit whose square is one equals one or minus one. -/
theorem odd_prime_power_roots {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e)
    (u : (ZMod (p ^ e))ˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let a : ℤ := (u : ZMod (p ^ e)).val
  have hav : (a : ZMod (p ^ e)) = u := by simp [a]
  have hs : (u : ZMod (p ^ e)) ^ 2 = 1 := congrArg (fun v : (ZMod (p ^ e))ˣ => (v : ZMod (p ^ e))) hu
  have hz : (((a - 1) * (a + 1) : ℤ) : ZMod (p ^ e)) = 0 := by
    push_cast
    rw [hav]
    calc ((u : ZMod (p ^ e)) - 1) * (u + 1) = (u : ZMod (p ^ e)) ^ 2 - 1 := by ring
      _ = 0 := by rw [hs]; ring
  have hd : (p : ℤ) ^ e ∣ (a - 1) * (a + 1) := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot : ¬ ((p : ℤ) ∣ a - 1 ∧ (p : ℤ) ∣ a + 1) := by
    rintro ⟨h1,h2⟩
    have htwo : (p : ℤ) ∣ 2 := by convert dvd_sub h2 h1 using 1 <;> ring
    have htwo' : p ∣ 2 := by exact_mod_cast htwo
    have hpeq := (Nat.dvd_prime Nat.prime_two).mp htwo'
    exact hpeq.elim hp.ne_one hp2
  rcases em ((p : ℤ) ∣ a - 1) with h | h
  · left
    have hn : ¬ (p : ℤ) ∣ a + 1 := fun h' => hnot ⟨h,h'⟩
    have hd1 := hpi.pow_dvd_of_dvd_mul_right e hn hd
    apply Units.ext
    rw [← hav]
    have hz1 : ((a - 1 : ℤ) : ZMod (p ^ e)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hd1)
    push_cast at hz1
    exact sub_eq_zero.mp hz1
  · right
    have hd1 := hpi.pow_dvd_of_dvd_mul_left e h hd
    apply Units.ext
    rw [← hav]
    have hz1 : ((a + 1 : ℤ) : ZMod (p ^ e)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hd1)
    push_cast at hz1
    exact eq_neg_of_add_eq_zero_left hz1


/-- Gallagher page 136, every positive odd prime power contributes exactly one rank. -/
theorem odd_prime_power_count {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) :
    Nat.card {u : (ZMod (p ^ e))ˣ // u ^ 2 = 1} = 2 := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let x : {u : (ZMod (p ^ e))ˣ // u ^ 2 = 1} := ⟨1, by simp⟩
  let y : {u : (ZMod (p ^ e))ˣ // u ^ 2 = 1} := ⟨-1, by simp⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    have hz := congrArg (fun u : {u : (ZMod (p ^ e))ˣ // u ^ 2 = 1} =>
      (u.val : ZMod (p ^ e))) h
    change (1 : ZMod (p ^ e)) = -1 at hz
    have htwo : (2 : ZMod (p ^ e)) = 0 := by linear_combination hz
    have hd : p ^ e ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp htwo
    have hpdiv : p ∣ 2 := (dvd_pow_self p he.ne').trans hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hpdiv).elim hp.ne_one hp2
  · ext u
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases odd_prime_power_roots hp hp2 he u.val u.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- Gallagher page 136, a square root of one in a ring is automatically a unit. -/
theorem unit_roots_count_eq_ring_roots (R : Type*) [CommRing R] :
    Nat.card {u : Rˣ // u ^ 2 = 1} = Nat.card {x : R // x ^ 2 = 1} := by
  let f : {u : Rˣ // u ^ 2 = 1} → {x : R // x ^ 2 = 1} := fun u =>
    ⟨u.val.val, congrArg (fun v : Rˣ => v.val) u.property⟩
  apply Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro u v h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  · intro x
    let hu : IsUnit x.val := IsUnit.of_pow_eq_one x.property (by decide)
    refine ⟨⟨hu.unit, ?_⟩, ?_⟩
    · apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one] using x.property
    · apply Subtype.ext
      exact hu.unit_spec

/-- Gallagher page 136, local two power count. A product of consecutive even neighbors
divisible by two to e forces one neighbor divisible by two to e minus one. -/
theorem two_power_root_reduction (e : ℕ) (he : 3 ≤ e) (a : ℤ) (hd : (2 : ℤ) ^ e ∣ (a - 1) * (a + 1)) :
    (2 : ℤ) ^ (e - 1) ∣ a - 1 ∨ (2 : ℤ) ^ (e - 1) ∣ a + 1 := by
  have hprime : Prime (2 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
  have hreduce : ∀ (x y : ℤ), y - x = 2 →
      (2 : ℤ) ^ e ∣ x * y → 2 ∣ x → 2 ∣ y →
      (2 : ℤ) ^ (e - 1) ∣ x ∨ (2 : ℤ) ^ (e - 1) ∣ y := by
    intro x y hdiff hprod hx hy
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    have hbc : c - b = 1 := by omega
    have hsmall : (2 : ℤ) ^ (e - 2) ∣ b * c := by
      have heq : (2 : ℤ) ^ e = 4 * 2 ^ (e - 2) := by
        calc (2 : ℤ) ^ e = 2 ^ (2 + (e - 2)) := by congr 1; omega
          _ = 4 * 2 ^ (e - 2) := by rw [pow_add]; norm_num
      rw [hb, hc, heq] at hprod
      have hmul : (2 * b) * (2 * c) = 4 * (b * c) := by ring
      rw [hmul] at hprod
      exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hprod
    have hpow : (2 : ℤ) ^ (e - 1) = 2 * 2 ^ (e - 2) := by
      calc (2 : ℤ) ^ (e - 1) = 2 ^ ((e - 2) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 2) := by rw [pow_succ, mul_comm]
    by_cases hb2 : 2 ∣ b
    · have hc2 : ¬ (2 : ℤ) ∣ c := by
        intro hc2
        have : (2 : ℤ) ∣ 1 := hbc ▸ dvd_sub hc2 hb2
        norm_num at this
      left
      rw [hb, hpow]
      exact mul_dvd_mul_left 2 (hprime.pow_dvd_of_dvd_mul_right (e - 2) hc2 hsmall)
    · right
      rw [hc, hpow]
      exact mul_dvd_mul_left 2 (hprime.pow_dvd_of_dvd_mul_left (e - 2) hb2 hsmall)
  by_cases hx : (2 : ℤ) ∣ a - 1
  · by_cases hy : (2 : ℤ) ∣ a + 1
    · exact hreduce _ _ (by ring) hd hx hy
    · exact Or.inl ((pow_dvd_pow (2 : ℤ) (by omega : e - 1 ≤ e)).trans
        (hprime.pow_dvd_of_dvd_mul_right e hy hd))
  · exact Or.inr ((pow_dvd_pow (2 : ℤ) (by omega : e - 1 ≤ e)).trans
      (hprime.pow_dvd_of_dvd_mul_left e hx hd))


/-- Gallagher page 136, the four possible representatives at two to e for e at least three. -/
theorem two_power_root_values (e a : ℕ) (he : 3 ≤ e) (ha : a < 2 ^ e)
    (hd : (2 : ℤ) ^ e ∣ ((a : ℤ) - 1) * ((a : ℤ) + 1)) :
    a = 1 ∨ a = 2 ^ (e - 1) + 1 ∨ a = 2 ^ (e - 1) - 1 ∨ a = 2 ^ e - 1 := by
  set H : ℕ := 2 ^ (e - 1) with hH
  have hH4 : 4 ≤ H := by
    change 2 ^ 2 ≤ 2 ^ (e - 1)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ^ e = 2 * H := by
    dsimp [H]
    calc 2 ^ e = 2 ^ ((e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := by rw [pow_succ, mul_comm]
  have ha' : (a : ℤ) < 2 * (H : ℤ) := by exact_mod_cast (htwo ▸ ha)
  have hH' : (4 : ℤ) ≤ H := by exact_mod_cast hH4
  rcases two_power_root_reduction e he a hd with h | h
  · obtain ⟨z, hz⟩ := h
    have hz' : (a : ℤ) - 1 = (H : ℤ) * z := by exact_mod_cast hz
    have hz0 : 0 ≤ z := by
      by_contra hh
      have : z ≤ -1 := by omega
      nlinarith [show (0 : ℤ) ≤ a by positivity]
    have hz2 : z < 2 := by
      by_contra hh
      have : 2 ≤ z := by omega
      nlinarith
    have hz01 : z = 0 ∨ z = 1 := by omega
    rcases hz01 with rfl | rfl
    · left; simp only [mul_zero] at hz'; omega
    · right; left; simp only [mul_one] at hz'; omega
  · obtain ⟨z, hz⟩ := h
    have hz' : (a : ℤ) + 1 = (H : ℤ) * z := by exact_mod_cast hz
    have hz0 : 1 ≤ z := by
      by_contra hh
      have : z ≤ 0 := by omega
      nlinarith [show (0 : ℤ) ≤ a by positivity]
    have hz2 : z ≤ 2 := by
      by_contra hh
      have : 3 ≤ z := by omega
      nlinarith
    have hz12 : z = 1 ∨ z = 2 := by omega
    rcases hz12 with rfl | rfl
    · right; right; left; simp only [mul_one] at hz'; omega
    · right; right; right; rw [htwo]; omega


/-- Gallagher page 136, the factor four in the real character count once eight divides the modulus. -/
theorem two_power_ring_count_four (e : ℕ) (he : 3 ≤ e) :
    Nat.card {z : ZMod (2 ^ e) // z ^ 2 = 1} = 4 := by
  classical
  letI : NeZero (2 ^ e) := ⟨by positivity⟩
  set H : ℕ := 2 ^ (e - 1) with hH
  have hH4 : 4 ≤ H := by
    change 2 ^ 2 ≤ 2 ^ (e - 1)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ^ e = 2 * H := by
    dsimp [H]
    calc 2 ^ e = 2 ^ ((e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := by rw [pow_succ, mul_comm]
  let T : Finset ℕ := {1, H + 1, H - 1, 2 * H - 1}
  have hT : ∀ a ∈ T, a < 2 ^ e := by
    intro a ha
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
    rw [htwo]
    omega
  have hroot : {z : ZMod (2 ^ e) | z ^ 2 = 1} =
      (T.image (fun a : ℕ => (a : ZMod (2 ^ e))) : Set (ZMod (2 ^ e))) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image]
    constructor
    · intro hz
      have hd : (2 : ℤ) ^ e ∣ ((z.val : ℤ) - 1) * ((z.val : ℤ) + 1) := by
        have hz0 : ((((z.val : ℤ) - 1) * ((z.val : ℤ) + 1) : ℤ) : ZMod (2 ^ e)) = 0 := by
          push_cast
          rw [ZMod.natCast_zmod_val]
          calc (z - 1) * (z + 1) = z ^ 2 - 1 := by ring
            _ = 0 := by rw [hz]; ring
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz0
      have hvals := two_power_root_values e z.val he (ZMod.val_lt z) hd
      rcases hvals with h | h | h | h
      · exact ⟨1, by simp [T], by rw [← h, ZMod.natCast_zmod_val]⟩
      · exact ⟨H + 1, by simp [T], by rw [← h, ZMod.natCast_zmod_val]⟩
      · exact ⟨H - 1, by simp [T], by rw [← h, ZMod.natCast_zmod_val]⟩
      · exact ⟨2 * H - 1, by simp [T], by rw [← htwo, ← h, ZMod.natCast_zmod_val]⟩
    · rintro ⟨a, ha, rfl⟩
      have hH2 : (2 : ZMod (2 ^ e)) * H = 0 := by
        change ((2 : ℕ) : ZMod (2 ^ e)) * (H : ZMod (2 ^ e)) = 0
        rw [← Nat.cast_mul, ← htwo]
        exact ZMod.natCast_self _
      have hHsq : (H : ZMod (2 ^ e)) ^ 2 = 0 := by
        have hd : 2 ^ e ∣ H ^ 2 := by
          dsimp [H]
          rw [← pow_mul]
          exact pow_dvd_pow 2 (by omega)
        simpa only [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr hd
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · simp
      · push_cast
        linear_combination hHsq + hH2
      · rw [Nat.cast_sub (by omega : 1 ≤ H)]
        push_cast
        linear_combination hHsq - hH2
      · rw [Nat.cast_sub (by omega : 1 ≤ 2 * H)]
        push_cast
        rw [hH2]
        norm_num
  change Nat.card {z : ZMod (2 ^ e) | z ^ 2 = 1} = 4
  rw [Nat.card_coe_set_eq, hroot, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (by
      intro a ha b hb hab
      have hv := congrArg ZMod.val hab
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (hT a ha), Nat.mod_eq_of_lt (hT b hb)] at hv
      exact hv)]
  change ({1, H + 1, H - 1, 2 * H - 1} : Finset ℕ).card = 4
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega)]
  simp


/-- Gallagher page 136, the complete two power factor in the character count.
The finite checks at moduli one, two and four close the base cases of this general statement. -/
theorem two_power_ring_count (e : ℕ) :
    Nat.card {z : ZMod (2 ^ e) // z ^ 2 = 1} =
      2 ^ ((if 2 ≤ e then 1 else 0) + (if 3 ≤ e then 1 else 0)) := by
  by_cases he : 3 ≤ e
  · rw [two_power_ring_count_four e he]
    simp [he, show 2 ≤ e by omega]
  · interval_cases e <;> norm_num [Nat.card_eq_fintype_card] <;> decide

/-- Gallagher page 136, the real character rank is additive over coprime positive factors. -/
theorem rank_coprime_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    realCharacterRank (a * b) = realCharacterRank a + realCharacterRank b := by
  classical
  have aux : ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → Odd a →
      realCharacterRank (a * b) = realCharacterRank a + realCharacterRank b := by
    intro a b ha hb hab hao
    have h2 : ¬ 2 ∣ a := hao.not_two_dvd_nat
    have h4a : ¬ 4 ∣ a := fun h => h2 ((by decide : 2 ∣ 4).trans h)
    have h8a : ¬ 8 ∣ a := fun h => h2 ((by decide : 2 ∣ 8).trans h)
    have hcp : Nat.Coprime 2 a := Nat.coprime_two_left.mpr hao
    have h4 : 4 ∣ a * b ↔ 4 ∣ b := (hcp.pow_left 2).dvd_mul_left
    have h8 : 8 ∣ a * b ↔ 8 ∣ b := (hcp.pow_left 3).dvd_mul_left
    have hd : Disjoint (a.primeFactors.erase 2) (b.primeFactors.erase 2) :=
      hab.disjoint_primeFactors.mono (erase_subset _ _) (erase_subset _ _)
    have hcard : ((a * b).primeFactors.erase 2).card =
        (a.primeFactors.erase 2).card + (b.primeFactors.erase 2).card := by
      rw [Nat.primeFactors_mul ha.ne' hb.ne', erase_union_distrib, card_union_of_disjoint hd]
    simp only [realCharacterRank, hcard, h4, h8, ite_eq_right h4a, ite_eq_right h8a]
    omega
  by_cases hao : Odd a
  · exact aux a b ha hb hab hao
  · have hbo : Odd b := by
      by_contra hbo
      have h2a : 2 ∣ a := (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hao))
      have h2b : 2 ∣ b := (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hbo))
      have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2a h2b
      rw [hab.gcd_eq_one] at this
      norm_num at this
    simpa only [mul_comm b a, add_comm (realCharacterRank b)] using aux b a hb ha hab.symm hbo


/-- LEAF. Gallagher page 136, first sentence of the proof of Lemma 9.
A primitive real character gives strictly more real characters than any proper divisor. -/
theorem primitive_count_lt {r d : ℕ} (hr : 0 < r) (hd : d ∣ r) (hdr : d < r)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (h2 : χ ^ 2 = 1) :
    realCharacterCount d < realCharacterCount r := by
  classical
  letI : NeZero r := ⟨hr.ne'⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  letI : NeZero d := ⟨hd0.ne'⟩
  let f : {ψ : DirichletCharacter ℂ d // ψ ^ 2 = 1} →
      {ψ : DirichletCharacter ℂ r // ψ ^ 2 = 1} := fun ψ =>
    ⟨DirichletCharacter.changeLevel hd ψ.val, by
      rw [← map_pow, ψ.property, map_one]⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact DirichletCharacter.changeLevel_injective hd (congrArg Subtype.val hab)
  have hmissing : (⟨χ, h2⟩ : {ψ : DirichletCharacter ℂ r // ψ ^ 2 = 1}) ∉ Set.range f := by
    rintro ⟨ψ, hψ⟩
    have heq := congrArg Subtype.val hψ
    have hf : χ.FactorsThrough d := ⟨hd, ψ.val, heq.symm⟩
    have hle : χ.conductor ≤ d := Nat.sInf_le hf
    rw [hχ] at hle
    omega
  letI := Fintype.ofFinite {ψ : DirichletCharacter ℂ d // ψ ^ 2 = 1}
  letI := Fintype.ofFinite {ψ : DirichletCharacter ℂ r // ψ ^ 2 = 1}
  simpa only [realCharacterCount, Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_of_notMem f hinj hmissing

/-- Gallagher page 136, arithmetic behind the last sentence. Removing a repeated odd prime
does not change the real character rank. -/
theorem rank_mul_odd_prime {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : 0 < t) (hpt : p ∣ t) :
    realCharacterRank (p * t) = realCharacterRank t := by
  classical
  have hpf : (p * t).primeFactors = t.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero ht.ne', hp.primeFactors]
    exact union_eq_right.mpr (singleton_subset_iff.mpr (Nat.mem_primeFactors.mpr ⟨hp, hpt, ht.ne'⟩))
  have hcp : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have h4 : 4 ∣ p * t ↔ 4 ∣ t := by
    exact (hcp.pow_left 2).dvd_mul_left
  have h8 : 8 ∣ p * t ↔ 8 ∣ t := by
    exact (hcp.pow_left 3).dvd_mul_left
  simp only [realCharacterRank, hpf, h4, h8]

/-- Gallagher page 136, the correction terms at powers of two in the real character rank. -/
theorem rank_two_pow_mul (k m : ℕ) (hm : Odd m) :
    realCharacterRank (2 ^ k * m) =
      m.primeFactors.card + (if 2 ≤ k then 1 else 0) + (if 3 ≤ k then 1 else 0) := by
  classical
  have hm0 : m ≠ 0 := by intro h; subst m; simp at hm
  have h2m : ¬ 2 ∣ m := hm.not_two_dvd_nat
  have hpf : ((2 ^ k * m).primeFactors.erase 2) = m.primeFactors := by
    by_cases hk : k = 0
    · simp [hk, erase_eq_of_notMem (fun h => h2m (Nat.dvd_of_mem_primeFactors h))]
    · rw [Nat.primeFactors_mul (by positivity) hm0, Nat.primeFactors_prime_pow hk Nat.prime_two]
      ext p
      simp only [mem_erase, mem_union, mem_singleton]
      constructor
      · rintro ⟨hne, hp | hp⟩
        · exact False.elim (hne hp)
        · exact hp
      · intro hp
        exact ⟨fun h => h2m (h ▸ Nat.dvd_of_mem_primeFactors hp), Or.inr hp⟩
  have hval : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd h2m, add_zero]
  have h4 : 4 ∣ 2 ^ k * m ↔ 2 ≤ k := by
    change 2 ^ 2 ∣ _ ↔ _
    rw [Nat.prime_two.pow_dvd_iff_le_factorization (by positivity), hval]
  have h8 : 8 ∣ 2 ^ k * m ↔ 3 ≤ k := by
    change 2 ^ 3 ∣ _ ↔ _
    rw [Nat.prime_two.pow_dvd_iff_le_factorization (by positivity), hval]
  simp only [realCharacterRank, hpf, h4, h8]


/-- LEAF. Gallagher page 136, proof of Lemma 9. The number of real characters equals
2 to the number of odd prime factors, with the two corrections for 4 and 8. -/
theorem realCharacterCount_eq (r : ℕ) (hr : 0 < r) :
    realCharacterCount r = 2 ^ realCharacterRank r := by
  classical
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ r hr
  · intro p e hp he _
    by_cases hp2 : p = 2
    · subst p
      have hrank : realCharacterRank (2 ^ e) =
          (if 2 ≤ e then 1 else 0) + (if 3 ≤ e then 1 else 0) := by
        simpa using rank_two_pow_mul e 1 (by decide)
      rw [count_eq_unit_roots _ (by positivity), unit_roots_count_eq_ring_roots, hrank]
      exact two_power_ring_count e
    · have h2 : ¬ 2 ∣ p ^ e := by
        intro h
        have h2p := Nat.prime_two.dvd_of_dvd_pow h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
      have h4 : ¬ 4 ∣ p ^ e := fun h => h2 ((by decide : 2 ∣ 4).trans h)
      have h8 : ¬ 8 ∣ p ^ e := fun h => h2 ((by decide : 2 ∣ 8).trans h)
      have hrank : realCharacterRank (p ^ e) = 1 := by
        simp [realCharacterRank, Nat.primeFactors_prime_pow he.ne' hp, Ne.symm hp2, h4, h8]
      rw [count_eq_unit_roots _ (pow_pos hp.pos e), hrank, pow_one]
      exact odd_prime_power_count hp hp2 he
  · intro h; omega
  · intro _
    rw [count_eq_unit_roots 1 (by norm_num), unit_roots_count_eq_ring_roots]
    norm_num [realCharacterRank, Nat.card_eq_fintype_card]
  · intro a b ha hb hab iha ihb _
    rw [count_coprime_mul a b (by omega) (by omega) hab, iha (by omega), ihb (by omega),
      rank_coprime_mul a b (by omega) (by omega) hab, pow_add]


/-- LEAF. Gallagher page 136, last sentence of the proof of Lemma 9.
A modulus outside display 7 has a proper divisor with the same real character rank. -/
theorem bad_conductor_divisor (r : ℕ) (hr : 0 < r)
    (hbad : ¬ ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧
      (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀)) :
    ∃ d : ℕ, 0 < d ∧ d ∣ r ∧ d < r ∧ realCharacterRank d = realCharacterRank r := by
  classical
  obtain ⟨k, m, hm, hrm⟩ := Nat.exists_eq_two_pow_mul_odd hr.ne'
  have hm0 : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    simp [this] at hrm
    omega
  by_cases hms : Squarefree m
  · by_cases hk1 : k = 1
    · refine ⟨m, hm0, ?_, ?_, ?_⟩
      · rw [hrm]; exact dvd_mul_left m (2 ^ k)
      · rw [hrm, hk1]; norm_num; omega
      · rw [hrm, hk1, rank_two_pow_mul 1 m hm]
        have hzero := rank_two_pow_mul 0 m hm
        simpa using hzero
    · have hk : k = 0 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
      rcases hk with hk | hk | hk | hk
      · exact False.elim (hbad ⟨m, hm, hms, Or.inl (by simpa [hk] using hrm)⟩)
      · exact False.elim (hbad ⟨m, hm, hms, Or.inr (Or.inl (by simpa [hk] using hrm))⟩)
      · exact False.elim (hbad ⟨m, hm, hms, Or.inr (Or.inr (by simpa [hk] using hrm))⟩)
      · refine ⟨2 ^ (k - 1) * m, by positivity, ?_, ?_, ?_⟩
        · rw [hrm]
          exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) m
        · rw [hrm]
          have hp : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
          exact Nat.mul_lt_mul_of_pos_right hp hm0
        · rw [hrm, rank_two_pow_mul (k - 1) m hm, rank_two_pow_mul k m hm]
          simp [show 2 ≤ k - 1 by omega, show 3 ≤ k - 1 by omega,
            show 2 ≤ k by omega, show 3 ≤ k by omega]
  · rw [Nat.squarefree_iff_prime_squarefree] at hms
    push Not at hms
    obtain ⟨p, hp, hpp⟩ := hms
    have hpm : p ∣ m := (dvd_mul_right p p).trans hpp
    have hp2 : p ≠ 2 := by intro h; exact hm.not_two_dvd_nat (h ▸ hpm)
    have hppr : p * p ∣ r := hpp.trans (hrm ▸ dvd_mul_left m (2 ^ k))
    have hpr : p ∣ r := (dvd_mul_right p p).trans hppr
    have hd : 0 < r / p := Nat.div_pos (Nat.le_of_dvd hr hpr) hp.pos
    have hpd : p ∣ r / p := (Nat.dvd_div_iff_mul_dvd hpr).mpr hppr
    refine ⟨r / p, hd, Nat.div_dvd_of_dvd hpr, Nat.div_lt_self hr hp.one_lt, ?_⟩
    calc realCharacterRank (r / p) = realCharacterRank (p * (r / p)) :=
          (rank_mul_odd_prime hp hp2 hd hpd).symm
      _ = realCharacterRank r := by rw [Nat.mul_div_cancel' hpr]

/-- Gallagher page 136, Lemma 9, display 7. Assembly from the three proved leaves.
The statement has exactly the hypotheses and conclusion of the existing cited lemma. -/
theorem lemma9 {r : ℕ} (hr : 0 < r) (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) :
    ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀) := by
  by_contra hbad
  obtain ⟨d, hd0, hd, hdr, heq⟩ := bad_conductor_divisor r hr hbad
  have hlt := primitive_count_lt hr hd hdr χ hχ h2
  rw [realCharacterCount_eq d hd0, realCharacterCount_eq r hr, heq] at hlt
  exact (lt_irrefl _ hlt)

end LeanLab.Romanov.Decomp134
