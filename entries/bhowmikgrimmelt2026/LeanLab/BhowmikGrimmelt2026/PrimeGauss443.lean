module

public import LeanLab.BhowmikGrimmelt2026.GaussReduction443

/-!
Elementary induced Gauss sums behind Montgomery Vaughan 1975 page 358 Lemma 5.2.
The frequency reduction in the written proof is on pages 359 and 360.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- A proper periodic pullback is orthogonal to the standard additive character.
Source: the residue cancellation used in Montgomery Vaughan page 359. -/
theorem periodic_gauss_zero443 {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (hlt : m < q) (F : ZMod m → ℂ) :
    ∑ a : ZMod q, F ((ZMod.castHom hd (ZMod m)) a) * ZMod.stdAddChar a = 0 := by
  let S := ∑ a : ZMod q, F ((ZMod.castHom hd (ZMod m)) a) * ZMod.stdAddChar a
  have hz : (m : ZMod q) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (NeZero.ne m)) hlt
      ((ZMod.natCast_eq_zero_iff m q).mp hz)
  have he : (ZMod.stdAddChar (m : ZMod q) : ℂ) ≠ 1 := by
    intro he
    apply hz
    apply ZMod.injective_stdAddChar (N := q)
    simpa using he
  have hshift : S = S * ZMod.stdAddChar (m : ZMod q) := by
    conv_lhs => rw [show S = ∑ a : ZMod q,
      F ((ZMod.castHom hd (ZMod m)) a) * ZMod.stdAddChar a from rfl,
      ← Equiv.sum_comp (Equiv.addRight (m : ZMod q))]
    simp only [Equiv.coe_addRight, map_add, map_natCast, ZMod.natCast_self, add_zero,
      AddChar.map_add_eq_mul]
    dsimp [S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hprod : S * (1 - ZMod.stdAddChar (m : ZMod q)) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (Ne.symm he))

/-- Removing residues divisible by a prime leaves the lifted character.
Source: Montgomery Vaughan page 358 Lemma 5.2, induced character restriction. -/
theorem changeLevel_prime_value443 {m : ℕ} [NeZero m] (p : ℕ) (hp : p.Prime) [NeZero (m * p)]
    (χ : DirichletCharacter ℂ m) (a : ZMod (m * p)) :
    DirichletCharacter.changeLevel (Nat.dvd_mul_right m p) χ a =
      χ ((ZMod.castHom (Nat.dvd_mul_right m p) (ZMod m)) a) -
        if p ∣ a.val then χ ((ZMod.castHom (Nat.dvd_mul_right m p) (ZMod m)) a) else 0 := by
  haveI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) hp.ne_zero⟩
  classical
  have hc : ((ZMod.castHom (Nat.dvd_mul_right m p) (ZMod m)) a) = (a.val : ZMod m) := by
    rw [← ZMod.natCast_zmod_val a]
    simp
  have hu : IsUnit a ↔ (a.val.Coprime m ∧ ¬p ∣ a.val) := by
    have hnat : IsUnit (a.val : ZMod (m * p)) ↔
        (a.val.Coprime m ∧ ¬p ∣ a.val) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
      exact and_congr Iff.rfl ⟨fun h => hp.coprime_iff_not_dvd.mp h.symm,
        fun h => (hp.coprime_iff_not_dvd.mpr h).symm⟩
    simpa only [ZMod.natCast_zmod_val] using hnat
  by_cases hunit : IsUnit a
  · have hd := (hu.mp hunit).2
    rw [if_neg hd, sub_zero]
    obtain ⟨u, rfl⟩ := hunit
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd χ _ u
  · rw [MulChar.map_nonunit _ hunit]
    by_cases hd : p ∣ a.val
    · simp [hd]
    · rw [if_neg hd, sub_zero, hc]
      symm
      exact MulChar.map_nonunit χ (by
        rw [ZMod.isUnit_iff_coprime]
        intro hm
        exact hunit (hu.mpr ⟨hm, hd⟩))

/-- Summing over multiples of p in modulus m times p equals summing over modulus m.
Source: the residue grouping underlying Montgomery Vaughan page 358 Lemma 5.2. -/
theorem sum_multiples443 (m p : ℕ) [NeZero m] [NeZero p] [NeZero (m * p)] (F : ZMod (m * p) → ℂ) :
    (∑ a : ZMod (m * p), if p ∣ a.val then F a else 0) =
      ∑ b : ZMod m, F ((p * b.val : ℕ) : ZMod (m * p)) := by
  haveI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
  classical
  let f : ZMod m → ZMod (m * p) := fun b => ((p * b.val : ℕ) : ZMod (m * p))
  have hval (b : ZMod m) : (f b).val = p * b.val := by
    apply ZMod.val_natCast_of_lt
    rw [mul_comm m p]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt b) (Nat.pos_of_ne_zero (NeZero.ne p))
  have hinj : Function.Injective f := by
    intro a b h
    apply ZMod.val_injective
    have h' := congrArg ZMod.val h
    rw [hval, hval] at h'
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne p)) h'
  symm
  apply Fintype.sum_of_injective f hinj (fun b => F (f b))
    (fun a => if p ∣ a.val then F a else 0) ?_ ?_
  · intro a ha
    apply if_neg
    intro hd
    obtain ⟨k, hk⟩ := hd
    have hklt : k < m := by
      have ht := ZMod.val_lt a
      rw [hk, mul_comm m p] at ht
      exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero (NeZero.ne p))).mp ht
    have hb : f (k : ZMod m) = a := by
      apply ZMod.val_injective
      rw [hval, ZMod.val_natCast_of_lt hklt]
      exact hk.symm
    exact ha ⟨k, hb⟩
  · intro b
    rw [hval, if_pos (dvd_mul_right p b.val)]

/-- The removed multiples contribute the prime character value times the original Gauss sum.
Source: Montgomery Vaughan page 358 Lemma 5.2. -/
theorem prime_removed_gauss443 {m : ℕ} [NeZero m] (p : ℕ) (hp : p.Prime) [NeZero (m * p)]
    (χ : DirichletCharacter ℂ m) :
    (∑ a : ZMod (m * p), if p ∣ a.val then
      χ ((ZMod.castHom (Nat.dvd_mul_right m p) (ZMod m)) a) * ZMod.stdAddChar a else 0) =
      χ (p : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) hp.ne_zero⟩
  rw [sum_multiples443, gaussSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have he : ZMod.stdAddChar ((p * b.val : ℕ) : ZMod (m * p)) =
      ZMod.stdAddChar (b : ZMod m) := by
    have h := stdAddChar_factor443 (Nat.dvd_mul_right m p) p rfl 1
      ((b.val : ℕ) : ZMod (m * p))
    have hblt : b.val < m * p := lt_of_lt_of_le (ZMod.val_lt b)
      (Nat.le_mul_of_pos_right m hp.pos)
    simpa only [mul_one, one_mul, Int.cast_mul, Int.cast_one, Int.cast_natCast, Nat.cast_mul,
      ZMod.val_natCast_of_lt hblt, ZMod.natCast_zmod_val] using h
  rw [he]
  simp only [map_natCast, Nat.cast_mul, map_mul, ZMod.natCast_zmod_val]
  ring

/-- Lifting by one prime multiplies the Gauss sum by the negative character value of that prime.
Source: the induced Gauss formula in Montgomery Vaughan page 358 Lemma 5.2.
This identity holds without primitivity. -/
theorem gaussSum_lift_prime443 {m : ℕ} [NeZero m] (p : ℕ) (hp : p.Prime) [NeZero (m * p)]
    (χ : DirichletCharacter ℂ m) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right m p) χ)
        (ZMod.stdAddChar (N := m * p)) =
      -χ (p : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by
  haveI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) hp.ne_zero⟩
  unfold gaussSum
  simp_rw [changeLevel_prime_value443 p hp χ, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib,
    periodic_gauss_zero443 (Nat.dvd_mul_right m p)
      (by nlinarith [hp.two_le, Nat.pos_of_ne_zero (NeZero.ne m)]),
    prime_removed_gauss443 p hp χ]
  simp only [zero_sub, neg_mul, gaussSum]

end LeanLab.BhowmikGrimmelt2026


