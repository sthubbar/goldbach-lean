module

public import LeanLab.Romanov.SigmaOne

/-!
# Residue counts for exponent tuples

Gallagher page 134, the last step of the proof of Lemma 5.
These elementary bounds support the existing SigmaOne target.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.Romanov.Residues134

open Finset
open LeanLab.Linnik.U1434Lemma21 (sv)

/-- Gallagher page 134, fixing a residue fixes the exponent modulo the order. -/
theorem pow_residue_count_le_nat {q : ℕ} (hq : Odd q) (c L : ℕ) :
    #{μ ∈ Icc 1 L | 2 ^ μ % q = c} ≤ L / orderOf (2 : ZMod q) + 1 := by
  classical
  calc
    #{μ ∈ Icc 1 L | 2 ^ μ % q = c} ≤ #(range (L / orderOf (2 : ZMod q) + 1)) := by
      apply card_le_card_of_injOn (fun μ => μ / orderOf (2 : ZMod q))
      · intro μ hμ
        simp only [mem_coe, mem_filter, mem_Icc] at hμ
        rw [mem_coe, mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hμ.1.2)
      · intro a ha b hb hab
        simp only [mem_coe, mem_filter, mem_Icc] at ha hb
        change a / orderOf (2 : ZMod q) = b / orderOf (2 : ZMod q) at hab
        have hpow : 2 ^ a ≡ 2 ^ b [MOD q] := by
          change 2 ^ a % q = 2 ^ b % q
          exact ha.2.trans hb.2.symm
        have hu : IsUnit (2 : ZMod q) :=
          ZMod.isUnit_prime_of_not_dvd Nat.prime_two hq.not_two_dvd_nat
        have heq : (2 : ZMod q) ^ a = (2 : ZMod q) ^ b := by
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpow
        have hequ : hu.unit ^ a = hu.unit ^ b := Units.ext heq
        have hmod := pow_eq_pow_iff_modEq.mp hequ
        have hord : orderOf (2 : ZMod q) = orderOf hu.unit := @orderOf_units (ZMod q) _ hu.unit
        rw [← hord] at hmod
        change a % orderOf (2 : ZMod q) = b % orderOf (2 : ZMod q) at hmod
        calc a = a % orderOf (2 : ZMod q) + orderOf (2 : ZMod q) * (a / orderOf (2 : ZMod q)) := (Nat.mod_add_div a _).symm
          _ = b % orderOf (2 : ZMod q) + orderOf (2 : ZMod q) * (b / orderOf (2 : ZMod q)) := by rw [hmod, hab]
          _ = b := Nat.mod_add_div b _
    _ = _ := card_range _

/-- Gallagher page 134, the real valued form of the one variable residue bound. -/
theorem pow_residue_count_le {q : ℕ} (hq : Odd q) (c L : ℕ) :
    (#{μ ∈ Icc 1 L | 2 ^ μ % q = c} : ℝ) ≤
      (L : ℝ) / orderOf (2 : ZMod q) + 1 := by
  calc
    (#{μ ∈ Icc 1 L | 2 ^ μ % q = c} : ℝ) ≤
        ((L / orderOf (2 : ZMod q) + 1 : ℕ) : ℝ) := by
      exact_mod_cast pow_residue_count_le_nat hq c L
    _ ≤ _ := by
      push_cast
      exact add_le_add Nat.cast_div_le le_rfl

/-- Gallagher page 134, fix every exponent except the first. Tuples are counted with multiplicity. -/
theorem tuple_residue_count_le_nat {q : ℕ} (hq : Odd q) (K L c : ℕ) :
    #{ν : Fin (K + 1) → Fin L | sv ν % q = c} ≤
      L ^ K * (L / orderOf (2 : ZMod q) + 1) := by
  classical
  let E := orderOf (2 : ZMod q)
  have hsplit (ν : Fin (K + 1) → Fin L) :
      sv ν = 2 ^ ((ν 0 : ℕ) + 1) + sv (Fin.tail ν) := by
    exact Fin.sum_univ_succ _
  calc
    #{ν : Fin (K + 1) → Fin L | sv ν % q = c} ≤
        #((univ : Finset (Fin K → Fin L)) ×ˢ range (L / E + 1)) := by
      apply card_le_card_of_injOn (fun ν : Fin (K + 1) → Fin L =>
        (Fin.tail ν, ((ν 0 : ℕ) + 1) / E))
      · intro ν hν
        simp only [mem_coe, mem_product, mem_univ, true_and, mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (by have := (ν 0).isLt; omega))
      · intro a ha b hb hab
        have ht : Fin.tail a = Fin.tail b := congrArg Prod.fst hab
        have hd : ((a 0 : ℕ) + 1) / E = ((b 0 : ℕ) + 1) / E := congrArg Prod.snd hab
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        have hsum : sv a ≡ sv b [MOD q] := ha'.trans hb'.symm
        rw [hsplit a, hsplit b, ht] at hsum
        have hpow := Nat.ModEq.add_right_cancel' (sv (Fin.tail b)) hsum
        have hu : IsUnit (2 : ZMod q) :=
          ZMod.isUnit_prime_of_not_dvd Nat.prime_two hq.not_two_dvd_nat
        have heq : (2 : ZMod q) ^ ((a 0 : ℕ) + 1) = (2 : ZMod q) ^ ((b 0 : ℕ) + 1) := by
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpow
        have hequ : hu.unit ^ ((a 0 : ℕ) + 1) = hu.unit ^ ((b 0 : ℕ) + 1) := Units.ext heq
        have hmod := pow_eq_pow_iff_modEq.mp hequ
        have hord : E = orderOf hu.unit := @orderOf_units (ZMod q) _ hu.unit
        rw [← hord] at hmod
        change ((a 0 : ℕ) + 1) % E = ((b 0 : ℕ) + 1) % E at hmod
        have hfirst : a 0 = b 0 := by
          apply Fin.ext
          have haa := Nat.mod_add_div ((a 0 : ℕ) + 1) E
          have hbb := Nat.mod_add_div ((b 0 : ℕ) + 1) E
          rw [hmod, hd] at haa
          omega
        funext i
        exact Fin.cases hfirst (fun j => congrFun ht j) i
    _ = _ := by simp [E]

/-- Gallagher page 134, the real bound after fixing every other exponent. -/
theorem tuple_residue_count_le {q : ℕ} (hq : Odd q) (K L c : ℕ) :
    (#{ν : Fin (K + 1) → Fin L | sv ν % q = c} : ℝ) ≤
      (L : ℝ) ^ (K + 1) / orderOf (2 : ZMod q) + (L : ℝ) ^ K := by
  have h : (#{ν : Fin (K + 1) → Fin L | sv ν % q = c} : ℝ) ≤
      (L : ℝ) ^ K * (((L / orderOf (2 : ZMod q) : ℕ) : ℝ) + 1) := by
    exact_mod_cast tuple_residue_count_le_nat hq K L c
  calc
    (#{ν : Fin (K + 1) → Fin L | sv ν % q = c} : ℝ) ≤
        (L : ℝ) ^ K * (((L / orderOf (2 : ZMod q) : ℕ) : ℝ) + 1) := h
    _ ≤ (L : ℝ) ^ K * ((L : ℝ) / orderOf (2 : ZMod q) + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add Nat.cast_div_le le_rfl) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Gallagher page 134, the same count for positive guarded remainders in SigmaOne. -/
theorem remainder_count_le {q : ℕ} (hq : Odd q) (K L N : ℕ)
    (hN : ∀ ν : Fin (K + 1) → Fin L, sv ν ≤ N) :
    (#{ν : Fin (K + 1) → Fin L | q ∣ N - sv ν} : ℝ) ≤
      (L : ℝ) ^ (K + 1) / orderOf (2 : ZMod q) + (L : ℝ) ^ K := by
  classical
  have heq : (univ.filter (fun ν : Fin (K + 1) → Fin L => q ∣ N - sv ν)) =
      univ.filter (fun ν : Fin (K + 1) → Fin L => sv ν % q = N % q) := by
    ext ν
    simp only [mem_filter, mem_univ, true_and]
    exact (Nat.modEq_iff_dvd' (hN ν)).symm
  rw [heq]
  exact tuple_residue_count_le hq K L (N % q)

end LeanLab.Romanov.Residues134
