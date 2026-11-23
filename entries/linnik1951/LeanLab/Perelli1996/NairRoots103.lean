module

public import Mathlib

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.
This file contains the standard root counting argument: a primitive integer polynomial F has at
most (natDegree F)^omega(d) roots modulo a squarefree d. Lagrange's bound modulo a prime, then
the Chinese remainder theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open Polynomial

namespace LeanLab.Perelli1996.Nair103

theorem roots_prime (F : ℤ[X]) (hprim : F.IsPrimitive) (p : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter (fun b : ℕ => (p : ℤ) ∣ F.eval (b : ℤ))).card ≤ F.natDegree := by
  have : Fact p.Prime := Fact.mk hp
  set G : (ZMod p)[X] := F.map (Int.castRingHom (ZMod p)) with hG
  have hG0 : G ≠ 0 := by
    intro h
    have hdvd : (C (p : ℤ)) ∣ F := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have h0 : G.coeff i = 0 := by rw [h]; simp
      rw [hG, Polynomial.coeff_map, eq_intCast] at h0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hu := hprim _ hdvd
    have h1 : (p : ℤ).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hu
    rw [Int.natAbs_natCast] at h1
    exact hp.one_lt.ne' h1
  calc ((Finset.range p).filter (fun b : ℕ => (p : ℤ) ∣ F.eval (b : ℤ))).card
      ≤ G.roots.toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun b : ℕ => (b : ZMod p))
        · intro b hb
          have hb' : (p : ℤ) ∣ F.eval (b : ℤ) := (Finset.mem_filter.mp hb).2
          have hc : ((b : ℕ) : ZMod p) = (((b : ℤ)) : ZMod p) := by simp
          have hroot : G.eval (b : ZMod p) = 0 := by
            rw [hc, hG, Polynomial.eval_intCast_map, eq_intCast]
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb'
          have : (b : ZMod p) ∈ G.roots := (Polynomial.mem_roots hG0).mpr hroot
          simpa using this
        · intro b1 h1 b2 h2 h
          have l1 : b1 < p := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
          have l2 : b2 < p := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
          have h' : (b1 : ZMod p) = (b2 : ZMod p) := h
          rw [ZMod.natCast_eq_natCast_iff'] at h'
          rwa [Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at h'
    _ ≤ Multiset.card G.roots := Multiset.toFinset_card_le _
    _ ≤ G.natDegree := Polynomial.card_roots' _
    _ ≤ F.natDegree := Polynomial.natDegree_map_le

theorem eval_mod_dvd (F : ℤ[X]) (m b : ℕ) (h : (m : ℤ) ∣ F.eval (b : ℤ)) :
    (m : ℤ) ∣ F.eval ((b % m : ℕ) : ℤ) := by
  have hb : (b : ℤ) = (m : ℤ) * ((b / m : ℕ) : ℤ) + ((b % m : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod b m).symm
  have h1 : (m : ℤ) ∣ (b : ℤ) - ((b % m : ℕ) : ℤ) := ⟨((b / m : ℕ) : ℤ), by linarith⟩
  have h2 : (m : ℤ) ∣ F.eval (b : ℤ) - F.eval ((b % m : ℕ) : ℤ) :=
    dvd_trans h1 (Polynomial.sub_dvd_eval_sub _ _ F)
  have h3 : F.eval ((b % m : ℕ) : ℤ) =
      F.eval (b : ℤ) - (F.eval (b : ℤ) - F.eval ((b % m : ℕ) : ℤ)) := by ring
  rw [h3]
  exact dvd_sub h h2

theorem roots_mul (F : ℤ[X]) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hc : m.Coprime n) :
    ((Finset.range (m * n)).filter (fun b : ℕ => ((m * n : ℕ) : ℤ) ∣ F.eval (b : ℤ))).card ≤
      ((Finset.range m).filter (fun b : ℕ => (m : ℤ) ∣ F.eval (b : ℤ))).card *
        ((Finset.range n).filter (fun b : ℕ => (n : ℤ) ∣ F.eval (b : ℤ))).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun b : ℕ => (b % m, b % n))
  · intro b hb
    have hb' : ((m * n : ℕ) : ℤ) ∣ F.eval (b : ℤ) := (Finset.mem_filter.mp hb).2
    have hmd : (m : ℤ) ∣ F.eval (b : ℤ) :=
      dvd_trans (by rw [Nat.cast_mul]; exact dvd_mul_right _ _) hb'
    have hnd : (n : ℤ) ∣ F.eval (b : ℤ) :=
      dvd_trans (by rw [Nat.cast_mul]; exact dvd_mul_left _ _) hb'
    have g1 : b % m ∈ (Finset.range m).filter (fun b : ℕ => (m : ℤ) ∣ F.eval (b : ℤ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm), eval_mod_dvd F m b hmd⟩
    have g2 : b % n ∈ (Finset.range n).filter (fun b : ℕ => (n : ℤ) ∣ F.eval (b : ℤ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hn), eval_mod_dvd F n b hnd⟩
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨g1, g2⟩)
  · intro b1 h1 b2 h2 h
    have l1 : b1 < m * n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    have l2 : b2 < m * n := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
    have e1 : b1 % m = b2 % m := congrArg Prod.fst h
    have e2 : b1 % n = b2 % n := congrArg Prod.snd h
    have hmod : b1 ≡ b2 [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨e1, e2⟩
    exact Nat.ModEq.eq_of_lt_of_lt hmod l1 l2

theorem roots_squarefree (F : ℤ[X]) (hprim : F.IsPrimitive) (d : ℕ) (hd : Squarefree d) :
    ((Finset.range d).filter (fun b : ℕ => (d : ℤ) ∣ F.eval (b : ℤ))).card ≤
      F.natDegree ^ d.primeFactors.card := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    have hn1 : n = 1 := ((Nat.squarefree_pow_iff hp.ne_one hn.ne').mp hd).2
    subst hn1
    rw [pow_one, hp.primeFactors, Finset.card_singleton, pow_one]
    exact roots_prime F hprim p hp
  | zero => exact absurd hd not_squarefree_zero
  | one =>
    rw [Nat.primeFactors_one, Finset.card_empty, pow_zero]
    calc _ ≤ (Finset.range 1).card := Finset.card_filter_le _ _
      _ = 1 := Finset.card_range 1
  | coprime a b ha hb hab iha ihb =>
    have sa : Squarefree a := Squarefree.of_mul_left hd
    have sb : Squarefree b := Squarefree.of_mul_right hd
    rw [hab.primeFactors_mul, Finset.card_union_of_disjoint hab.disjoint_primeFactors, pow_add]
    exact le_trans (roots_mul F a b (by omega) (by omega) hab)
      (Nat.mul_le_mul (iha sa) (ihb sb))

end LeanLab.Perelli1996.Nair103
