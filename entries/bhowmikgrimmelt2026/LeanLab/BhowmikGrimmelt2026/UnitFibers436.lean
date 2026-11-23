module

public import Mathlib

/-!
The unit residue fiber count used in the remaining twisted sum norm formula.
Source: Montgomery Vaughan 1975 page 359, Case 2 after display 5.3.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Each unit fiber has cardinality equal to the source totient divided by the target totient.
This multiplicative form avoids natural division.
Source: Montgomery Vaughan page 359, Case 2. -/
theorem unitsMap_fiber_card_mul436 {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (u : (ZMod m)ˣ) :
    ((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = u)).card) *
      Nat.totient m = Nat.totient q := by
  classical
  have hk := Subgroup.card_ker_mul_card_of_surjective (ZMod.unitsMap_surjective hd)
  have hcard :
      ((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = 1)).card) *
        Nat.totient m = Nat.totient q := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, MonoidHom.mem_ker,
      ZMod.card_units_eq_totient] using hk
  have hu := MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hd)
    (ZMod.unitsMap_surjective hd u) (ZMod.unitsMap_surjective hd 1)
  rw [hu]
  exact hcard

/-- The real unit fiber count is precisely the totient quotient in the twisted sum formula.
Source: Montgomery Vaughan page 359, final line of Case 2. -/
theorem unitsMap_fiber_card436 {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (u : (ZMod m)ˣ) :
    (((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = u)).card) : ℝ) =
      (Nat.totient q : ℝ) / (Nat.totient m : ℝ) := by
  have hm : (Nat.totient m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))).ne'
  apply (eq_div_iff hm).mpr
  exact_mod_cast unitsMap_fiber_card_mul436 hd u

/-- Summing a function pulled back along unit reduction multiplies its sum by the fiber count.
Source: Montgomery Vaughan page 359 Case 2 and page 360 before display 5.1. -/
theorem unitsMap_sum436 {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (F : (ZMod m)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, F (ZMod.unitsMap hd a)) =
      ((Nat.totient q : ℂ) / (Nat.totient m : ℂ)) * ∑ u : (ZMod m)ˣ, F u := by
  classical
  have hc (u : (ZMod m)ˣ) :
      (((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = u)).card) : ℂ) =
        (Nat.totient q : ℂ) / (Nat.totient m : ℂ) := by
    have h := congrArg Complex.ofReal (unitsMap_fiber_card436 hd u)
    push_cast at h
    exact h
  rw [← Finset.sum_fiberwise' Finset.univ (ZMod.unitsMap hd) F]
  simp_rw [Finset.sum_const, nsmul_eq_mul, hc]
  rw [Finset.mul_sum]

end LeanLab.BhowmikGrimmelt2026

