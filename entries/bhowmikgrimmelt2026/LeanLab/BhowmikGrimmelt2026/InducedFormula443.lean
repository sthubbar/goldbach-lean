module

public import LeanLab.BhowmikGrimmelt2026.InducedGauss443

/-!
The induced Gauss formula of Pintz Part I page 11 display 4.1.
The elementary prime lifting proof extends it to every source character.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The full induced Gauss sum formula.
Source: Montgomery Vaughan page 358 Lemma 5.2 and Pintz Part I page 11 display 4.1.
The formula follows by iterating the proved prime lifting identity. -/
theorem gaussSum_lift_formula443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) :
    gaussSum (DirichletCharacter.changeLevel hd χ) (ZMod.stdAddChar (N := q)) =
      (ArithmeticFunction.moebius (q / r) : ℂ) * χ ((q / r : ℕ) : ZMod r) *
        gaussSum χ (ZMod.stdAddChar (N := r)) := by
  have aux : ∀ d : ℕ, d ≠ 0 → ∀ (q : ℕ) [NeZero q], q = r * d → ∀ hd : r ∣ q,
      gaussSum (DirichletCharacter.changeLevel hd χ) (ZMod.stdAddChar (N := q)) =
        (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod r) *
          gaussSum χ (ZMod.stdAddChar (N := r)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd0 q hq0 hq hdq
      by_cases hd1 : d = 1
      · subst d
        simp only [mul_one] at hq
        subst q
        simp
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨k, hk⟩ := hpd
      have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hd0 hk
      have hklt : k < d := by nlinarith [Nat.pos_of_ne_zero hk0, hp.two_le]
      let m := r * k
      haveI : NeZero m := ⟨mul_ne_zero (NeZero.ne r) hk0⟩
      have hm : r ∣ m := Nat.dvd_mul_right r k
      have hi := ih k hklt hk0 m rfl hm
      have hq' : q = m * p := by dsimp [m]; rw [hq, hk]; ring
      clear hq
      subst q
      rw [DirichletCharacter.changeLevel_trans χ hm (Nat.dvd_mul_right m p),
        gaussSum_lift_prime443 p hp]
      by_cases hpr : p ∣ r
      · have hpm : p ∣ m := hpr.trans hm
        have hn : ¬ IsUnit (p : ZMod m) := by
          rw [ZMod.isUnit_iff_coprime]
          exact fun h => (hp.coprime_iff_not_dvd.mp h) hpm
        rw [MulChar.map_nonunit _ hn]
        have hχp : χ (p : ZMod r) = 0 := MulChar.map_nonunit _ (by
          rw [ZMod.isUnit_iff_coprime]
          exact fun h => (hp.coprime_iff_not_dvd.mp h) hpr)
        rw [hk, Nat.cast_mul, map_mul χ, hχp]
        ring
      · by_cases hpk : p ∣ k
        · have hpm : p ∣ m := hpk.trans (Nat.dvd_mul_left k r)
          have hn : ¬ IsUnit (p : ZMod m) := by
            rw [ZMod.isUnit_iff_coprime]
            exact fun h => (hp.coprime_iff_not_dvd.mp h) hpm
          have hsq : ¬ Squarefree d := by
            intro hs
            apply (Nat.squarefree_iff_prime_squarefree.mp hs p hp)
            obtain ⟨j, hj⟩ := hpk
            rw [hk, hj]
            exact ⟨j, by ring⟩
          rw [MulChar.map_nonunit _ hn, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
          simp
        · have hpm : ¬p ∣ m := by
            dsimp [m]
            exact fun h => (hp.dvd_mul.mp h).elim hpr hpk
          have hu : IsUnit (p : ZMod m) :=
            (ZMod.isUnit_iff_coprime _ _).mpr (hp.coprime_iff_not_dvd.mpr hpm)
          have hc : DirichletCharacter.changeLevel hm χ (p : ZMod m) = χ (p : ZMod r) := by
            rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd,
              hu.unit_spec, ZMod.cast_natCast hm]
          have hμ : ArithmeticFunction.moebius d =
              -ArithmeticFunction.moebius k := by
            rw [hk, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
              (hp.coprime_iff_not_dvd.mpr hpk), ArithmeticFunction.moebius_apply_prime hp]
            ring
          rw [hc, hi, hμ, hk, Nat.cast_mul, map_mul χ]
          push_cast
          ring
  obtain ⟨d, hqd⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hqd; exact NeZero.ne q hqd
  have hquot : q / r = d := by rw [hqd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne r))]
  rw [hquot]
  exact aux d hd0 q hqd ⟨d, hqd⟩

end LeanLab.BhowmikGrimmelt2026
