module

public import LeanLab.BhowmikGrimmelt2026.PrimeGauss443

/-!
A norm consequence of the induced Gauss identity.
Source: Pintz Part I page 11 display 4.1 and Montgomery Vaughan page 358 Lemma 5.2.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Lifting a character never increases its Gauss sum norm.
Source: Montgomery Vaughan page 358 Lemma 5.2, norm consequence.
The proof iterates the elementary prime lifting identity. -/
theorem gaussSum_lift_norm443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) :
    ‖gaussSum (DirichletCharacter.changeLevel hd χ) (ZMod.stdAddChar (N := q))‖ ≤
      ‖gaussSum χ (ZMod.stdAddChar (N := r))‖ := by
  have aux : ∀ d : ℕ, d ≠ 0 → ∀ (q : ℕ) [NeZero q], q = r * d → ∀ hd : r ∣ q,
      ‖gaussSum (DirichletCharacter.changeLevel hd χ) (ZMod.stdAddChar (N := q))‖ ≤
        ‖gaussSum χ (ZMod.stdAddChar (N := r))‖ := by
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
      have hklt : k < d := by
        have := Nat.pos_of_ne_zero hk0
        nlinarith [hp.two_le]
      let m := r * k
      haveI : NeZero m := ⟨mul_ne_zero (NeZero.ne r) hk0⟩
      have hq' : q = m * p := by dsimp [m]; rw [hq, hk]; ring
      have hm : r ∣ m := Nat.dvd_mul_right r k
      have hi := ih k hklt hk0 m rfl hm
      clear hq
      subst q
      rw [DirichletCharacter.changeLevel_trans χ hm (Nat.dvd_mul_right m p),
        gaussSum_lift_prime443 p hp, norm_mul, norm_neg]
      exact (mul_le_mul_of_nonneg_right
        (DirichletCharacter.norm_le_one (DirichletCharacter.changeLevel hm χ) (p : ZMod m))
        (norm_nonneg _)).trans (by simpa only [one_mul] using hi)
  obtain ⟨d, hqd⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hqd; exact NeZero.ne q hqd
  exact aux d hd0 q hqd ⟨d, hqd⟩

end LeanLab.BhowmikGrimmelt2026

