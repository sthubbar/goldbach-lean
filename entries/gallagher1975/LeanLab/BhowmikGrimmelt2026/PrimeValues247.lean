module

public import LeanLab.BhowmikGrimmelt2026.PrincipalFactor247

/-!
Prime local values for the coefficient formula on P0029 page 23 display 6.4.
Source: page 5 display 2.5 and Pintz Part I page 20 display 7.14.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The natural frequency twisted sum is a Gauss sum with a shifted standard additive character.
Source: P0029 page 23 display 6.4 and its cChi convention. -/
theorem cChi_nat_gauss247 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    cChi χ N = gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)) := by
  rw [cChi, gaussSum]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [AddChar.mulShift_spec', ← Audit1610.ee_val a]
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- At a prime not dividing the natural frequency the principal twisted sum is minus one.
Source: P0029 page 5 display 2.5 and Pintz Part I page 20 display 7.14. -/
theorem cChi_principal_prime_not_dvd247 (p N : ℕ) (hp : p.Prime) (hN : ¬ p ∣ N) :
    @cChi p ⟨hp.ne_zero⟩ (1 : DirichletCharacter ℂ p) N = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [cChi_nat_gauss247]
  apply gaussSum_one_left
  intro h
  have hx := congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) h
  change ZMod.stdAddChar (N := p) (N * 1) = 1 at hx
  rw [mul_one] at hx
  have hn : (N : ZMod p) = 0 := ZMod.injective_stdAddChar (by simpa using hx)
  exact hN (by simpa only [ZMod.natCast_eq_zero_iff] using hn)

/-- At a prime dividing the natural frequency the principal twisted sum is the totient.
Source: P0029 page 5 display 2.5 and Pintz Part I page 20 display 7.14. -/
theorem cChi_principal_prime_dvd247 (p N : ℕ) (hp : p.Prime) (hN : p ∣ N) :
    @cChi p ⟨hp.ne_zero⟩ (1 : DirichletCharacter ℂ p) N = (Nat.totient p : ℂ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : (N : ZMod p) = 0 := by simpa only [ZMod.natCast_eq_zero_iff] using hN
  rw [cChi_nat_gauss247, hn]
  have hshift : (ZMod.stdAddChar (N := p)).mulShift (0 : ZMod p) = 1 := by
    ext a
    simp [AddChar.mulShift_apply]
  rw [hshift, gaussSum_one_one, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The unramified factor has the two classical prime values.
Source: P0029 page 6 display 2.10 and Pintz Part I page 20 display 7.14. -/
theorem unramified_factor_value247 (r₁ r₂ p N : ℕ) (hp : p.Prime)
    (hp₁ : ¬ p ∣ r₁) (hp₂ : ¬ p ∣ r₂)
    (ψ₁ : DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : DirichletCharacter ℂ (compLevel r₂ p)) :
    eulerFactorGen ψ₁ ψ₂ N p =
      if p ∣ N then 1 + 1 / (Nat.totient p : ℂ)
      else 1 - 1 / (Nat.totient p : ℂ) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [unramified_factor_formula247 r₁ r₂ p hp hp₁ hp₂ ψ₁ ψ₂]
  by_cases hN : p ∣ N
  · rw [if_pos hN, cChi_principal_prime_dvd247 p N hp hN]
    have hφ : (Nat.totient p : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
    field_simp
  · rw [if_neg hN, cChi_principal_prime_not_dvd247 p N hp hN]
    ring

end LeanLab.BhowmikGrimmelt2026


