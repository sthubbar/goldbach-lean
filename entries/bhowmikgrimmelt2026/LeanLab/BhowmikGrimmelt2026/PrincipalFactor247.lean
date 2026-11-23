module

public import LeanLab.BhowmikGrimmelt2026.Audit1610

/-!
Unramified local arithmetic for the component Euler product on P0029 page 23 display 6.4.
The general coefficient and finite expansion leaves remain OPEN.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The principal level one pair has only the zeroth and first prime power terms.
Source: P0029 page 23 display 6.4 and Pintz Part I page 20 display 7.14. -/
theorem principal_factor_formula247 (N : ℤ) (p : ℕ) (hp : p.Prime) :
    eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) N p =
      1 + @cChi p ⟨hp.ne_zero⟩ (1 : DirichletCharacter ℂ p) N / (Nat.totient p : ℂ) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  unfold eulerFactorGen
  rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  · rw [dif_neg (hne 0), dif_neg (hne 1),
      Audit1610.Aq_congr _ _ _ (pow_zero p) (i' := ⟨one_ne_zero⟩),
      Audit1610.Aq_congr _ _ _ (pow_one p) (i' := ⟨hp.ne_zero⟩),
      Audit1610.Aq_one N 1 (one_dvd _), Audit1610.Aq_one N p (one_dvd _),
      Audit1610.tauConj_one_level_one, Audit1610.cChi_one_level_one,
      Audit1610.tauConj_one_prime, Nat.totient_one]
    ring
  · intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [dif_neg (hne k)]
    haveI : NeZero (p ^ k) := ⟨hne k⟩
    exact Audit1610.Aq_one_high N p k hp hk2 (one_dvd _)

/-- Any characters whose levels are one have the principal Euler factor formula.
Source: P0029 page 23 display 6.4, the conductor one specialization. -/
theorem level_one_factor_formula247 {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hr₁ : r₁ = 1) (hr₂ : r₂ = 1) (N : ℤ) (p : ℕ) (hp : p.Prime) :
    eulerFactorGen χ₁ χ₂ N p =
      1 + @cChi p ⟨hp.ne_zero⟩ (1 : DirichletCharacter ℂ p) N / (Nat.totient p : ℂ) ^ 2 := by
  subst r₁
  subst r₂
  rw [DirichletCharacter.level_one' χ₁ rfl, DirichletCharacter.level_one' χ₂ rfl]
  exact principal_factor_formula247 N p hp

/-- Away from both conductors, every component pair has the principal local factor.
No component product hypothesis or global series identity is needed.
Source: P0029 page 23 display 6.4 and Pintz Part I page 20 display 7.14. -/
theorem unramified_factor_formula247 (r₁ r₂ : ℕ) (p : ℕ) (hp : p.Prime)
    (hp₁ : ¬ p ∣ r₁) (hp₂ : ¬ p ∣ r₂)
    (ψ₁ : DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : DirichletCharacter ℂ (compLevel r₂ p)) (N : ℤ) :
    eulerFactorGen ψ₁ ψ₂ N p =
      1 + @cChi p ⟨hp.ne_zero⟩ (1 : DirichletCharacter ℂ p) N / (Nat.totient p : ℂ) ^ 2 := by
  apply level_one_factor_formula247 ψ₁ ψ₂ _ _ N p hp
  · simp [compLevel, Nat.factorization_eq_zero_of_not_dvd hp₁]
  · simp [compLevel, Nat.factorization_eq_zero_of_not_dvd hp₂]

end LeanLab.BhowmikGrimmelt2026

