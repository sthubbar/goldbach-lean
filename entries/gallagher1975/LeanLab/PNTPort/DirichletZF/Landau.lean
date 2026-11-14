module

public import LeanLab.PNTPort.DirichletZF.SiegelLift

/-!
# Landau's theorem: one exceptional character up to modulus `Q`

Lab proof, unit U-5112. AI wrote this file. Known mathematics, no cited input; Landau 1918,
Davenport chapter 14, Montgomery-Vaughan Corollary 11.9 in the form for characters of different
moduli.

`landau`: there is an absolute `c > 0` such that for every `Q ≥ 2`, any two non-principal
characters `χ₁` mod `q₁` and `χ₂` mod `q₂` with `q₁, q₂ ≤ Q` whose L-functions both vanish at
real points `β₁, β₂ ≥ 1 - c / log Q` induce the same character mod `q₁q₂`. So for primitive
characters, at most one of modulus up to `Q` has such a zero. The proof lifts both to
`q₁q₂` and applies `one_exceptional` there.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex

theorem landau : ∃ c : ℝ, 0 < c ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂],
    q₁ ≤ Q → q₂ ≤ Q → ∀ (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
      χ₁ ≠ 1 → χ₂ ≠ 1 → ∀ β₁ β₂ : ℝ, β₁ ≤ 1 → β₂ ≤ 1 →
        DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
        1 - c / Real.log Q ≤ β₁ → 1 - c / Real.log Q ≤ β₂ →
          DirichletCharacter.changeLevel (Nat.dvd_mul_right q₁ q₂) χ₁ =
            DirichletCharacter.changeLevel (Nat.dvd_mul_left q₂ q₁) χ₂ := by
  obtain ⟨c₅, hc₅, -, hexc⟩ := one_exceptional
  set L₀ := Real.log (6 * Z) with hL₀
  have hZ := one_le_Z
  have hL₀0 : 0 ≤ L₀ := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ := L₀ / Real.log 2 + 2 with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨c₅ / κ, by positivity, fun Q hQ q₁ q₂ _ _ h1 h2 χ₁ χ₂ hχ₁ hχ₂ β₁ β₂ hb1 hb2 hz1 hz2
    hβ₁ hβ₂ ↦ ?_⟩
  set M := q₁ * q₂
  haveI : NeZero M := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  have d₁ : q₁ ∣ M := Nat.dvd_mul_right q₁ q₂
  have d₂ : q₂ ∣ M := Nat.dvd_mul_left q₂ q₁
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : Real.log 2 ≤ Real.log Q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have hlQ : 0 < Real.log Q := by linarith
  -- `log B_M(0) ≤ κ log Q`
  have hM : (M : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have : M ≤ Q * Q := Nat.mul_le_mul h1 h2
    have : (M : ℝ) ≤ (Q : ℝ) * Q := by exact_mod_cast this
    nlinarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hB : Real.log (Bt M 0) ≤ κ * Real.log Q := by
    have e : Bt M 0 = (6 * Z) * M := by unfold Bt; simp; ring
    rw [e, Real.log_mul (by positivity) hM0.ne']
    have : Real.log M ≤ 2 * Real.log Q := by
      have := Real.log_le_log hM0 hM
      rwa [Real.log_pow] at this
    have : L₀ ≤ L₀ / Real.log 2 * Real.log Q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlogQ hL₀0
    have e2 : (L₀ / Real.log 2 + 2) * Real.log Q = L₀ / Real.log 2 * Real.log Q +
        2 * Real.log Q := by ring
    rw [hκ, e2, ← hL₀]; linarith
  have hBpos : 0 < Real.log (Bt M 0) := by linarith [one_le_log_Bt (N := M) 0]
  have hcmp : c₅ / κ / Real.log Q ≤ c₅ / Real.log (Bt M 0) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc₅.le hBpos (by linarith)
  have hz1' : DirichletCharacter.LFunction (DirichletCharacter.changeLevel d₁ χ₁) β₁ = 0 := by
    rw [L_lift d₁ hχ₁, hz1, zero_mul]
  have hz2' : DirichletCharacter.LFunction (DirichletCharacter.changeLevel d₂ χ₂) β₂ = 0 := by
    rw [L_lift d₂ hχ₂, hz2, zero_mul]
  have hc0 : 0 ≤ c₅ / Real.log (Bt M 0) := by positivity
  exact hexc M _ _ (lift_ne_one d₁ hχ₁) (lift_ne_one d₂ hχ₂) β₁ β₂ hz1' hz2'
    (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_im, abs_zero]; exact hc0)
    (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_im, abs_zero]; exact hc0)

end LeanLab.PNTPort.DirichletZF
