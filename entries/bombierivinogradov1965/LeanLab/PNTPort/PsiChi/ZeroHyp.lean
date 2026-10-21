module

public import LeanLab.PNTPort.PsiChi.Assembly
public import LeanLab.PNTPort.DirichletZF.RealZero
public import LeanLab.PNTPort.DirichletZF.Siegel
public import LeanLab.PNTPort.DirichletZF.SiegelLift

/-!
# Where the zeros are: the classical region, or Siegel's bound

Lab proof, unit U-5206, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics, no
cited input; Siegel's theorem is `siegel_zero` of DirichletZF/Siegel.lean, CLOUD
20261019T0413Z-cloud16, ineffective.

`zeros_classical_or_siegel`: for every `ε > 0` there are `c, c_S > 0` such that for every `N ≥ 1`
and every `χ ≠ χ₀` mod `N`, every zero `ρ` of `L(s, χ)` has `Re ρ ≤ 1 - c / log B(Im ρ)` or
`Re ρ ≤ 1 - c_S N^{-ε}`. For `N < 8` the character is lifted to modulus `8N`, where
`siegel_zero` applies; a zero of `L(s, χ)` is a zero of the lift.
-/

@[expose] public section


open Complex

namespace LeanLab.PNTPort.PsiChi

open LeanLab.PNTPort.DirichletZF

theorem zeros_classical_or_siegel (ε : ℝ) (hε : 0 < ε) : ∃ c cS : ℝ, 0 < c ∧ 0 < cS ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) ∨ ρ.re ≤ 1 - cS * (N : ℝ) ^ (-ε) := by
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  obtain ⟨cs, hcs, hsieg⟩ := siegel_zero ε hε
  refine ⟨c, cs * (8 : ℝ) ^ (-ε), hc, by positivity, fun N _ χ hχ ρ hρ ↦ ?_⟩
  rcases (hreg N χ hχ).1 ρ hρ with h | ⟨-, -, hsq, him⟩
  · exact Or.inl h
  right
  have hρr : ρ = ((ρ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hβ1 : ρ.re ≤ 1 := by
    by_contra hcon; push_neg at hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon.le hρ
  have hdvd : N ∣ 8 * N := Dvd.intro_left 8 rfl
  haveI : NeZero (8 * N) := ⟨by have := NeZero.ne N; omega⟩
  have h8 : 8 ≤ 8 * N := by have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N); omega
  have hz : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd χ) (ρ.re : ℂ) = 0 := by
    rw [L_lift hdvd hχ, ← hρr, hρ, zero_mul]
  have key := hsieg (8 * N) h8 (DirichletCharacter.changeLevel hdvd χ) (lift_ne_one hdvd hχ)
    (lift_sq hdvd hsq) ρ.re hβ1 hz
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have e : ((8 * N : ℕ) : ℝ) ^ (-ε) = (8 : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε) := by
    push_cast; rw [Real.mul_rpow (by norm_num) hN.le]
  rw [e] at key
  linarith

end LeanLab.PNTPort.PsiChi
