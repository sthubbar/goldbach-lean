module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The 3-4-1 inequality for logarithmic derivatives of Dirichlet L-functions

Lab proof, unit U-5110. AI wrote this file. Known mathematics, the classical
de la Vallee Poussin positivity step behind every zero-free region for `L(s, χ)`.
No cited input.

For a Dirichlet character `χ` mod `N`, `σ > 1` and real `t`,

  `3 Re(-L'/L(σ, χ₀)) + 4 Re(-L'/L(σ + it, χ)) + Re(-L'/L(σ + 2it, χ²)) ≥ 0`,

with `χ₀ = 1` the principal character. Termwise, `n` coprime to `N` contributes
`Λ(n) n^{-σ} (3 + 4 Re z + Re z²)` with `z = χ(n) n^{-it}` on the unit circle, and
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`; every other `n` contributes `0`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-- `3 + 4 Re z + Re z² ≥ 0` on the unit circle. -/
lemma three_four_one_unit {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h1 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  have h2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  rw [h2]
  nlinarith [sq_nonneg (z.re + 1)]

/-- The real part of the `n`-th term of the combination, as a real number. -/
lemma term_comb_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (σ : ℝ) (t : ℝ)
    (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) σ n).re
      + 4 * (term (↗χ * ↗Λ) (σ + t * I) n).re
      + (term (↗(χ ^ 2) * ↗Λ) (σ + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [term_of_ne_zero hn, Pi.mul_apply]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  -- `n^{-(σ + it)} = n^{-σ} · n^{-it}`
  have hsplit : ∀ u : ℝ, ((n : ℂ) ^ ((σ : ℂ) + u * I)) =
      ((n : ℝ) ^ σ : ℝ) * (n : ℂ) ^ ((u : ℂ) * I) := by
    intro u
    rw [Complex.cpow_add _ _ (by exact_mod_cast hn), ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow hn0.le]
  set a : ℝ := (n : ℝ) ^ σ with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn0 σ
  set w : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw1; simp at hw1
  have hw2 : (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = w ^ 2 := by
    rw [hw, ← Complex.cpow_nat_mul]
    push_cast; ring_nf
  set Lv : ℝ := Λ n with hL
  have hL0 : 0 ≤ Lv := vonMangoldt_nonneg
  have e1 : (n : ℂ) ^ (σ : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
  have e2 : (n : ℂ) ^ ((σ : ℂ) + t * I) = (a : ℂ) * w := hsplit t
  have e3 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) = (a : ℂ) * w ^ 2 := by
    have := hsplit (2 * t); push_cast at this; rw [this]
    congr 1; rw [← hw2]; push_cast; ring_nf
  rw [e1, e2, e3]
  by_cases hu : IsUnit (n : ZMod N)
  · have h1 : (1 : DirichletCharacter ℂ N) n = 1 := by
      simp [MulChar.one_apply hu]
    have hχ : ‖χ n‖ = 1 := by
      have := χ.unit_norm_eq_one hu.unit
      rwa [IsUnit.unit_spec] at this
    have hχ2 : (χ ^ 2) n = (χ n) ^ 2 := by simp [pow_two]
    rw [h1, hχ2]
    set z : ℂ := χ n * w⁻¹ with hz
    have hz1 : ‖z‖ = 1 := by simp [hz, hχ, hw1]
    have key := three_four_one_unit hz1
    have r1 : (1 * (Lv : ℂ) / (a : ℂ)).re = Lv / a := by
      rw [one_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    have r2 : (χ n * (Lv : ℂ) / ((a : ℂ) * w)).re = Lv / a * z.re := by
      rw [hz]
      have : χ n * (Lv : ℂ) / ((a : ℂ) * w) = ((Lv / a : ℝ) : ℂ) * (χ n * w⁻¹) := by
        push_cast; field_simp
      rw [this, Complex.re_ofReal_mul]
    have r3 : ((χ n) ^ 2 * (Lv : ℂ) / ((a : ℂ) * w ^ 2)).re = Lv / a * (z ^ 2).re := by
      rw [hz]
      have : (χ n) ^ 2 * (Lv : ℂ) / ((a : ℂ) * w ^ 2) = ((Lv / a : ℝ) : ℂ) * (χ n * w⁻¹) ^ 2 := by
        push_cast; field_simp
      rw [this, Complex.re_ofReal_mul]
    rw [r1, r2, r3]
    have hLa : 0 ≤ Lv / a := div_nonneg hL0 ha0.le
    nlinarith [mul_nonneg hLa key]
  · have h0 : ∀ ψ : DirichletCharacter ℂ N, ψ n = 0 := fun ψ ↦ ψ.map_nonunit hu
    simp [h0]

/-- The 3-4-1 inequality for the twisted von Mangoldt L-series, `σ > 1`. -/
theorem three_four_one_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    0 ≤ 3 * (L (↗(1 : DirichletCharacter ℂ N) * ↗Λ) σ).re
      + 4 * (L (↗χ * ↗Λ) (σ + t * I)).re
      + (L (↗(χ ^ 2) * ↗Λ) (σ + 2 * t * I)).re := by
  have s1 : LSeriesSummable (↗(1 : DirichletCharacter ℂ N) * ↗Λ) σ :=
    LSeriesSummable_twist_vonMangoldt _ (by simpa using hσ)
  have s2 : LSeriesSummable (↗χ * ↗Λ) (σ + t * I) :=
    LSeriesSummable_twist_vonMangoldt _ (by simpa using hσ)
  have s3 : LSeriesSummable (↗(χ ^ 2) * ↗Λ) (σ + 2 * t * I) :=
    LSeriesSummable_twist_vonMangoldt _ (by simpa using hσ)
  simp only [LSeries]
  rw [Complex.re_tsum s1, Complex.re_tsum s2, Complex.re_tsum s3,
    ← tsum_mul_left, ← tsum_mul_left]
  have r1 := (Complex.reCLM.summable s1).mul_left 3
  have r2 := (Complex.reCLM.summable s2).mul_left 4
  have r3 := Complex.reCLM.summable s3
  simp only [Complex.reCLM_apply] at r1 r2 r3
  rw [← r1.tsum_add r2, ← (r1.add r2).tsum_add r3]
  exact tsum_nonneg fun n ↦ term_comb_nonneg χ σ t n

/-- The 3-4-1 inequality for `-L'/L`, `σ > 1`. -/
theorem three_four_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv (LFunction (1 : DirichletCharacter ℂ N)) σ
          / LFunction (1 : DirichletCharacter ℂ N) σ).re
      + 4 * (-deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re
      + (-deriv (LFunction (χ ^ 2)) (σ + 2 * t * I) / LFunction (χ ^ 2) (σ + 2 * t * I)).re := by
  have key := three_four_one_LSeries χ hσ t
  have hre : ∀ u : ℝ, 1 < ((σ : ℂ) + u * I).re := fun u ↦ by simpa using hσ
  have conv : ∀ (ψ : DirichletCharacter ℂ N) (s : ℂ), 1 < s.re →
      -deriv (LFunction ψ) s / LFunction ψ s = L (↗ψ * ↗Λ) s := by
    intro ψ s hs
    rw [LSeries_twist_vonMangoldt_eq ψ hs, LFunction_eq_LSeries ψ hs]
    congr 2
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact LFunction_eq_LSeries ψ hz
  rw [conv _ _ (by simpa using hσ), conv _ _ (by simpa using hre t),
    conv _ _ (by simpa using hre (2 * t))]
  · exact key

end LeanLab.PNTPort.DirichletZF

