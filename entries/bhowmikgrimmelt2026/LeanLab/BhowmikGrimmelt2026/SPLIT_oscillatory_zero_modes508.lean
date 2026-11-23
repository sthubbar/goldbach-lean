module

public import LeanLab.BhowmikGrimmelt2026.Decomp508a

/-!
Split of `oscillatory_zero_modes508`. The single retained zero mode is bounded in the two
frequency regimes `|β| X ≤ 1` and `1 ≤ |β| X`, and the zero list is counted with reciprocal
weights. Each LEAF carries one open input; the assembly
`oscillatory_zero_modes508_split` restates the sealed estimate and has no unproved step.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The retained zero modes written as a sum of single-mode Abel expressions. -/
private theorem zeroTwist508_unfold {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (X : ℕ) (β : ℝ) :
    zeroTwist508 χ Z X β =
      ∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))) := rfl

/-- LEAF: one retained zero mode, small frequency regime. For a single `ρ` with
`0 < ρ.re ≤ Θ` and `|β| X ≤ 1` the Abel expression of that mode, which is the difference
between the endpoint term and the summed phase increments, is at most `8 X^Θ / ‖ρ‖`.
This is the summation by parts step for one mode only. OPEN. -/
theorem zero_mode_small_frequency508 {Θ : ℝ} (hΘ1 : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρΘ : ρ.re ≤ Θ) {β : ℝ} (hβ : |β| * (X : ℝ) ≤ 1) :
    ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      8 * (X : ℝ) ^ Θ / ‖ρ‖ := by
  have hX1' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  have hd : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hnorm_pow : ∀ n : ℕ, ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ ρ.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.cast_zero, Complex.zero_cpow hρne]
      simpa using (Real.zero_rpow (ne_of_gt hρ0)).symm
    · rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  have hstep : ∀ n : ℕ,
      ‖ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
    intro n
    rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring, ee_add150]
    rw [show ee ((n : ℝ) * β) * ee β - ee ((n : ℝ) * β) = ee ((n : ℝ) * β) * (ee β - 1) by ring,
      norm_mul, norm_ee150, one_mul]
    exact norm_ee_sub_one_le502 β
  have hterm : ∀ n ∈ Finset.range X,
      ‖(n : ℂ) ^ ρ / ρ * (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
        (X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|) := by
    intro n hn
    have hnX : (n : ℝ) ≤ (X : ℝ) := by
      have hlt : n < X := Finset.mem_range.mp hn
      exact_mod_cast le_of_lt hlt
    have hpow : (n : ℝ) ^ ρ.re ≤ (X : ℝ) ^ ρ.re :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnX (le_of_lt hρ0)
    have hdiv : (n : ℝ) ^ ρ.re / ‖ρ‖ ≤ (X : ℝ) ^ ρ.re / ‖ρ‖ :=
      (div_le_div_iff_of_pos_right hd).mpr hpow
    rw [norm_mul, norm_div, hnorm_pow n]
    exact mul_le_mul hdiv (hstep n) (norm_nonneg _) (by positivity)
  have hkey : (X : ℝ) ^ ρ.re / ‖ρ‖ +
      (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) ≤
      8 * (X : ℝ) ^ Θ / ‖ρ‖ := by
    have hbX : (X : ℝ) * (2 * Real.pi * |β|) ≤ 2 * Real.pi := by
      have h1 : (X : ℝ) * (2 * Real.pi * |β|) = 2 * Real.pi * (|β| * (X : ℝ)) := by ring
      rw [h1]
      nlinarith [Real.pi_pos]
    have hconst : (1 : ℝ) + 2 * Real.pi ≤ 8 := by
      have := Real.pi_lt_d2
      linarith
    have hXσΘ : (X : ℝ) ^ ρ.re ≤ (X : ℝ) ^ Θ :=
      Real.rpow_le_rpow_of_exponent_le hX1' hρΘ
    have hmul : (X : ℝ) ^ ρ.re * (1 + 2 * Real.pi) ≤ (X : ℝ) ^ Θ * 8 :=
      mul_le_mul hXσΘ hconst (by positivity) (by positivity)
    have heq : (X : ℝ) ^ ρ.re / ‖ρ‖ +
        (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) =
        ((X : ℝ) ^ ρ.re * (1 + (X : ℝ) * (2 * Real.pi * |β|))) / ‖ρ‖ := by
      field_simp
    rw [heq, show 8 * (X : ℝ) ^ Θ / ‖ρ‖ = ((X : ℝ) ^ Θ * 8) / ‖ρ‖ by ring]
    refine (div_le_div_iff_of_pos_right hd).mpr ?_
    calc (X : ℝ) ^ ρ.re * (1 + (X : ℝ) * (2 * Real.pi * |β|)) ≤
        (X : ℝ) ^ ρ.re * (1 + 2 * Real.pi) := by
          have hp : (0 : ℝ) ≤ (X : ℝ) ^ ρ.re := Real.rpow_nonneg (Nat.cast_nonneg X) _
          nlinarith
      _ ≤ (X : ℝ) ^ Θ * 8 := hmul
  refine (norm_sub_le _ _).trans ?_
  calc ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β)‖ +
        ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖
      ≤ ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β)‖ +
        (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) := by
        have hB : ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
            (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) := by
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact add_le_add (le_refl _) hB
    _ = (X : ℝ) ^ ρ.re / ‖ρ‖ +
        (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) := by
        rw [norm_mul, norm_div, hnorm_pow X, norm_ee150, mul_one]
    _ ≤ 8 * (X : ℝ) ^ Θ / ‖ρ‖ := hkey

end LeanLab.BhowmikGrimmelt2026
