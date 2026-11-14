module

public import LeanLab.PNTPort.DirichletZF.Estermann
public import LeanLab.PNTPort.DirichletZF.NearOne

/-!
# Siegel's theorem for a pair of characters of one modulus

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input, the core of the
Estermann-Goldfeld proof of Siegel's theorem, Davenport chapter 21.

`siegel_pair`: there is an absolute `c > 0` such that for every `N ≥ 8`, real non-principal
`χ₁, χ₂` mod `N` with `χ₁χ₂ ≠ χ₀`, and a real zero `β` of `L(s, χ₁)` with `7/8 ≤ β < 1`,

  `‖L(1, χ₂)‖ ≥ c (1 - β) N^{-12(1-β)} / log² N`.

This is a uniform bound, not yet Siegel's theorem: `χ₁` must have the same modulus `N` as `χ₂`,
so holding `β` fixed while `N` grows needs the move to a common modulus, not done here, and the
case with no exceptional zero is separate. `χ₁χ₂ ≠ χ₀` with `χ₁² = χ₀` excludes `χ₂ = χ₁`.
`siegel_pair_le` assumes only `Re F(β) ≤ 0`, which also covers that case.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Real

lemma log_four_thirds_ge : 1 / 4 ≤ Real.log (4 / 3) := by
  have h := Real.add_one_le_exp (-(1 / 4) : ℝ)
  have h2 : Real.exp (-(1 / 4) : ℝ) * Real.exp (1 / 4) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he : 0 < Real.exp (-(1 / 4) : ℝ) := Real.exp_pos _
  nlinarith [Real.exp_pos (1 / 4 : ℝ)]

/-- The same with `Re F(β) ≤ 0` in place of a zero of `L(s, χ₁)`. -/
theorem siegel_pair_le : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N], 8 ≤ N →
    ∀ (χ₁ χ₂ : DirichletCharacter ℂ N), χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ * χ₂ ≠ 1 → χ₁ ^ 2 = 1 →
      χ₂ ^ 2 = 1 → ∀ β : ℝ, 7 / 8 ≤ β → β < 1 → (Fq χ₁ χ₂ β).re ≤ 0 →
        c * (1 - β) * (N : ℝ) ^ (-(12 * (1 - β))) / Real.log N ^ 2 ≤
          ‖DirichletCharacter.LFunction χ₂ 1‖ := by
  obtain ⟨C₀, hC₀, hest⟩ := estermann
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  set E := Real.exp 1 * Real.exp 1 with hE
  have hEpos : 0 < E := by positivity
  refine ⟨1 / (8 * Real.exp 1 * (32 * C) * E ^ 2), by positivity,
    fun N _ hN χ₁ χ₂ h1 h2 h12 r1 r2 β hβ hβ1 hz ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 2 ≤ Real.log N := one_le_log_half hN
  set A := 32 * C * (N : ℝ) ^ 3 with hA
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith [(show (8 : ℝ) ≤ N by exact_mod_cast hN)])
    rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  set K : ℕ := ⌈Real.log A / Real.log (4 / 3)⌉₊ with hK
  have hl43 := log_four_thirds_ge
  have hl43p : 0 < Real.log (4 / 3) := by linarith
  have hK1 : 1 ≤ K := by
    have h32 : (32 : ℝ) ≤ A := by
      have : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by
        linarith [(show (8 : ℝ) ≤ N by exact_mod_cast hN)])
      rw [hA]; nlinarith
    have hpos : 0 < Real.log A / Real.log (4 / 3) := div_pos (Real.log_pos (by linarith)) hl43p
    have : (0 : ℝ) < K := lt_of_lt_of_le hpos (Nat.le_ceil _)
    exact_mod_cast this
  have hKge : Real.log A / Real.log (4 / 3) ≤ K := Nat.le_ceil _
  have hKle : (K : ℝ) ≤ Real.log A / Real.log (4 / 3) + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Real.log A / Real.log (4 / 3) by
      exact div_nonneg (Real.log_nonneg hA1) hl43p.le)
    rw [← hK] at this; linarith
  -- `(3/4)^K ≤ 1/A`
  have h34 : (3 / 4 : ℝ) ^ K ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    have : Real.log A ≤ K * Real.log (4 / 3) := by
      rwa [div_le_iff₀ hl43p] at hKge
    have e1 : (3 / 4 : ℝ) ^ K = Real.exp (-(K * Real.log (4 / 3))) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, inv_pow, ← Real.exp_log
        (show (0 : ℝ) < (4 / 3) ^ K by positivity), Real.log_pow, Real.exp_neg]
    rw [e1]
    calc Real.exp (-(K * Real.log (4 / 3))) * A
        = Real.exp (-(K * Real.log (4 / 3))) * Real.exp (Real.log A) := by
          rw [Real.exp_log hApos]
      _ = Real.exp (Real.log A - K * Real.log (4 / 3)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  -- `(2 - β)^K ≤ e (32C) N^{12(1-β)}`
  set u := 1 - β with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  have hu8 : u ≤ 1 / 8 := by rw [hu]; linarith
  have hxK : (2 - β) ^ K ≤ Real.exp 1 * (32 * C) * (N : ℝ) ^ (12 * u) := by
    have hx : (2 - β) = 1 + u := by rw [hu]; ring
    rw [hx]
    have h1 : (1 + u) ^ K ≤ Real.exp (u * K) := by
      rw [← Real.exp_log (show (0 : ℝ) < (1 + u) ^ K by positivity), Real.log_pow]
      apply Real.exp_le_exp.mpr
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    have h2 : u * K ≤ u + 4 * u * Real.log A := by
      have : (K : ℝ) ≤ 4 * Real.log A + 1 := by
        have : Real.log A / Real.log (4 / 3) ≤ 4 * Real.log A := by
          rw [div_le_iff₀ hl43p]
          nlinarith [Real.log_nonneg hA1]
        linarith
      nlinarith
    have h3 : Real.exp (u + 4 * u * Real.log A) ≤ Real.exp 1 * (32 * C) * (N : ℝ) ^ (12 * u) := by
      rw [Real.exp_add]
      have hlogA : Real.log A = Real.log (32 * C) + 3 * Real.log N := by
        rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      have e2 : Real.exp (4 * u * Real.log A) =
          Real.exp (4 * u * Real.log (32 * C)) * (N : ℝ) ^ (12 * u) := by
        rw [hlogA, Real.rpow_def_of_pos hN0, ← Real.exp_add]; ring_nf
      rw [e2]
      have hC32 : 0 ≤ Real.log (32 * C) := Real.log_nonneg (by linarith)
      have e3 : Real.exp (4 * u * Real.log (32 * C)) ≤ 32 * C := by
        calc Real.exp (4 * u * Real.log (32 * C)) ≤ Real.exp (Real.log (32 * C)) :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ = 32 * C := Real.exp_log (by positivity)
      have e4 : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      have hNu : 0 < (N : ℝ) ^ (12 * u) := Real.rpow_pos_of_pos hN0 _
      calc Real.exp u * (Real.exp (4 * u * Real.log (32 * C)) * (N : ℝ) ^ (12 * u))
          ≤ Real.exp 1 * ((32 * C) * (N : ℝ) ^ (12 * u)) := by
            gcongr
      _ = _ := by ring
    exact h1.trans ((Real.exp_le_exp.mpr h2).trans h3)
  -- Estermann at `σ = β`
  have hest' := hest N χ₁ χ₂ h1 h2 h12 r1 r2 β hβ hβ1 K hK1
  have hest' := hest'.trans hz
  set lam := ‖Pq χ₁ χ₂ 1‖ with hlam
  have hB : 4 * (C₀ * (N : ℝ) ^ 3) * (3 / 4) ^ K ≤ 1 / 8 := by
    have : C₀ ≤ C := le_max_left _ _
    have h3 : 0 ≤ (3 / 4 : ℝ) ^ K := by positivity
    calc 4 * (C₀ * (N : ℝ) ^ 3) * (3 / 4) ^ K ≤ 4 * (C * (N : ℝ) ^ 3) * (1 / A) := by
          gcongr
      _ = 1 / 8 := by rw [hA]; field_simp; ring
  have hlam_ge : u / (8 * (2 - β) ^ K) ≤ lam := by
    have hxpos : 0 < (2 - β) ^ K := pow_pos (by linarith) K
    rw [div_le_iff₀ (mul_pos (by norm_num) hxpos)]
    have : 1 / 8 ≤ lam * (2 - β) ^ K / u := by
      have h4 : 1 / 4 - lam * (2 - β) ^ K / (1 - β) ≤ 1 / 8 := by linarith
      rw [← hu] at h4
      linarith
    rw [le_div_iff₀ hu0] at this
    linarith
  -- upper bounds for the other two factors
  have hL1 : ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ E * Real.log N := by
    have := norm_LFunction_le_log h1 hN (s := 1) (by simp; positivity) (by simp)
    simpa using this
  have hL12 : ‖DirichletCharacter.LFunction (χ₁ * χ₂) 1‖ ≤ E * Real.log N := by
    have := norm_LFunction_le_log h12 hN (s := 1) (by simp; positivity) (by simp)
    simpa using this
  have hlam_le : lam ≤ (E * Real.log N) ^ 2 * ‖DirichletCharacter.LFunction χ₂ 1‖ := by
    rw [hlam]
    simp only [Pq, norm_mul]
    calc ‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ₂ 1‖ *
          ‖DirichletCharacter.LFunction (χ₁ * χ₂) 1‖
        ≤ (E * Real.log N) * ‖DirichletCharacter.LFunction χ₂ 1‖ * (E * Real.log N) := by
          gcongr
      _ = _ := by ring
  -- assemble
  have hNu : 0 < (N : ℝ) ^ (12 * u) := Real.rpow_pos_of_pos hN0 _
  have hneg : (N : ℝ) ^ (-(12 * u)) = 1 / (N : ℝ) ^ (12 * u) := by
    rw [Real.rpow_neg hN0.le, one_div]
  rw [hneg]
  have hlog2 : 0 < Real.log N ^ 2 := by positivity
  have hD : 0 < 8 * Real.exp 1 * (32 * C) * E ^ 2 := by positivity
  have key : u / (8 * (Real.exp 1 * (32 * C) * (N : ℝ) ^ (12 * u))) ≤
      (E * Real.log N) ^ 2 * ‖DirichletCharacter.LFunction χ₂ 1‖ := by
    refine le_trans ?_ (hlam_ge.trans hlam_le)
    apply div_le_div_of_nonneg_left hu0.le (mul_pos (by norm_num) (pow_pos (by linarith) K))
    linarith
  rw [div_le_iff₀ (by positivity)] at key
  rw [div_le_iff₀ hlog2]
  have e : 1 / (8 * Real.exp 1 * (32 * C) * E ^ 2) * u * (1 / (N : ℝ) ^ (12 * u)) =
      u / (8 * (Real.exp 1 * (32 * C) * (N : ℝ) ^ (12 * u))) / E ^ 2 := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  calc u / (8 * (Real.exp 1 * (32 * C) * (N : ℝ) ^ (12 * u)))
      ≤ (E * Real.log N) ^ 2 * ‖DirichletCharacter.LFunction χ₂ 1‖ := by
        rw [div_le_iff₀ (by positivity)]; exact key
    _ = ‖DirichletCharacter.LFunction χ₂ 1‖ * Real.log N ^ 2 * E ^ 2 := by ring

theorem siegel_pair : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N], 8 ≤ N →
    ∀ (χ₁ χ₂ : DirichletCharacter ℂ N), χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ * χ₂ ≠ 1 → χ₁ ^ 2 = 1 →
      χ₂ ^ 2 = 1 → ∀ β : ℝ, 7 / 8 ≤ β → β < 1 → DirichletCharacter.LFunction χ₁ β = 0 →
        c * (1 - β) * (N : ℝ) ^ (-(12 * (1 - β))) / Real.log N ^ 2 ≤
          ‖DirichletCharacter.LFunction χ₂ 1‖ := by
  obtain ⟨c, hc, h⟩ := siegel_pair_le
  refine ⟨c, hc, fun N _ hN χ₁ χ₂ h1 h2 h12 r1 r2 β hβ hβ1 hz ↦
    h N hN χ₁ χ₂ h1 h2 h12 r1 r2 β hβ hβ1 ?_⟩
  simp [Fq, hz]

end LeanLab.PNTPort.DirichletZF

