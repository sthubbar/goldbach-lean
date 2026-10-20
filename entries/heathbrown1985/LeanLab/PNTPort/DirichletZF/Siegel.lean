module

public import LeanLab.PNTPort.DirichletZF.SiegelLift

/-!
# Siegel's theorem

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input, the
Estermann-Goldfeld proof, Davenport chapter 21. Ineffective, as every proof of it is.

`siegel`: for every `ε > 0` there is `c > 0` such that for every `N ≥ 1` and every real
non-principal Dirichlet character `χ` mod `N`, `‖L(1, χ)‖ ≥ c N^{-ε}`.

`siegel_core` does the work from a reference real character `ψ` mod `N₁` and a point `β` with
`Re F(β) ≤ 0` for `ψ` against every lifted `χ`; `siegel` supplies `ψ, β` in two cases: an
exceptional real zero near `1` exists for some character, or none does and then `ψ = χ₈` and
`F(β) ≤ 0` from the signs of `ζ` and `L` on `(0, 1)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter
open scoped ComplexOrder

lemma rpow_neg_mul {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ (-x) = a ^ (-x) * b ^ (-x) := Real.mul_rpow ha hb

/-- Siegel's bound from a reference character. -/
theorem siegel_core {N₁ : ℕ} [NeZero N₁] (ψ : DirichletCharacter ℂ N₁) (hψ : ψ ≠ 1)
    {β : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hF : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ (h₁ : N₁ ∣ (8 * N₁) * N) (h₂ : N ∣ (8 * N₁) * N),
        DirichletCharacter.changeLevel h₁ ψ * DirichletCharacter.changeLevel h₂ χ ≠ 1 →
        (Fq (DirichletCharacter.changeLevel h₁ ψ) (DirichletCharacter.changeLevel h₂ χ) β).re ≤ 0)
    (hψ2 : ψ ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) (hεβ : 12 * (1 - β) ≤ ε / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  obtain ⟨c₀, hc₀, hpair⟩ := siegel_pair_le
  set A : ℕ := 8 * N₁ with hA
  have hA8 : 8 ≤ A := by have := Nat.pos_of_ne_zero (NeZero.ne N₁); omega
  haveI : NeZero A := ⟨by omega⟩
  set D : ℝ := 2 ^ (A + 1) with hD
  have hDpos : 0 < D := by positivity
  have hLψ : 0 < ‖DirichletCharacter.LFunction ψ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)
  set κ := min (c₀ * (1 - β) * (ε ^ 2 / 16)) (‖DirichletCharacter.LFunction ψ 1‖ * (ε / 6))
    with hκ
  have h1β : 0 < 1 - β := by linarith
  have hκpos : 0 < κ := lt_min (by positivity) (by positivity)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  refine ⟨κ * (A : ℝ) ^ (-ε) / D, by positivity, fun N _ χ hχ hχ2 ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set M : ℕ := A * N with hM
  haveI : NeZero M := ⟨Nat.mul_ne_zero (NeZero.ne A) (NeZero.ne N)⟩
  have hM8 : 8 ≤ M := le_trans hA8 (Nat.le_mul_of_pos_right A (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hMr : (M : ℝ) = A * N := by rw [hM]; push_cast; ring
  have hM0 : (0 : ℝ) < M := by rw [hMr]; positivity
  have hM1 : (1 : ℝ) ≤ M := by
    have : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    linarith
  have h₁ : N₁ ∣ A * N := Dvd.dvd.mul_right (Dvd.intro_left 8 rfl) N
  have h₂ : N ∣ A * N := Dvd.intro_left A rfl
  set ψ' := DirichletCharacter.changeLevel h₁ ψ
  set χ' := DirichletCharacter.changeLevel h₂ χ
  -- `‖L(1, χ)‖ ≥ ‖L(1, χ')‖ / D`
  have hχlift : ‖DirichletCharacter.LFunction χ' 1‖ ≤ ‖DirichletCharacter.LFunction χ 1‖ * D := by
    rw [L_lift h₂ hχ, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_Efac_one_le χ) (norm_nonneg _)
  have hMpow : (M : ℝ) ^ (-ε) = (A : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε) := by
    rw [hMr, rpow_neg_mul hApos.le hN0.le]
  have hlogM : 0 < Real.log M := Real.log_pos (by
    have : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    linarith)
  -- it suffices to show `κ M^{-ε} ≤ ‖L(1, χ')‖`
  suffices hmain : κ * (M : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ' 1‖ by
    rw [hMpow] at hmain
    have := hmain.trans hχlift
    rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
    linarith
  by_cases h12 : ψ' * χ' ≠ 1
  · -- the pair bound at `M`
    have hb := hpair M hM8 ψ' χ' (lift_ne_one h₁ hψ) (lift_ne_one h₂ hχ) h12 (lift_sq h₁ hψ2)
      (lift_sq h₂ hχ2) β hβ hβ1 (hF N χ hχ hχ2 h₁ h₂ h12)
    -- `M^{-12(1-β)} ≥ M^{-ε/2}` and `log² M ≤ (16/ε²) M^{ε/2}`
    have hp1 : (M : ℝ) ^ (-(ε / 2)) ≤ (M : ℝ) ^ (-(12 * (1 - β))) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    have hlog : Real.log M ≤ (M : ℝ) ^ (ε / 4) / (ε / 4) :=
      Real.log_le_rpow_div hM0.le (by positivity)
    have hlog2 : Real.log M ^ 2 ≤ (16 / ε ^ 2) * (M : ℝ) ^ (ε / 2) := by
      have h0 : 0 ≤ Real.log M := hlogM.le
      calc Real.log M ^ 2 ≤ ((M : ℝ) ^ (ε / 4) / (ε / 4)) ^ 2 := pow_le_pow_left₀ h0 hlog 2
        _ = (16 / ε ^ 2) * (M : ℝ) ^ (ε / 2) := by
            rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
            field_simp
            ring_nf
    have hhalf : (M : ℝ) ^ (-ε) * (M : ℝ) ^ (ε / 2) = (M : ℝ) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hM0]; congr 1; ring
    have hMeps : 0 < (M : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hM0 _
    have key : (ε ^ 2 / 16) * (M : ℝ) ^ (-ε) * Real.log M ^ 2 ≤ (M : ℝ) ^ (-(12 * (1 - β))) := by
      calc (ε ^ 2 / 16) * (M : ℝ) ^ (-ε) * Real.log M ^ 2
          ≤ (ε ^ 2 / 16) * (M : ℝ) ^ (-ε) * ((16 / ε ^ 2) * (M : ℝ) ^ (ε / 2)) := by gcongr
        _ = (M : ℝ) ^ (-ε) * (M : ℝ) ^ (ε / 2) := by field_simp
        _ = (M : ℝ) ^ (-(ε / 2)) := hhalf
        _ ≤ _ := hp1
    have hl2 : 0 < Real.log M ^ 2 := by positivity
    calc κ * (M : ℝ) ^ (-ε) ≤ c₀ * (1 - β) * (ε ^ 2 / 16) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hMeps.le
      _ = c₀ * (1 - β) * ((ε ^ 2 / 16) * (M : ℝ) ^ (-ε) * Real.log M ^ 2) / Real.log M ^ 2 := by
          field_simp
      _ ≤ c₀ * (1 - β) * (M : ℝ) ^ (-(12 * (1 - β))) / Real.log M ^ 2 := by gcongr
      _ ≤ _ := hb
  · push Not at h12
    have hψ'2 := lift_sq h₁ hψ2
    have hinv : ψ'⁻¹ = ψ' := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hψ'2)
    have hχψ : χ' = ψ' := by rw [eq_inv_of_mul_eq_one_right h12, hinv]
    rw [hχψ, L_lift h₁ hψ, norm_mul]
    have hE := norm_Efac_one_ge ψ M
    have hω := card_primeFactors_le_log M
    have hlog2 := Real.log_two_gt_d9
    have hlog8 : 2 ≤ Real.log M := one_le_log_half hM8
    have hω3 : (M.primeFactors.card : ℝ) + 1 ≤ 3 * Real.log M := by
      have : (M.primeFactors.card : ℝ) ≤ Real.log M / Real.log 2 := by
        rw [le_div_iff₀ (by linarith)]; exact hω
      have : Real.log M / Real.log 2 ≤ 2 * Real.log M := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have hlog : Real.log M ≤ (M : ℝ) ^ (ε / 2) / (ε / 2) :=
      Real.log_le_rpow_div hM0.le (by positivity)
    have hω6 : (M.primeFactors.card : ℝ) + 1 ≤ (6 / ε) * (M : ℝ) ^ (ε / 2) := by
      have : 3 * Real.log M ≤ 3 * ((M : ℝ) ^ (ε / 2) / (ε / 2)) := by linarith
      calc _ ≤ 3 * Real.log M := hω3
        _ ≤ 3 * ((M : ℝ) ^ (ε / 2) / (ε / 2)) := this
        _ = (6 / ε) * (M : ℝ) ^ (ε / 2) := by field_simp; ring
    have hMh : 0 < (M : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hM0 _
    have hpe : (M : ℝ) ^ (-ε) ≤ (M : ℝ) ^ (-(ε / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    have hMm : (M : ℝ) ^ (-(ε / 2)) = 1 / (M : ℝ) ^ (ε / 2) := by
      rw [Real.rpow_neg hM0.le, one_div]
    have hEge : (ε / 6) * (M : ℝ) ^ (-(ε / 2)) ≤ ‖Efac ψ M 1‖ := by
      refine le_trans ?_ hE
      rw [hMm, le_div_iff₀ (by positivity)]
      calc ε / 6 * (1 / (M : ℝ) ^ (ε / 2)) * ((M.primeFactors.card : ℝ) + 1)
          ≤ ε / 6 * (1 / (M : ℝ) ^ (ε / 2)) * ((6 / ε) * (M : ℝ) ^ (ε / 2)) := by gcongr
        _ = 1 := by field_simp
    calc κ * (M : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction ψ 1‖ * (ε / 6) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hM0.le _)
      _ ≤ ‖DirichletCharacter.LFunction ψ 1‖ * (ε / 6) * (M : ℝ) ^ (-(ε / 2)) := by gcongr
      _ = ‖DirichletCharacter.LFunction ψ 1‖ * ((ε / 6) * (M : ℝ) ^ (-(ε / 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEge (norm_nonneg _)

/-- `Re F(β) ≤ 0` when `ζ(β) < 0` and the three L-values are nonnegative reals. -/
lemma Fq_re_nonpos {N : ℕ} [NeZero N] {χ₁ χ₂ : DirichletCharacter ℂ N} {β : ℝ} (h0 : 0 < β)
    (h1 : β < 1) (a : 0 ≤ DirichletCharacter.LFunction χ₁ β)
    (b : 0 ≤ DirichletCharacter.LFunction χ₂ β)
    (c : 0 ≤ DirichletCharacter.LFunction (χ₁ * χ₂) β) : (Fq χ₁ χ₂ β).re ≤ 0 := by
  obtain ⟨hzi, hzr⟩ := riemannZeta_real_neg h0 h1
  have hP : 0 ≤ DirichletCharacter.LFunction χ₁ β * DirichletCharacter.LFunction χ₂ β *
      DirichletCharacter.LFunction (χ₁ * χ₂) β := mul_nonneg (mul_nonneg a b) c
  obtain ⟨hPr, hPi⟩ := Complex.nonneg_iff.mp hP
  have e : Fq χ₁ χ₂ β = riemannZeta β * (DirichletCharacter.LFunction χ₁ β *
      DirichletCharacter.LFunction χ₂ β * DirichletCharacter.LFunction (χ₁ * χ₂) β) := by
    simp only [Fq]; ring
  rw [e, Complex.mul_re, hzi, ← hPi]
  nlinarith

/-- **Siegel's theorem.** -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  intro ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set δ := ε' / 24 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ8 : δ ≤ 1 / 8 := by rw [hδ]; linarith
  have hεβ : 12 * (1 - (1 - δ)) ≤ ε' / 2 := by rw [hδ]; linarith
  -- reduce to `ε'`
  suffices h : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ ^ 2 = 1 → c * (N : ℝ) ^ (-ε') ≤ ‖DirichletCharacter.LFunction χ 1‖ by
    obtain ⟨c, hc, h⟩ := h
    refine ⟨c, hc, fun N _ χ hχ hχ2 ↦ le_trans ?_ (h N χ hχ hχ2)⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left ε 1])) hc.le
  by_cases hA : ∃ (N₁ : ℕ) (_ : NeZero N₁) (ψ : DirichletCharacter ℂ N₁), ψ ≠ 1 ∧ ψ ^ 2 = 1 ∧
      ∃ β : ℝ, 1 - δ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction ψ β = 0
  · obtain ⟨N₁, _, ψ, hψ, hψ2, β, hβ, hβ1, hz⟩ := hA
    have hεβ' : 12 * (1 - β) ≤ ε' / 2 := by linarith
    refine siegel_core ψ hψ (by linarith) hβ1 ?_ hψ2 hε'0 hεβ'
    intro N _ χ hχ hχ2 h₁ h₂ _
    haveI : NeZero ((8 * N₁) * N) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num)
      (NeZero.ne N₁)) (NeZero.ne N)⟩
    have : DirichletCharacter.LFunction (DirichletCharacter.changeLevel h₁ ψ) β = 0 := by
      rw [L_lift h₁ hψ, hz, zero_mul]
    simp [Fq, this]
  · push Not at hA
    refine siegel_core chi8 chi8_ne_one (β := 1 - δ) (by linarith) (by linarith) ?_ chi8_sq
      hε'0 hεβ
    intro N _ χ hχ hχ2 h₁ h₂ h12
    haveI : NeZero ((8 * 8) * N) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne N)⟩
    have hnz : ∀ φ : DirichletCharacter ℂ ((8 * 8) * N), φ ≠ 1 → φ ^ 2 = 1 →
        0 ≤ DirichletCharacter.LFunction φ ((1 - δ : ℝ)) := by
      intro φ hφ hφ2
      exact LFunction_nonneg_of_no_zero hφ hφ2 (by linarith) fun σ hσ hσ1 ↦
        hA ((8 * 8) * N) inferInstance φ hφ hφ2 σ hσ hσ1
    have s1 := lift_sq h₁ chi8_sq
    have s2 := lift_sq h₂ hχ2
    refine Fq_re_nonpos (by linarith) (by linarith) (hnz _ (lift_ne_one h₁ chi8_ne_one) s1)
      (hnz _ (lift_ne_one h₂ hχ) s2) (hnz _ h12 (by rw [mul_pow, s1, s2, one_mul]))

/-- **Siegel's theorem, zero form.** For every `ε > 0` there is `c > 0` such that every real
zero `β` of `L(s, χ)`, `χ` real non-principal mod `N ≥ 8`, satisfies `β ≤ 1 - c N^{-ε}`. -/
theorem siegel_zero : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N], 8 ≤ N →
    ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 → ∀ β : ℝ, β ≤ 1 →
      DirichletCharacter.LFunction χ β = 0 → β ≤ 1 - c * (N : ℝ) ^ (-ε) := by
  intro ε hε
  obtain ⟨c₁, hc₁, hs⟩ := siegel (ε / 2) (by positivity)
  set E := Real.exp 1 * Real.exp 1
  have hE : 0 < E := by positivity
  refine ⟨min (c₁ * (ε / 4) ^ 2 / (5 * E)) ε, lt_min (by positivity) hε,
    fun N _ hN χ hχ hχ2 β hβ1 hz ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl2 : 2 ≤ Real.log N := one_le_log_half hN
  have hNe : 0 < (N : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hN0 _
  have hNe1 : (N : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  by_cases hfar : β < 1 - 1 / Real.log N
  · -- far from `1`: `1/log N ≥ N^{-ε} · (ε/?)`, use `c ≤ ...`; simplest: `1/log N ≥ c N^{-ε}`
    have hlog : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hN0.le hε
    have hlp : 0 < Real.log N := by linarith
    have hNε : (N : ℝ) ^ (-ε) * (N : ℝ) ^ ε = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have h1 : min (c₁ * (ε / 4) ^ 2 / (5 * E)) ε * (N : ℝ) ^ (-ε) ≤ 1 / Real.log N := by
      rw [le_div_iff₀ hlp]
      calc min (c₁ * (ε / 4) ^ 2 / (5 * E)) ε * (N : ℝ) ^ (-ε) * Real.log N
          ≤ ε * (N : ℝ) ^ (-ε) * ((N : ℝ) ^ ε / ε) := by
            gcongr
            exact min_le_right _ _
        _ = 1 := by field_simp; linarith [hNε]
    linarith
  · push Not at hfar
    have hb := norm_LFunction_one_le_of_zero hχ hN hfar hβ1 hz
    have hL := hs N χ hχ hχ2
    have hlog : Real.log N ≤ (N : ℝ) ^ (ε / 4) / (ε / 4) :=
      Real.log_le_rpow_div hN0.le (by positivity)
    have hlp : 0 ≤ Real.log N := by linarith
    have hlog2 : Real.log N ^ 2 ≤ (N : ℝ) ^ (ε / 2) / (ε / 4) ^ 2 := by
      calc Real.log N ^ 2 ≤ ((N : ℝ) ^ (ε / 4) / (ε / 4)) ^ 2 := pow_le_pow_left₀ hlp hlog 2
        _ = (N : ℝ) ^ (ε / 2) / (ε / 4) ^ 2 := by
            rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 2; push_cast; ring
    have hNh : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hN0 _
    have hsplit : (N : ℝ) ^ (-(ε / 2)) = (N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h1β : 0 ≤ 1 - β := by linarith
    -- `c₁ N^{-ε/2} ≤ 5E log² N (1 - β) ≤ 5E N^{ε/2} (1 - β)/(ε/4)²`
    have key : c₁ * (N : ℝ) ^ (-(ε / 2)) ≤ 5 * E * ((N : ℝ) ^ (ε / 2) / (ε / 4) ^ 2) * (1 - β) := by
      calc c₁ * (N : ℝ) ^ (-(ε / 2)) ≤ ‖DirichletCharacter.LFunction χ 1‖ := hL
        _ ≤ 5 * E * Real.log N ^ 2 * (1 - β) := hb
        _ ≤ _ := by gcongr
    rw [hsplit] at key
    have : c₁ * (ε / 4) ^ 2 / (5 * E) * (N : ℝ) ^ (-ε) ≤ 1 - β := by
      have hε4 : 0 < (ε / 4) ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have e : c₁ * ((N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 2)) * (ε / 4) ^ 2 ≤
          5 * E * (N : ℝ) ^ (ε / 2) * (1 - β) := by
        have := mul_le_mul_of_nonneg_right key hε4.le
        calc _ ≤ 5 * E * ((N : ℝ) ^ (ε / 2) / (ε / 4) ^ 2) * (1 - β) * (ε / 4) ^ 2 := this
          _ = _ := by field_simp
      nlinarith
    have hm : min (c₁ * (ε / 4) ^ 2 / (5 * E)) ε * (N : ℝ) ^ (-ε) ≤
        c₁ * (ε / 4) ^ 2 / (5 * E) * (N : ℝ) ^ (-ε) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hNe.le
    linarith

end LeanLab.PNTPort.DirichletZF

