module

public import LeanLab.PNTPort.DirichletZF.Exceptional

/-!
# The exceptional zero is real, and so is its character

Lab proof, unit U-5110. AI wrote this file. Known mathematics, no cited input. The proof of
`LFunction_conj` follows Mathlib's `riemannZeta_conj`: termwise on `Re s > 1`, then the identity
theorem.

* `LFunction_conj`: `L(conj s, χ) = conj L(s, χ)` for `χ ≠ χ₀` with `χ² = χ₀`;
* `zero_free_region_real`: absolute `c, c' > 0` such that for every `N`, every zero of every
  non-principal `L(s, χ)` mod `N` has `β ≤ 1 - c / log B(γ)`, except possibly one zero of one
  character, and that zero is real, `γ = 0`, its character is real, `χ² = χ₀`, and it lies in the
  box `β ≥ 1 - c / log B(0)`, `|γ| ≤ c' / log B(0)`.
This is Montgomery-Vaughan Theorems 11.3 and 11.4, simplicity of the zero aside, with
`log B(t) = log(2NZ(|t| + 3))`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter
open scoped ComplexConjugate LSeries.notation

variable {N : ℕ} [NeZero N]

theorem LFunction_conj {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (h2 : χ ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.LFunction χ (conj s) = conj (DirichletCharacter.LFunction χ s) := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hg_an : AnalyticOnNhd ℂ (fun z ↦ conj (DirichletCharacter.LFunction χ (conj z))) univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ ↦ (differentiableAt_conj_conj_iff.mpr (hL (conj z))).differentiableWithinAt)
      isOpen_univ
  have hf_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) univ :=
    hL.differentiableOn.analyticOnNhd isOpen_univ
  have hgz (z : ℂ) (hz : 1 < z.re) :
      conj (DirichletCharacter.LFunction χ (conj z)) = DirichletCharacter.LFunction χ z := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ (by rwa [conj_re]),
      DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries, LSeries, conj_tsum]
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    congr 1
    have him := im_eq_zero_of_sq h2 n
    apply Complex.ext <;> simp [him]
  have heq : EqOn (fun z ↦ conj (DirichletCharacter.LFunction χ (conj z)))
      (DirichletCharacter.LFunction χ) univ := by
    refine hg_an.eqOn_of_preconnected_of_eventuallyEq hf_an isPreconnected_univ (mem_univ 2) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hgz z hz
  have := heq (mem_univ (conj s))
  simp only [conj_conj] at this
  exact this.symm

/-- The full region: one possible exceptional zero, real, of a real character. -/
theorem zero_free_region_real : ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) ∨
        (1 - c / Real.log (Bt N 0) ≤ ρ.re ∧ |ρ.im| ≤ c' / Real.log (Bt N 0) ∧
          χ ^ 2 = 1 ∧ ρ.im = 0)) ∧
      (∀ (χ₂ : DirichletCharacter ℂ N), χ₂ ≠ 1 → ∀ ρ₁ ρ₂ : ℂ,
        DirichletCharacter.LFunction χ ρ₁ = 0 → DirichletCharacter.LFunction χ₂ ρ₂ = 0 →
        1 - c / Real.log (Bt N 0) ≤ ρ₁.re → |ρ₁.im| ≤ c' / Real.log (Bt N 0) →
        1 - c / Real.log (Bt N 0) ≤ ρ₂.re → |ρ₂.im| ≤ c' / Real.log (Bt N 0) →
          χ = χ₂ ∧ ρ₁ = ρ₂) := by
  obtain ⟨c, c', hc, hc', h⟩ := zero_free_region_all
  obtain ⟨c1, hc1, hcx⟩ := zero_free_complex
  set c'' := min c c1 with hc''
  have hc''pos : 0 < c'' := lt_min hc hc1
  refine ⟨c'', c', hc''pos, hc', fun N _ χ hχ ↦ ⟨fun ρ hρ ↦ ?_, ?_⟩⟩
  · have hL0 := one_le_log_Bt (N := N) 0
    have hLp0 : 0 < Real.log (Bt N 0) := by linarith
    have hLp : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
    have hmono : Real.log (Bt N 0) ≤ Real.log (Bt N ρ.im) := log_Bt_mono (by simp)
    have hdiv : ∀ c₁ : ℝ, c'' ≤ c₁ → c₁ / Real.log (Bt N ρ.im) ≥ c'' / Real.log (Bt N ρ.im) :=
      fun c₁ hle ↦ div_le_div_of_nonneg_right hle hLp.le
    have hdiv0 : c'' / Real.log (Bt N ρ.im) ≤ c'' / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_left hc''pos.le hLp0 hmono
    rcases (h N χ hχ).1 ρ hρ with hr | ⟨hb, hg⟩
    · left; have := hdiv c (min_le_left _ _); linarith
    · by_cases hsq : χ ^ 2 = 1
      · by_cases hb'' : 1 - c'' / Real.log (Bt N 0) ≤ ρ.re
        · right
          refine ⟨hb'', hg, hsq, ?_⟩
          have hz' : DirichletCharacter.LFunction χ (conj ρ) = 0 := by
            rw [LFunction_conj hχ hsq, hρ, map_zero]
          have := ((h N χ hχ).2 χ hχ ρ (conj ρ) hρ hz' hb hg (by rwa [conj_re])
            (by rwa [conj_im, abs_neg])).2
          have him := congrArg Complex.im this
          rw [conj_im] at him
          linarith
        · left; push Not at hb''; linarith
      · left
        have := hcx N χ hsq ρ hρ
        have := hdiv c1 (min_le_right _ _)
        linarith
  · intro χ₂ hχ₂ ρ₁ ρ₂ h1 h2 hb1 hg1 hb2 hg2
    have hL0 := one_le_log_Bt (N := N) 0
    have hLp0 : 0 < Real.log (Bt N 0) := by linarith
    have : c'' / Real.log (Bt N 0) ≤ c / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLp0.le
    exact (h N χ hχ).2 χ₂ hχ₂ ρ₁ ρ₂ h1 h2 (by linarith) hg1 (by linarith) hg2

end LeanLab.PNTPort.DirichletZF

