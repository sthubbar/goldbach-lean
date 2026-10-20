module

public import LeanLab.PNTPort.DirichletZF.LogDerivStrip
public import LeanLab.PNTPort.DirichletZF.Exceptional

/-!
# The strip bound for `L'/L(s, χ)` with the zero-free region plugged in

Lab proof, unit U-5201, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics, no
cited input: it combines `logDeriv_strip_le` with `zero_free_region_all` of Exceptional.lean.

`logDeriv_strip_uniform`: there are absolute `c, c', κ, K > 0` such that for every `N ≥ 1`, every
non-principal `χ` mod `N` and all real `t`, `σ` with `1 - κ / log B(t) ≤ σ ≤ 2`,
`‖L'/L(σ + it, χ)‖ ≤ K log² B(t)`, provided no zero of `L(s, χ)` in the exceptional box
`β ≥ 1 - c / log B(0)`, `|γ| ≤ c' / log B(0)` lies in the disc `‖ρ - (3/2 + it)‖ ≤ 3/4`.
That proviso holds for `|t| ≥ c' + 3/4`, `logDeriv_strip_large_t`, and for every `t` when `χ` has
no exceptional zero, `logDeriv_strip_of_noExceptional`. Uniform in `N`, which Siegel-Walfisz needs.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex

/-- `L(s, χ)` has no zero in the exceptional box of `zero_free_region_all`. -/
def NoExceptional {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (c c' : ℝ) : Prop :=
  ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
    ¬ (1 - c / Real.log (Bt N 0) ≤ ρ.re ∧ |ρ.im| ≤ c' / Real.log (Bt N 0))

theorem logDeriv_strip_uniform : ∃ c c' κ K : ℝ, 0 < c ∧ 0 < c' ∧ 0 < κ ∧ 0 < K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ t σ : ℝ,
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - ((3 : ℂ) / 2 + I * t)‖ ≤ 3 / 4 →
        ¬ (1 - c / Real.log (Bt N 0) ≤ ρ.re ∧ |ρ.im| ≤ c' / Real.log (Bt N 0))) →
      1 - κ / Real.log (Bt N t) ≤ σ → σ ≤ 2 →
      ‖deriv (DirichletCharacter.LFunction χ) (σ + I * t) /
          DirichletCharacter.LFunction χ (σ + I * t)‖ ≤ K * Real.log (Bt N t) ^ 2 := by
  obtain ⟨c, c', hc, hc', hzf⟩ := zero_free_region_all
  set c₀ := min c (5 / 12) with hc₀
  have hc₀pos : 0 < c₀ := lt_min hc (by norm_num)
  have hc₀le : c₀ ≤ 5 / 12 := min_le_right _ _
  have hl : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  refine ⟨c, c', 2 * c₀ / 5, K0 + 5 / (2 * c₀ * Real.log (10 / 9)), hc, hc', by positivity,
    by have := K0_pos; positivity, fun N _ χ hχ t σ hbox hσ1 hσ2 ↦ ?_⟩
  refine logDeriv_strip_le hχ hc₀pos hc₀le t σ (fun ρ hρ hρc ↦ ?_) hσ1 hσ2
  rcases (hzf N χ hχ).1 ρ hρ with h | h
  · have hL : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
    have : c₀ / Real.log (Bt N ρ.im) ≤ c / Real.log (Bt N ρ.im) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hL.le
    linarith
  · exact absurd h (hbox ρ hρ hρc)

/-- The proviso holds for `|t| ≥ c' + 3/4`. -/
theorem logDeriv_strip_large_t : ∃ c' κ K : ℝ, 0 < c' ∧ 0 < κ ∧ 0 < K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ t σ : ℝ,
      c' + 3 / 4 ≤ |t| → 1 - κ / Real.log (Bt N t) ≤ σ → σ ≤ 2 →
      ‖deriv (DirichletCharacter.LFunction χ) (σ + I * t) /
          DirichletCharacter.LFunction χ (σ + I * t)‖ ≤ K * Real.log (Bt N t) ^ 2 := by
  obtain ⟨c, c', κ, K, hc, hc', hκ, hK, h⟩ := logDeriv_strip_uniform
  refine ⟨c', κ, K, hc', hκ, hK, fun N _ χ hχ t σ ht hσ1 hσ2 ↦ ?_⟩
  refine h N χ hχ t σ (fun ρ _ hρc hbox ↦ ?_) hσ1 hσ2
  have him : |ρ.im - t| ≤ 3 / 4 := by
    have := Complex.abs_im_le_norm (ρ - ((3 : ℂ) / 2 + I * t))
    have e : (ρ - ((3 : ℂ) / 2 + I * t)).im = ρ.im - t := by simp
    rw [e] at this; linarith
  have hγ : c' ≤ |ρ.im| := by
    have := abs_sub_abs_le_abs_sub t ρ.im
    rw [abs_sub_comm] at this; linarith
  have hL1 : 1 < Real.log (Bt N 0) := by
    rw [Real.lt_log_iff_exp_lt (lt_trans one_pos (one_lt_Bt 0))]
    unfold Bt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hZ := one_le_Z
    have he := Real.exp_one_lt_d9
    simp only [abs_zero, zero_add]
    nlinarith
  have : c' / Real.log (Bt N 0) < c' := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  linarith [hbox.2]

/-- For `χ` with no exceptional zero the bound holds for every `t`. -/
theorem logDeriv_strip_of_noExceptional : ∃ c c' κ K : ℝ, 0 < c ∧ 0 < c' ∧ 0 < κ ∧ 0 < K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → NoExceptional χ c c' →
      ∀ t σ : ℝ, 1 - κ / Real.log (Bt N t) ≤ σ → σ ≤ 2 →
      ‖deriv (DirichletCharacter.LFunction χ) (σ + I * t) /
          DirichletCharacter.LFunction χ (σ + I * t)‖ ≤ K * Real.log (Bt N t) ^ 2 := by
  obtain ⟨c, c', κ, K, hc, hc', hκ, hK, h⟩ := logDeriv_strip_uniform
  exact ⟨c, c', κ, K, hc, hc', hκ, hK, fun N _ χ hχ hno t σ hσ1 hσ2 ↦
    h N χ hχ t σ (fun ρ hρ _ ↦ hno ρ hρ) hσ1 hσ2⟩

/-- **Strip bound with the exceptional zero kept at a distance.** Absolute `c, c', κ, K > 0`: for
every `N`, every `χ ≠ χ₀` mod `N` and `1 - κ / log B(t) ≤ σ ≤ 2`, if every zero of the exceptional
box in the disc `‖ρ - (3/2 + it)‖ ≤ 3/4` is at distance at least `(κ/2) / log B(t)` from
`σ + it`, then `‖L'/L(σ + it, χ)‖ ≤ K log² B(t)`. A contour can always pick its vertical line
`σ` so that the one possible exceptional zero, real by `zero_free_region_real`, is that far. -/
theorem logDeriv_strip_exc : ∃ c c' κ K : ℝ, 0 < c ∧ 0 < c' ∧ 0 < κ ∧ 0 < K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ t σ : ℝ,
      1 - κ / Real.log (Bt N t) ≤ σ → σ ≤ 2 →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - ((3 : ℂ) / 2 + I * t)‖ ≤ 3 / 4 →
        (1 - c / Real.log (Bt N 0) ≤ ρ.re ∧ |ρ.im| ≤ c' / Real.log (Bt N 0)) →
        κ / 2 / Real.log (Bt N t) ≤ ‖(σ + I * t : ℂ) - ρ‖) →
      ‖deriv (DirichletCharacter.LFunction χ) (σ + I * t) /
          DirichletCharacter.LFunction χ (σ + I * t)‖ ≤ K * Real.log (Bt N t) ^ 2 := by
  obtain ⟨c, c', hc, hc', hzf⟩ := zero_free_region_all
  set c₀ := min c (5 / 12) with hc₀
  have hc₀pos : 0 < c₀ := lt_min hc (by norm_num)
  have hc₀le : c₀ ≤ 5 / 12 := min_le_right _ _
  have hl : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  set κ := 2 * c₀ / 5 with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨c, c', κ, K0 + 2 / (κ * Real.log (10 / 9)), hc, hc', hκpos,
    by have := K0_pos; positivity, fun N _ χ hχ t σ hσ1 hσ2 hexc ↦ ?_⟩
  set L := Real.log (Bt N t) with hLdef
  have hL : 1 ≤ L := one_le_log_Bt t
  have hLpos : 0 < L := by linarith
  set cc : ℂ := (3 : ℂ) / 2 + I * t with hcc
  set s : ℂ := σ + I * t with hsdef
  have hsc : s - cc = ((σ - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hsdef, hcc]
  have hσ56 : 5 / 6 ≤ σ := by
    have : κ / L ≤ 1 / 6 := by
      rw [div_le_iff₀ hLpos]; rw [hκ]; nlinarith
    linarith
  have hs : ‖s - cc‖ ≤ 2 / 3 := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  set η := κ / 2 / L with hη
  have hηpos : 0 < η := by positivity
  have hdist : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - cc‖ ≤ 3 / 4 →
      η ≤ ‖s - ρ‖ := by
    intro ρ hρ hρc
    rcases (hzf N χ hχ).1 ρ hρ with h | h
    · have him : |ρ.im - t| ≤ 3 / 4 := by
        have := Complex.abs_im_le_norm (ρ - cc)
        have e : (ρ - cc).im = ρ.im - t := by simp [hcc]
        rw [e] at this; linarith
      have hlog := log_Bt_shift_le (N := N) t ρ.im him
      have hLγ : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
      have h1 : 4 * c₀ / 5 / L ≤ c₀ / Real.log (Bt N ρ.im) := by
        rw [div_le_div_iff₀ hLpos hLγ]; nlinarith
      have h2 : c₀ / Real.log (Bt N ρ.im) ≤ c / Real.log (Bt N ρ.im) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hLγ.le
      have h3 : 4 * c₀ / 5 / L = 4 * η := by rw [hη, hκ]; ring
      have h4 : κ / L = 2 * η := by rw [hη]; ring
      have e : (s - ρ).re = σ - ρ.re := by simp [hsdef]
      have := Complex.re_le_norm (s - ρ)
      have hσ1' : 1 - 2 * η ≤ σ := by rw [← h4]; exact hσ1
      linarith
    · exact hexc ρ hρ hρc h
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    have := hdist s h0 (hs.trans (by norm_num))
    rw [sub_self, norm_zero] at this; linarith
  have key := logDeriv_le_of_dist hχ t hs hLs hηpos hdist
  have hK0 := K0_pos
  have e2 : L / Real.log (10 / 9) / η = 2 / (κ * Real.log (10 / 9)) * L ^ 2 := by
    rw [hη]; field_simp
  rw [e2] at key
  calc _ ≤ K0 * L + 2 / (κ * Real.log (10 / 9)) * L ^ 2 := key
    _ ≤ K0 * L ^ 2 + 2 / (κ * Real.log (10 / 9)) * L ^ 2 := by
        have : K0 * L ≤ K0 * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hK0.le
        linarith
    _ = _ := by ring

end LeanLab.PNTPort.DirichletZF

