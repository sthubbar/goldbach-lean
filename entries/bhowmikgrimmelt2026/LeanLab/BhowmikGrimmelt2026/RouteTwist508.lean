module

public import LeanLab.BhowmikGrimmelt2026.RouteAbel508
public import LeanLab.BhowmikGrimmelt2026.RoutePhase508

/-!
ROUTE for `oscillatory_zero_modes508`, part three: the twisted power sum of one zero mode.
Source: P0029 page 15 display 4.6 in discrete form. The sum is cut at the end of the
stationary range; below it the dyadic blocks are bounded by the second derivative test and
summed by halving, above it the Kusmin Landau test applies.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- A dyadic block of the phase sum is at most `50 * R` once `sqrt |γ| ≤ R` and
`N ≤ R * sqrt |γ|`. -/
theorem block_fifty_aux508 {γ β R : ℝ} (hγ : γ ≠ 0) {N p q : ℕ} (hN : 1 ≤ N)
    (hp : N ≤ p) (hpq : p ≤ q) (hq : q + 1 ≤ 2 * N) (hs : Real.sqrt |γ| ≤ R)
    (hNR : (N : ℝ) ≤ R * Real.sqrt |γ|) :
    ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤ 50 * R := by
  have h := log_phase_block_vdc508 (β := β) hγ hN hp hpq hq
  have hs0 : 0 < Real.sqrt |γ| := Real.sqrt_pos.mpr (abs_pos.mpr hγ)
  have h1 : (N : ℝ) / Real.sqrt |γ| ≤ R := (div_le_iff₀ hs0).mpr hNR
  have h2 : 41 * (N : ℝ) / Real.sqrt |γ| = 41 * ((N : ℝ) / Real.sqrt |γ|) := by ring
  rw [h2] at h
  linarith

/-- The sum of `n ^ ρ * e(n β)` over `n < X` in modulus and phase form over `1 ≤ n < X`. -/
theorem twist_sum_phase_form_aux508 (X : ℕ) (hX : 1 ≤ X) {ρ : ℂ} (hρ0 : 0 < ρ.re) (β : ℝ) :
    ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β) =
      ∑ n ∈ Finset.Ico 1 X, (((n : ℝ) ^ ρ.re : ℝ) : ℂ) *
        ee (ρ.im / (2 * Real.pi) * Real.log n + (n : ℝ) * β) := by
  have hρ : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < X)]
  simp only [Nat.cast_zero, Complex.zero_cpow hρ, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact cpow_twist_phase508 (Finset.mem_Ico.mp hn).1 ρ β

/-- P0029 page 15 display 4.6, the sum inside the Abel form of one zero mode. For
`0 < Re ρ ≤ Θ`, `|Im ρ| ≤ 2X`, and a frequency with `1 / X ≤ |β| ≤ 1 / 2`, the sum of
`n ^ ρ * e(n β)` over `n < X` is at most `500 * X ^ Θ * sqrt (X / |β|)`. The height
restriction is needed: without it the estimate fails, see the route notes. -/
theorem log_power_twist_sum508 {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρΘ : ρ.re ≤ Θ) (hρT : |ρ.im| ≤ 2 * (X : ℝ)) {β : ℝ}
    (hβ1 : 1 ≤ |β| * (X : ℝ)) (hβ2 : |β| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ ≤
      500 * (X : ℝ) ^ Θ * Real.sqrt ((X : ℝ) / |β|) := by
  rw [twist_sum_phase_form_aux508 X hX hρ0 β]
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ρ.re := ⟨_, rfl⟩
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = ρ.im := ⟨_, rfl⟩
  rw [← hσ] at hρ0 hρΘ
  rw [← hγd] at hρT
  rw [← hσ, ← hγd]
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = |β| := ⟨_, rfl⟩
  rw [← hbd] at hβ1 hβ2
  rw [← hbd]
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hb0 : 0 ≤ b := by rw [hbd]; exact abs_nonneg β
  have hb : 0 < b := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hβ1; linarith
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, abs_zero] at hbd; linarith
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = Real.sqrt ((X : ℝ) / b) := ⟨_, rfl⟩
  rw [← hRd]
  have hXb0 : 0 ≤ (X : ℝ) / b := by positivity
  have hR0 : 0 ≤ R := by rw [hRd]; exact Real.sqrt_nonneg _
  have hRsq : R ^ 2 = (X : ℝ) / b := by rw [hRd]; exact Real.sq_sqrt hXb0
  have h2X : 2 * (X : ℝ) ≤ (X : ℝ) / b := by
    rw [le_div_iff₀ hb]; nlinarith
  have hsγ : Real.sqrt |γ| ≤ R := by
    rw [hRd]; exact Real.sqrt_le_sqrt (hρT.trans h2X)
  have hinvb : 1 / b ≤ R := by
    rw [hRd]
    apply Real.le_sqrt_of_sq_le
    have h1 : 1 / b ≤ (X : ℝ) := by rw [div_le_iff₀ hb]; linarith
    have h2 : (1 / b) ^ 2 = 1 / b * (1 / b) := by ring
    have h3 : (X : ℝ) / b = (X : ℝ) * (1 / b) := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  obtain ⟨τ, hτd⟩ : ∃ τ : ℝ, τ = max σ (1 / 2) := ⟨_, rfl⟩
  have hστ : σ ≤ τ := by rw [hτd]; exact le_max_left _ _
  have hτ : 1 / 2 ≤ τ := by rw [hτd]; exact le_max_right _ _
  have hτΘ : τ ≤ Θ := by rw [hτd]; exact max_le hρΘ hΘ
  have hXΘ0 : 0 ≤ (X : ℝ) ^ Θ := Real.rpow_nonneg (by linarith) Θ
  have hXτ : (X : ℝ) ^ τ ≤ (X : ℝ) ^ Θ := Real.rpow_le_rpow_of_exponent_le hXr hτΘ
  have hXR : 0 ≤ (X : ℝ) ^ Θ * R := mul_nonneg hXΘ0 hR0
  have h50 : (0 : ℝ) ≤ 50 * R := by linarith
  by_cases hcase : b * (X : ℝ) ≤ |γ|
  · -- Case A: the whole range is stationary.
    have hγ0 : γ ≠ 0 := by
      intro h; rw [h, abs_zero] at hcase; linarith
    have hXle : (X : ℝ) ≤ R * Real.sqrt |γ| := by
      rw [hRd, ← Real.sqrt_mul hXb0]
      apply Real.le_sqrt_of_sq_le
      have h1 : (X : ℝ) / b * (b * (X : ℝ)) = (X : ℝ) ^ 2 := by field_simp
      have h2 := mul_le_mul_of_nonneg_left hcase hXb0
      linarith
    have hV : ∀ N p q : ℕ, 1 ≤ N → N ≤ p → p ≤ q → q + 1 ≤ 2 * N → q < X →
        ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖
          ≤ 50 * R := by
      intro N p q hN hp hpq hq hqX
      have hNX : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : N ≤ X)
      exact block_fifty_aux508 hγ0 hN hp hpq hq hsγ (hNX.trans hXle)
    have h := halving_weighted_sum508
      (fun n : ℕ => ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β))
      hρ0.le hστ hτ h50 X hV X le_rfl
    refine h.trans ?_
    have h9 := mul_le_mul_of_nonneg_right hXτ hR0
    calc 8 * (X : ℝ) ^ τ * (50 * R) = 400 * ((X : ℝ) ^ τ * R) := by ring
      _ ≤ 500 * ((X : ℝ) ^ Θ * R) := by linarith only [h9, hXR]
      _ = 500 * (X : ℝ) ^ Θ * R := by ring
  · -- Case B: cut at the end of the stationary range.
    have hcase' : |γ| < b * (X : ℝ) := not_le.mp hcase
    have hπb : 0 < Real.pi * b := mul_pos Real.pi_pos hb
    obtain ⟨M, hMd⟩ : ∃ M : ℕ, M = Nat.ceil (|γ| / (Real.pi * b)) := ⟨_, rfl⟩
    have hMX : M ≤ X := by
      rw [hMd, Nat.ceil_le, div_le_iff₀ hπb]
      have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    have hMge : |γ| / (Real.pi * b) ≤ (M : ℝ) := by rw [hMd]; exact Nat.le_ceil _
    have hbR : (b * R) ^ 2 = b * (X : ℝ) := by
      rw [mul_pow, hRsq]; field_simp
    have hsγb : Real.sqrt |γ| ≤ b * R := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by rw [hbR]; exact hcase'.le⟩
    have hV : ∀ N p q : ℕ, 1 ≤ N → N ≤ p → p ≤ q → q + 1 ≤ 2 * N → q < M →
        ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖
          ≤ 50 * R := by
      intro N p q hN hp hpq hq hqM
      have hNM : N < M := by omega
      have hNlt : (N : ℝ) < |γ| / (Real.pi * b) := by
        rw [hMd] at hNM; exact Nat.lt_ceil.mp hNM
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hγpos : 0 < |γ| := by
        by_contra h
        have h0 : |γ| = 0 := le_antisymm (not_lt.mp h) (abs_nonneg γ)
        rw [h0, zero_div] at hNlt
        linarith
      have hγ0 : γ ≠ 0 := abs_pos.mp hγpos
      have hs0 : 0 ≤ Real.sqrt |γ| := Real.sqrt_nonneg _
      have hss : Real.sqrt |γ| * Real.sqrt |γ| = |γ| := Real.mul_self_sqrt (abs_nonneg γ)
      have h1 : |γ| / (Real.pi * b) ≤ |γ| / b := by
        apply div_le_div_of_nonneg_left (abs_nonneg γ) hb
        have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        nlinarith
      have h2 : |γ| / b ≤ R * Real.sqrt |γ| := by
        rw [div_le_iff₀ hb]
        have := mul_le_mul_of_nonneg_left hsγb hs0
        nlinarith
      exact block_fifty_aux508 hγ0 hN hp hpq hq hsγ (by linarith)
    have hlow := halving_weighted_sum508
      (fun n : ℕ => ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β))
      hρ0.le hστ hτ h50 M hV M le_rfl
    have hMτ : (M : ℝ) ^ τ ≤ (X : ℝ) ^ Θ :=
      (Real.rpow_le_rpow (Nat.cast_nonneg M) (by exact_mod_cast hMX) (by linarith)).trans hXτ
    have hlow' : ‖∑ n ∈ Finset.Ico 1 M, (((n : ℝ) ^ σ : ℝ) : ℂ) *
        ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤ 400 * ((X : ℝ) ^ Θ * R) := by
      refine hlow.trans ?_
      have h9 := mul_le_mul_of_nonneg_right hMτ hR0
      calc 8 * (M : ℝ) ^ τ * (50 * R) = 400 * ((M : ℝ) ^ τ * R) := by ring
        _ ≤ 400 * ((X : ℝ) ^ Θ * R) := by linarith only [h9]
    obtain ⟨a, had⟩ : ∃ a : ℕ, a = max M 1 := ⟨_, rfl⟩
    have ha1 : 1 ≤ a := by rw [had]; exact le_max_right _ _
    have haM : M ≤ a := by rw [had]; exact le_max_left _ _
    have haX : a ≤ X := by rw [had]; exact max_le hMX hX
    have hIcoM : Finset.Ico 1 a = Finset.Ico 1 M := by
      ext x; simp only [Finset.mem_Ico]; omega
    have hhigh : ‖∑ n ∈ Finset.Ico a X, (((n : ℝ) ^ σ : ℝ) : ℂ) *
        ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤ 2 * ((X : ℝ) ^ Θ * R) := by
      rcases Nat.lt_or_ge a X with hlt | hge
      · have hIco : Finset.Ico a X = Finset.Icc a (X - 1) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
        rw [hIco]
        have hB := abel_monotone_weight508 (fun n : ℕ => (n : ℝ) ^ σ)
          (fun n : ℕ => ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β))
          a (X - 1) (by omega) (2 / b)
          (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) σ)
          (fun n _ => Real.rpow_le_rpow (Nat.cast_nonneg n) (by push_cast; linarith) hρ0.le)
          (fun m hm => by
            have hm' := Finset.mem_Icc.mp hm
            have hmM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : M ≤ m)
            have hγm : |γ| ≤ Real.pi * |β| * m := by
              rw [← hbd]
              have := (div_le_iff₀ hπb).mp (hMge.trans hmM)
              linarith
            have := log_phase_tail_kl508 hβ0 (by rw [← hbd]; exact hβ2)
              (by omega : 1 ≤ m) hm'.2 hγm
            rw [← hbd] at this
            exact this)
        have hX1 : (1 : ℝ) ≤ ((X - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ X - 1)
        have hX1le : ((X - 1 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.sub_le X 1
        have hw : ((X - 1 : ℕ) : ℝ) ^ σ ≤ (X : ℝ) ^ Θ :=
          (Real.rpow_le_rpow_of_exponent_le hX1 (hστ.trans hτΘ)).trans
            (Real.rpow_le_rpow (by linarith) hX1le (by linarith))
        have h2b : 2 / b ≤ 2 * R := by
          have : 2 / b = 2 * (1 / b) := by ring
          rw [this]; linarith
        have h2b0 : (0 : ℝ) ≤ 2 / b := by positivity
        calc _ ≤ ((X - 1 : ℕ) : ℝ) ^ σ * (2 / b) := hB
          _ ≤ (X : ℝ) ^ Θ * (2 * R) := mul_le_mul hw h2b h2b0 hXΘ0
          _ = 2 * ((X : ℝ) ^ Θ * R) := by ring
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
        positivity
    rw [← Finset.sum_Ico_consecutive _ ha1 haX, hIcoM]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 400 * ((X : ℝ) ^ Θ * R) + 2 * ((X : ℝ) ^ Θ * R) := add_le_add hlow' hhigh
      _ ≤ 500 * ((X : ℝ) ^ Θ * R) := by linarith only [hXR]
      _ = 500 * (X : ℝ) ^ Θ * R := by ring

end LeanLab.BhowmikGrimmelt2026
