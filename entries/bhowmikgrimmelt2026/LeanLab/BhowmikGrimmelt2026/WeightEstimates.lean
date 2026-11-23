module

public import LeanLab.BhowmikGrimmelt2026.FourierCentral

/-!
Equations 7.6 and 7.7 at centered frequencies, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open scoped FourierTransform ContDiff

/-- For bases at least one, a larger natural power gives a smaller reciprocal. -/
theorem one_div_pow_le_rpow_neg {T A : ℝ} {k : ℕ} (hT : 1 ≤ T) (hk : A ≤ k) :
    1 / T ^ k ≤ T ^ (-A) := by
  have hT0 : 0 < T := by linarith
  rw [one_div, Real.rpow_neg hT0.le, ← Real.rpow_natCast]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hT hk)

/-- Global rapid Fourier decay for every real exponent. -/
theorem fourier_decay {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖𝓕 (fun x : ℝ => (G x : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-A) := by
  obtain ⟨C, hC, hF⟩ := fourier_decay_nat hsupp hsmooth ⌈A⌉₊
  refine ⟨C, hC, fun ξ => ?_⟩
  calc
    _ ≤ C / (1 + |ξ|) ^ ⌈A⌉₊ := hF ξ
    _ = C * (1 / (1 + |ξ|) ^ ⌈A⌉₊) := by ring
    _ ≤ C * (1 + |ξ|) ^ (-A) := mul_le_mul_of_nonneg_left
      (one_div_pow_le_rpow_neg (by linarith [abs_nonneg ξ]) (Nat.le_ceil A)) hC.le

/-- The uniform Poisson approximation at every real exponent and centered frequency. -/
theorem GThat_poisson_error {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G) (A : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ T β : ℝ, 1 ≤ T → |β| ≤ 1 / 2 →
      ‖GThat G T β - 𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β)‖ ≤ D * T ^ (-A) := by
  let k : ℕ := ⌈A⌉₊ + 2
  have hk : 1 < k := by omega
  have hAk : A ≤ (k : ℝ) := by
    dsimp [k]
    push_cast
    linarith [Nat.le_ceil A]
  obtain ⟨D, hD, herror⟩ := GThat_poisson_error_nat hsupp hsmooth hk
  refine ⟨D, hD, fun T β hT hβ => ?_⟩
  calc
    _ ≤ D / T ^ k := herror T β (by linarith) hβ
    _ = D * (1 / T ^ k) := by ring
    _ ≤ D * T ^ (-A) := mul_le_mul_of_nonneg_left (one_div_pow_le_rpow_neg hT hAk) hD.le

/-- Equation 7.6 with beta chosen in the centered unit interval. -/
theorem GThat_bound_centered {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T β : ℝ, 1 ≤ T → |β| ≤ 1 / 2 →
      ‖GThat G T β‖ ≤ C * ((1 + T * |β|) ^ (-A) + T ^ (-A)) := by
  obtain ⟨C, hC, hF⟩ := fourier_decay hsupp hsmooth A
  obtain ⟨D, hD, herror⟩ := GThat_poisson_error hsupp hsmooth A
  refine ⟨C + D, by positivity, fun T β hT hβ => ?_⟩
  have hT0 : 0 < T := by linarith
  have hf : ‖𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β)‖ ≤
      C * (1 + T * |β|) ^ (-A) := by
    simpa only [abs_mul, abs_neg, abs_of_pos hT0] using hF (-T * β)
  calc
    _ ≤ ‖GThat G T β - 𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β)‖ +
        ‖𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (GThat G T β - 𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β))
        (𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β))
    _ ≤ D * T ^ (-A) + C * (1 + T * |β|) ^ (-A) := add_le_add (herror T β hT hβ) hf
    _ ≤ (C + D) * ((1 + T * |β|) ^ (-A) + T ^ (-A)) := by
      nlinarith [mul_nonneg hC.le (Real.rpow_nonneg hT0.le (-A)),
        mul_nonneg hD.le (Real.rpow_nonneg (by positivity : 0 ≤ 1 + T * |β|) (-A))]

/-- Equation 7.7 with beta chosen in the centered unit interval. -/
theorem GThat_central_centered {G : ℝ → ℝ} (hG : IsMajorWeight G) (A : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ T β : ℝ, 1 ≤ T → |β| ≤ 1 / 2 →
      ‖GThat G T β - 1‖ ≤ 8 * Real.pi ^ 2 * (T * β) ^ 2 + D * T ^ (-A) := by
  obtain ⟨D, hD, herror⟩ := GThat_poisson_error hG.supp hG.smooth A
  refine ⟨D, hD, fun T β hT hβ => ?_⟩
  have hf := fourier_weight_quadratic hG (-T * β)
  have hsum := add_le_add (herror T β hT hβ) hf
  have hn : ‖GThat G T β - 1‖ ≤
      ‖GThat G T β - 𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β)‖ +
      ‖𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β) - 1‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (GThat G T β - 𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β))
      (𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β) - 1)
  calc
    _ ≤ D * T ^ (-A) + 8 * Real.pi ^ 2 * (-T * β) ^ 2 := hn.trans hsum
    _ = 8 * Real.pi ^ 2 * (T * β) ^ 2 + D * T ^ (-A) := by ring

end LeanLab.BhowmikGrimmelt2026
