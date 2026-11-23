module

public import LeanLab.BhowmikGrimmelt2026.Decay

/-!
Uniform bounds for the nonzero translates in the Poisson identity, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

/-- A centered frequency stays at least half an integer spacing from nonzero integers. -/
theorem int_sub_centered_lower {β : ℝ} (hβ : |β| ≤ 1 / 2) {m : ℤ} (hm : m ≠ 0) :
    |(m : ℝ)| / 2 ≤ |(m : ℝ) - β| := by
  have hn : (1 : ℝ) ≤ |(m : ℝ)| := by
    have hpos : (0 : ℤ) < |m| := abs_pos.mpr hm
    have hone : (1 : ℤ) ≤ |m| := by omega
    exact_mod_cast hone
  have htriangle := abs_sub_le (m : ℝ) β 0
  simp only [sub_zero] at htriangle
  linarith

/-- Pointwise bound for a nonzero Poisson translate, uniform over centered beta. -/
theorem poisson_term_bound {F : ℝ → ℂ} {C T β : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hT : 0 < T) (hβ : |β| ≤ 1 / 2)
    (hF : ∀ ξ : ℝ, ‖F ξ‖ ≤ C / (1 + |ξ|) ^ k) {m : ℤ} (hm : m ≠ 0) :
    ‖F (T * ((m : ℝ) - β))‖ ≤
      (C * 2 ^ k / T ^ k) * (|(m : ℝ)| ^ k)⁻¹ := by
  have hmpos : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  have hl := int_sub_centered_lower hβ hm
  have habs : T * |(m : ℝ)| / 2 ≤ 1 + |T * ((m : ℝ) - β)| := by
    rw [abs_mul, abs_of_pos hT]
    nlinarith
  calc
    _ ≤ C / (1 + |T * ((m : ℝ) - β)|) ^ k := hF _
    _ ≤ C / (T * |(m : ℝ)| / 2) ^ k :=
      div_le_div_of_nonneg_left hC (by positivity)
        (pow_le_pow_left₀ (by positivity) habs k)
    _ = (C * 2 ^ k / T ^ k) * (|(m : ℝ)| ^ k)⁻¹ := by
      rw [div_pow, mul_pow]
      field_simp <;> ring

/-- Summing all nonzero Poisson translates gives a uniform inverse power of T. -/
theorem poisson_tail_bound {F : ℝ → ℂ} {C T β : ℝ} {k : ℕ}
    (hk : 1 < k) (hC : 0 ≤ C) (hT : 0 < T) (hβ : |β| ≤ 1 / 2)
    (hF : ∀ ξ : ℝ, ‖F ξ‖ ≤ C / (1 + |ξ|) ^ k) :
    ‖∑' m : ℤ, if m = 0 then 0 else F (T * ((m : ℝ) - β))‖ ≤
      (C * 2 ^ k / T ^ k) * ∑' m : ℤ, (|(m : ℝ)| ^ k)⁻¹ := by
  let v : ℤ → ℝ := fun m => (|(m : ℝ)| ^ k)⁻¹
  let g : ℤ → ℂ := fun m => if m = 0 then 0 else F (T * ((m : ℝ) - β))
  let D : ℝ := C * 2 ^ k / T ^ k
  have hv : Summable v := by
    have hkr : (1 : ℝ) < k := by exact_mod_cast hk
    simpa [v, Real.rpow_neg, Real.rpow_natCast] using Real.summable_abs_int_rpow hkr
  have hbound (m : ℤ) : ‖g m‖ ≤ D * v m := by
    by_cases hm : m = 0
    · simp [g, hm, D, v, show k ≠ 0 by omega]
    · simpa [g, hm, D, v] using poisson_term_bound hC hT hβ hF hm
  have hDv : Summable (fun m => D * v m) := hv.mul_left D
  have hn : Summable (fun m => ‖g m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg (g m)) hbound hDv
  calc
    ‖∑' m, g m‖ ≤ ∑' m, ‖g m‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' m, D * v m := hn.tsum_le_tsum hbound hDv
    _ = D * ∑' m, v m := tsum_mul_left

/-- The Fourier series on the right side of the exact Poisson identity is summable. -/
theorem summable_poisson {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (hsmooth : ContDiff ℝ ∞ G) {T : ℝ} (hT : 0 < T) (β : ℝ) :
    Summable (fun m : ℤ => 𝓕 (fun x : ℝ => (G x : ℂ))
      (T * ((m : ℝ) - β))) := by
  have hc : HasCompactSupport (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) :=
    ((GT_hasCompactSupport hsupp hT).comp_left (g := Complex.ofReal) rfl).mul_right
  have hs : ContDiff ℝ ∞ (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) :=
    (Complex.ofRealCLM.contDiff.comp (GT_contDiff hsmooth T)).mul
      (ee_contDiff.comp (contDiff_const.mul contDiff_id))
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hs
  have h := schwartz_summable_int (𝓕 f)
  change Summable (fun m : ℤ =>
    𝓕 (fun x : ℝ => (GT G T x : ℂ) * ee (β * x)) (m : ℝ)) at h
  exact h.congr (fun m => fourier_modulated_GT G hT β m)

/-- Uniform Poisson approximation at centered frequencies, for each natural power above one. -/
theorem GThat_poisson_error_nat {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G)
    {k : ℕ} (hk : 1 < k) :
    ∃ D : ℝ, 0 < D ∧ ∀ T β : ℝ, 0 < T → |β| ≤ 1 / 2 →
      ‖GThat G T β - 𝓕 (fun x : ℝ => (G x : ℂ)) (-T * β)‖ ≤ D / T ^ k := by
  obtain ⟨C, hC, hF⟩ := fourier_decay_nat hsupp hsmooth k
  let S : ℝ := ∑' m : ℤ, (|(m : ℝ)| ^ k)⁻¹
  have hS : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  refine ⟨max (C * 2 ^ k * S) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro T β hT hβ
  have hsum := summable_poisson hsupp hsmooth hT β
  rw [GThat_poisson hsupp hsmooth hT β, hsum.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, zero_sub, mul_neg, neg_mul, add_sub_cancel_left]
  calc
    _ ≤ (C * 2 ^ k / T ^ k) * S := poisson_tail_bound hk hC.le hT hβ hF
    _ = (C * 2 ^ k * S) / T ^ k := by ring
    _ ≤ max (C * 2 ^ k * S) 1 / T ^ k :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

end LeanLab.BhowmikGrimmelt2026
