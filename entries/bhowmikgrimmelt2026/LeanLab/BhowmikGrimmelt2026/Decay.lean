module

public import LeanLab.BhowmikGrimmelt2026.Poisson

/-!
Rapid Fourier decay used on page 26 in Lemma 7.2.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory Filter Asymptotics
open scoped FourierTransform SchwartzMap ContDiff

/-- A compactly supported smooth real weight has a Schwartz complex lift. -/
noncomputable def weightSchwartz {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G) :
    𝓢(ℝ, ℂ) :=
  ((HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).comp_left
    (g := Complex.ofReal) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hsmooth)

/-- Global rapid decay of the continuous Fourier transform, at every natural power. -/
theorem fourier_decay_nat {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) (hsmooth : ContDiff ℝ ∞ G) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖𝓕 (fun x : ℝ => (G x : ℂ)) ξ‖ ≤ C / (1 + |ξ|) ^ k := by
  let f := weightSchwartz hsupp hsmooth
  let M := 2 ^ k * (Finset.Iic (k, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 f)
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro ξ
  rw [le_div_iff₀ (by positivity)]
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl (𝓕 f) ξ
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  change (1 + |ξ|) ^ k * ‖𝓕 (fun x : ℝ => (G x : ℂ)) ξ‖ ≤ M at h
  calc
    _ = (1 + |ξ|) ^ k * ‖𝓕 (fun x : ℝ => (G x : ℂ)) ξ‖ := mul_comm _ _
    _ ≤ M := h
    _ ≤ max M 1 := le_max_left _ _

/-- Integer samples of any Schwartz function form a summable series. -/
theorem schwartz_summable_int (f : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => f n) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
  exact (f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite

end LeanLab.BhowmikGrimmelt2026
