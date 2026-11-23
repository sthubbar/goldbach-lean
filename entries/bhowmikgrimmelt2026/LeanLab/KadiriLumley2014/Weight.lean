module

public import Mathlib

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 pages 9 and 10, Section 3.1 and Lemma 3.1.
Journal INTEGERS 14 A61 pages 12 and 13.
The weight below is the polynomial on the integration interval.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The smooth weight on the interval zero to one. -/
def weight (m : ℕ) (t : ℝ) : ℝ := (4 * t * (1 - t)) ^ m

/-- Reflection symmetry of the polynomial weight. -/
theorem weight_symm (m : ℕ) (t : ℝ) : weight m (1 - t) = weight m t := by
  unfold weight
  congr 1
  ring

/-- The weight is nonnegative on the integration interval. -/
theorem weight_nonneg (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ weight m t := by
  unfold weight
  exact pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.1) (sub_nonneg.mpr ht.2)) _

/-- The midpoint has weight one. -/
theorem weight_half (m : ℕ) : weight m (1 / 2) = 1 := by norm_num [weight]

/-- The weight vanishes at both endpoints for positive m. -/
theorem weight_endpoints {m : ℕ} (hm : 0 < m) : weight m 0 = 0 ∧ weight m 1 = 0 := by
  simp [weight, ne_of_gt hm]

/-- The polynomial weight is continuous. -/
theorem weight_continuous (m : ℕ) : Continuous (weight m) := by
  unfold weight
  fun_prop

/-- Its mass on zero to one is strictly positive. -/
theorem weight_mass_pos (m : ℕ) : 0 < ∫ t in (0 : ℝ)..1, weight m t := by
  apply intervalIntegral.integral_pos (by norm_num) (weight_continuous m).continuousOn
  · intro x hx
    exact weight_nonneg m ⟨hx.1.le, hx.2⟩
  · exact ⟨1 / 2, by norm_num, by rw [weight_half]; norm_num⟩

/-- Reflection puts the first moment at one half the mass. -/
theorem weight_first_moment (m : ℕ) :
    (∫ t in (0 : ℝ)..1, t * weight m t) = (∫ t in (0 : ℝ)..1, weight m t) / 2 := by
  have hi : IntervalIntegrable (weight m) volume 0 1 :=
    (weight_continuous m).intervalIntegrable _ _
  have ht : IntervalIntegrable (fun t => t * weight m t) volume 0 1 :=
    (continuous_id.mul (weight_continuous m)).intervalIntegrable _ _
  have href := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => t * weight m t) (a := 0) (b := 1) 1
  norm_num only [sub_self, sub_zero] at href
  simp_rw [weight_symm] at href
  have heq : (fun t : ℝ => (1 - t) * weight m t) =
      (fun t => weight m t - t * weight m t) := by ext t; ring
  rw [heq, intervalIntegral.integral_sub hi ht] at href
  linarith

/-- Exact normalized zeroth factor for the paper's symmetric weight. -/
theorem weight_F0_exact (m : ℕ) (δ : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 + δ * t) * weight m t) /
      (∫ t in (0 : ℝ)..1, weight m t) = 1 + δ / 2 := by
  have hi : IntervalIntegrable (weight m) volume 0 1 :=
    (weight_continuous m).intervalIntegrable _ _
  have ht : IntervalIntegrable (fun t => t * weight m t) volume 0 1 :=
    (continuous_id.mul (weight_continuous m)).intervalIntegrable _ _
  have heq : (fun t : ℝ => (1 + δ * t) * weight m t) =
      (fun t => weight m t + δ * (t * weight m t)) := by ext t; ring
  rw [heq, intervalIntegral.integral_add hi (ht.const_mul δ),
    intervalIntegral.integral_const_mul, weight_first_moment]
  have hmass := (weight_mass_pos m).ne'
  field_simp

/-- Lemma 3.1 first line follows from the exact expression. -/
theorem weight_F0_bounds (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 ≤ (∫ t in (0 : ℝ)..1, (1 + δ * t) * weight m t) /
      (∫ t in (0 : ℝ)..1, weight m t) ∧
    (∫ t in (0 : ℝ)..1, (1 + δ * t) * weight m t) /
      (∫ t in (0 : ℝ)..1, weight m t) ≤ 1 + δ := by
  rw [weight_F0_exact]
  constructor <;> linarith

end LeanLab.KadiriLumley2014.Task64
