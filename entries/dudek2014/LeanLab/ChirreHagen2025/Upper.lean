module

public import Mathlib
public import LeanLab.ChirreHagen2025.Statements

/-!
P0075 Chirre-Hagen 2025: the first display of Section 5 from Theorem 3. The integrand is a
square of a difference of two nonnegative monotone functions, so it is interval integrable,
and it is nonnegative, so the integral over `[a x, x]` is at most the integral over `[1, x]`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The integrand of `J_θ` is interval integrable on `[c, d]` for `0 ≤ c ≤ d`, `δ > 0`. -/
theorem integrand_intervalIntegrable {δ c d : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    IntervalIntegrable (fun y => (θ ((1 + δ) * y) - θ y - δ * y) ^ 2) MeasureTheory.volume c d := by
  set A : ℝ → ℝ := fun y => θ ((1 + δ) * y) with hA
  set B : ℝ → ℝ := fun y => θ y + δ * y with hB
  have hs : Set.uIcc c d = Set.Icc c d := Set.uIcc_of_le hcd
  have hAm : MonotoneOn A (Set.uIcc c d) := fun u _ v _ huv =>
    theta_mono (by nlinarith)
  have hBm : MonotoneOn B (Set.uIcc c d) := fun u _ v _ huv => by
    simp only [hB]; have := theta_mono huv; nlinarith
  have hA0 : ∀ y ∈ Set.uIcc c d, 0 ≤ A y := fun y _ => theta_nonneg _
  have hB0 : ∀ y ∈ Set.uIcc c d, 0 ≤ B y := fun y hy => by
    rw [hs] at hy
    have := theta_nonneg y
    simp only [hB]; nlinarith [hy.1]
  have iAA := (hAm.mul hAm hA0 hA0).intervalIntegrable (μ := MeasureTheory.volume)
  have iAB := (hAm.mul hBm hA0 hB0).intervalIntegrable (μ := MeasureTheory.volume)
  have iBB := (hBm.mul hBm hB0 hB0).intervalIntegrable (μ := MeasureTheory.volume)
  have := (iAA.sub (iAB.const_mul 2)).add iBB
  refine this.congr ?_
  intro y _
  simp only [Pi.mul_apply, hA, hB]
  ring

/-- `J_θ` over `[a x, x]` is at most `J_θ(x, δ)` when `1 ≤ a x ≤ x`. -/
theorem jFrom_le {a x δ : ℝ} (hδ : 0 < δ) (h1 : 1 ≤ a * x) (h2 : a * x ≤ x) :
    JthetaFrom a x δ ≤ Jtheta x δ := by
  unfold JthetaFrom Jtheta
  have i1 := integrand_intervalIntegrable (δ := δ) hδ zero_le_one h1
  have i2 := integrand_intervalIntegrable (δ := δ) hδ (by linarith) h2
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have : 0 ≤ ∫ y in (1 : ℝ)..a * x, (θ ((1 + δ) * y) - θ y - δ * y) ^ 2 :=
    intervalIntegral.integral_nonneg h1 (fun y _ => sq_nonneg _)
  linarith

/-- Section 5's first display from Theorem 3 in its stated form. -/
theorem section5Upper_of
    (h3 : ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2) :
    Section5Upper := by
  intro a x δ ha ha1 hx hδ hδle
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ a * x := by
    calc (1 : ℝ) = 1 / 10 ^ 13 * 10 ^ 13 := by norm_num
      _ ≤ a * x := by gcongr
  have h2 : a * x ≤ x := by nlinarith
  exact le_trans (jFrom_le hδ h1 h2) (h3 x δ hx hδ hδle)

/-- So under RH, Section 5's upper bound needs only Theorem 3. -/
theorem section5Upper_of_RH
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2) :
    RiemannHypothesis → Section5Upper :=
  fun hRH => section5Upper_of (h3 hRH)

end LeanLab.ChirreHagen2025
