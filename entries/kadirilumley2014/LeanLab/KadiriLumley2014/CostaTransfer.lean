module

public import LeanLab.KadiriLumley2014.OmegaBound

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 3, Lemma 2.1 and equation 2.10.
Journal INTEGERS 14 A61 page 4 equations 9 and 10.
Costa Lemma 2.1 remains a named cited input.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- Costa Pereira 1985 Theorem 5, cited as Lemma 2.1 of Kadiri and Lumley 2014.
The Chebyshev functions use the standard Mathlib definitions. -/
def CostaEstimate : Prop := ∀ x : ℝ, Real.exp 38 ≤ x →
  0.999 * Real.sqrt x + x ^ (1 / 3 : ℝ) < Chebyshev.psi x - Chebyshev.theta x ∧
  Chebyshev.psi x - Chebyshev.theta x < 1.001 * Real.sqrt x + x ^ (1 / 3 : ℝ)

/-- Square root scaling for a positive exponential. -/
theorem sqrt_exp_mul (u Y : ℝ) (_hY : 0 ≤ Y) :
    Real.sqrt (Real.exp u * Y) = Real.exp (u / 2) * Real.sqrt Y := by
  rw [Real.sqrt_mul (Real.exp_nonneg u), Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 2
  ring

/-- Cube root scaling for a positive exponential. -/
theorem cbrt_exp_mul (u Y : ℝ) (hY : 0 ≤ Y) :
    (Real.exp u * Y) ^ (1 / 3 : ℝ) = Real.exp (u / 3) * Y ^ (1 / 3 : ℝ) := by
  rw [Real.mul_rpow (Real.exp_nonneg u) hY, ← Real.exp_mul]
  congr 2
  ring

/-- The change in psi minus theta is bounded by the two scaled root terms.
This is conditional on CostaEstimate. -/
theorem costa_gap_scaled (hCosta : CostaEstimate) {u Y : ℝ}
    (hu : 0 ≤ u) (hY : Real.exp 38 ≤ Y) :
    (Chebyshev.psi (Real.exp u * Y) - Chebyshev.theta (Real.exp u * Y)) -
      (Chebyshev.psi Y - Chebyshev.theta Y) <
      (1.001 * Real.exp (u / 2) - 0.999) * Real.sqrt Y +
        (Real.exp (u / 3) - 1) * Y ^ (1 / 3 : ℝ) := by
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos 38) hY
  have hexp : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hAY : Y ≤ Real.exp u * Y := by nlinarith
  have hl := (hCosta Y hY).1
  have hh := (hCosta (Real.exp u * Y) (hY.trans hAY)).2
  rw [sqrt_exp_mul u Y hY0.le, cbrt_exp_mul u Y hY0.le] at hh
  linarith

/-- Root factoring for the error coefficient in equation 2.10. -/
theorem root_factor_sixth {X A : ℝ} (hX : 0 < X) (hA : 0 < A) :
    Real.sqrt X * Real.sqrt A * (X ^ (-(1 : ℝ) / 6) * A ^ (-(1 : ℝ) / 6)) =
      (X * A) ^ (1 / 3 : ℝ) := by
  have hx : Real.sqrt X * X ^ (-(1 : ℝ) / 6) = X ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX]
    norm_num
  have ha : Real.sqrt A * A ^ (-(1 : ℝ) / 6) = A ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hA]
    norm_num
  rw [Real.mul_rpow hX.le hA.le]
  calc
    Real.sqrt X * Real.sqrt A * (X ^ (-(1 : ℝ) / 6) * A ^ (-(1 : ℝ) / 6)) =
      (Real.sqrt X * X ^ (-(1 : ℝ) / 6)) * (Real.sqrt A * A ^ (-(1 : ℝ) / 6)) := by ring
    _ = X ^ (1 / 3 : ℝ) * A ^ (1 / 3 : ℝ) := by rw [hx, ha]

/-- Full pointwise omega bound after the cited Costa estimate.
This is conditional on CostaEstimate. -/
theorem costa_gap_lt_omega (hCosta : CostaEstimate) {u δ X t : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 0.0001) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Chebyshev.psi (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (Real.exp u * (X * (1 + δ * t)))) -
      (Chebyshev.psi (X * (1 + δ * t)) - Chebyshev.theta (X * (1 + δ * t))) <
        (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 38) hX
  have hA0 : 0 < 1 + δ := by linarith
  have hdt0 : 0 ≤ δ * t := mul_nonneg hδ ht0
  have hdt1 : δ * t ≤ δ := by nlinarith
  have hY : Real.exp 38 ≤ X * (1 + δ * t) :=
    hX.trans (le_mul_of_one_le_right hX0.le (by linarith))
  have hY0 : 0 ≤ X * (1 + δ * t) := (Real.exp_pos 38).le.trans hY
  have hYm : X * (1 + δ * t) ≤ X * (1 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hX0.le
  have hc := costa_gap_scaled hCosta hu hY
  have he2 : 1 ≤ Real.exp (u / 2) := Real.one_le_exp_iff.mpr (by linarith)
  have he3 : 1 ≤ Real.exp (u / 3) := Real.one_le_exp_iff.mpr (by linarith)
  have hC : 0 ≤ 1.001 * Real.exp (u / 2) - 0.999 := by linarith
  have hD : 0 ≤ Real.exp (u / 3) - 1 := by linarith
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hYm) hC
  have hr := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY0 hYm (by norm_num : (0 : ℝ) ≤ 1 / 3)) hD
  have hbound :
      (1.001 * Real.exp (u / 2) - 0.999) * Real.sqrt (X * (1 + δ * t)) +
        (Real.exp (u / 3) - 1) * (X * (1 + δ * t)) ^ (1 / 3 : ℝ) ≤
      Real.sqrt X * (Real.sqrt (1 + δ) *
        (1.001 * Real.exp (u / 2) - 0.999 + X ^ (-(1 : ℝ) / 6) *
          (1 + δ) ^ (-(1 : ℝ) / 6) * (Real.exp (u / 3) - 1))) := by
    have heq : Real.sqrt X * (Real.sqrt (1 + δ) *
        (1.001 * Real.exp (u / 2) - 0.999 + X ^ (-(1 : ℝ) / 6) *
          (1 + δ) ^ (-(1 : ℝ) / 6) * (Real.exp (u / 3) - 1))) =
        (1.001 * Real.exp (u / 2) - 0.999) * Real.sqrt (X * (1 + δ)) +
          (Real.exp (u / 3) - 1) * (X * (1 + δ)) ^ (1 / 3 : ℝ) := by
      rw [Real.sqrt_mul hX0.le, ← root_factor_sixth hX0 hA0]
      ring
    rw [heq]
    linarith
  have hω := mul_lt_mul_of_pos_left (omega_coefficient_lt hu hu1 hδ hδ1 hX)
    (Real.sqrt_pos.2 hX0)
  nlinarith

end LeanLab.KadiriLumley2014.Task64
