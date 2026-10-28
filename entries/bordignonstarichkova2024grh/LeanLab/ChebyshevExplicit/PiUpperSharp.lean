module

public import LeanLab.ChebyshevExplicit.PiUpper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
AI wrote the Lean code. Codex task04, 2026-10-21.

Chebyshev's explicit theta bound inside Abel summation.
This file derives bounds from Psi30Upper and Mathlib's Abel identity.
The resulting constants are derived here, not quoted from a paper.
Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- The natural-input theta bound extends to every real input at least two. -/
theorem theta_le_11062_real {x : ℝ} (hx : 2 ≤ x) :
    θ x ≤ 1.1062 * x + 2 * log x ^ 2 + 160 := by
  have hfloor : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have h : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    exact_mod_cast h
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlog : log (⌊x⌋₊ : ℝ) ≤ log x :=
    log_le_log (by linarith) hle
  have hlog0 : 0 ≤ log (⌊x⌋₊ : ℝ) := log_nonneg hfloor
  rw [theta_eq_theta_coe_floor]
  exact (theta_le_11062 ⌊x⌋₊).trans (by
    nlinarith [sq_le_sq₀ hlog0 (log_nonneg (by linarith : 1 ≤ x)) |>.mpr hlog])

/-- Abel's integral with the sharper theta bound and both error terms integrated. -/
theorem integral_theta_le_11062 {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤
      1.1062 * (4 * x / log x ^ 2 + x.sqrt / log 2 ^ 2)
        + 2 * (log x - log 2) + 160 * (1 / log 2 - 1 / log x) := by
  have hlog2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have hlogx : log x ≠ 0 := (log_pos (by linarith)).ne'
  have hi1 := intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 < x)
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)] at ht
    exact (continuousAt_id.inv₀ (by dsimp; linarith [ht.1])).continuousWithinAt
  have hi3 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / log t ^ 2)
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  calc
    _ ≤ ∫ t in 2..x, 1.1062 * (1 / log t ^ 2) + 2 * t⁻¹
        + 160 * (t⁻¹ / log t ^ 2) := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_
        (((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)) ?_
      · rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith),
          ← integrableOn_Icc_iff_integrableOn_Ioc]
        exact integrableOn_theta_div_id_mul_log_sq x
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt : 0 < log t := log_pos (by linarith [ht.1])
        calc θ t / (t * log t ^ 2)
            ≤ (1.1062 * t + 2 * log t ^ 2 + 160) / (t * log t ^ 2) :=
              div_le_div_of_nonneg_right (theta_le_11062_real ht.1) (by positivity)
          _ = _ := by field_simp
    _ = 1.1062 * (∫ t in 2..x, 1 / log t ^ 2)
        + 2 * (log x - log 2) + 160 * (1 / log 2 - 1 / log x) := by
      rw [intervalIntegral.integral_add ((hi1.const_mul _).add (hi2.const_mul _))
          (hi3.const_mul _),
        intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_inv_of_pos (by norm_num) (by linarith),
        integral_inv_div_log_sq (by norm_num) (by linarith),
        log_div (by linarith : x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      simp [one_div]
    _ ≤ _ := by
      gcongr
      exact integral_one_div_log_sq_le hx

/-- The coefficient of `x / log x ^ 2` is `4 * 1.1062 = 4.4248`. -/
theorem pi_le_11062_sharp_real {x : ℝ} (hx : 4 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.1062 * x / log x + 4.4248 * x / log x ^ 2
        + 1.1062 * x.sqrt / log 2 ^ 2 + 4 * log x + 160 / log 2 - 2 * log 2 := by
  have hl : 0 < log x := log_pos (by linarith)
  have h2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  calc
    _ = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2) :=
      primeCounting_eq_theta_div_log_add_integral (by linarith)
    _ ≤ (1.1062 * x + 2 * log x ^ 2 + 160) / log x
        + (1.1062 * (4 * x / log x ^ 2 + x.sqrt / log 2 ^ 2)
          + 2 * (log x - log 2) + 160 * (1 / log 2 - 1 / log x)) :=
      add_le_add (div_le_div_of_nonneg_right (theta_le_11062_real (by linarith)) hl.le)
        (integral_theta_le_11062 hx)
    _ = _ := by field_simp; ring

/-- The sharper explicit prime-counting bound at natural inputs. -/
theorem pi_le_11062_sharp (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤
      1.1062 * n / log n + 4.4248 * n / log n ^ 2
        + 1.1062 * (n : ℝ).sqrt / log 2 ^ 2 + 4 * log n + 160 / log 2 - 2 * log 2 := by
  have hx : (4 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Nat.floor_natCast] using pi_le_11062_sharp_real hx

/-- Use the smaller explicit bound at every natural input at least four. -/
theorem pi_le_11062_best (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ min
      ((1.1062 * n + 2 * log n ^ 2 + 160) / log n
        + log 4 * (4 * n / log n ^ 2 + (n : ℝ).sqrt / log 2 ^ 2))
      (1.1062 * n / log n + 4.4248 * n / log n ^ 2
        + 1.1062 * (n : ℝ).sqrt / log 2 ^ 2 + 4 * log n + 160 / log 2 - 2 * log 2) :=
  le_min (pi_le_11062 n hn) (pi_le_11062_sharp n hn)

end LeanLab.ChebyshevExplicit
