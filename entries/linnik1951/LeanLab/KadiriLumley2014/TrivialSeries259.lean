module

public import LeanLab.KadiriLumley2014.TrivialDerivative301
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4 equation 2.15.
The trivial-zero derivative series equals one half of the logarithmic remainder.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Real Set
open LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- The negative even real power is the corresponding power of the inverse square. -/
theorem negative_even_rpow {y : ℝ} (hy : 0 < y) (n : ℕ) :
    y ^ (-2 * ((n : ℝ) + 1)) = (1 / y ^ 2) ^ (n + 1) := by
  rw [show -2 * ((n : ℝ) + 1) = (-2 : ℝ) * (n + 1 : ℕ) by push_cast; ring,
    Real.rpow_mul_natCast hy.le]
  congr 1
  rw [Real.rpow_neg hy.le, Real.rpow_two, one_div]

/-- The derivative summands of the integrated trivial-zero series sum to the logarithm. -/
theorem hasSum_trivial_derivatives {y : ℝ} (hy : 1 < y) :
    HasSum (fun n : ℕ => -y ^ (-2 * ((n : ℝ) + 1)) / (2 * n + 2))
      (Real.log (1 - 1 / y ^ 2) / 2) := by
  have hq : |1 / y ^ 2| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    nlinarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hq).mul_left (-1 / 2)
  convert h using 1
  · funext n
    rw [negative_even_rpow (by linarith : 0 < y)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    field_simp
  · ring

/-- On y above two the derivative summands have a fixed summable geometric bound. -/
theorem trivial_derivative_bound (n : ℕ) {y : ℝ} (hy : 2 < y) :
    ‖-y ^ (-2 * ((n : ℝ) + 1)) / (2 * n + 2)‖ ≤
      (1 / 4 : ℝ) ^ (n + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [norm_div, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (by positivity), negative_even_rpow (by linarith)]
  have hq : 1 / y ^ 2 ≤ (1 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  calc
    _ ≤ (1 / y ^ 2) ^ (n + 1) := div_le_self (by positivity) (by linarith)
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hq _

/-- The complete integrated trivial-zero contribution is differentiable above two. -/
theorem hasDerivAt_trivial_series {y : ℝ} (hy : 2 < y) :
    HasDerivAt (fun y : ℝ => y * ∑' n : ℕ, tb y n)
      (Real.log (1 - 1 / y ^ 2) / 2) y := by
  have hs : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_right (1 / 4)
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioi (convex_Ioi (2 : ℝ)).isPreconnected
    (fun n z hz => Task301.hasDerivAt_y_tb n (by change 2 < z at hz; linarith))
    (fun n z hz => trivial_derivative_bound n hz)
    (show (3 : ℝ) ∈ Ioi (2 : ℝ) by norm_num)
    ((summable_tb (by norm_num : (1 : ℝ) ≤ 3)).mul_left 3) hy
  rw [(hasSum_trivial_derivatives (by linarith : 1 < y)).tsum_eq] at hd
  simpa only [tsum_mul_left] using hd

end LeanLab.KadiriLumley2014.Task259
