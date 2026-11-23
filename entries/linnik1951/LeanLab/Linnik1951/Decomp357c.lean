module

public import LeanLab.Linnik1951.Decomp357b
public import LeanLab.Linnik1951.Decomp357i
public import LeanLab.Linnik1951.Asymptotics357

/-!
P0093 pages 161 and 165 to 167. Exceptional prime mass and power series growth.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- P0093 pages 165 and 166. The rational major arcs form a measurable set. -/
theorem measurable_major357 (N : ℕ) : MeasurableSet (majorArcs280 N) := by
  unfold majorArcs280
  simp only [Set.setOf_and, Set.setOf_exists]
  apply measurableSet_Icc.inter
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.inter
  · exact MeasurableSet.const _
  · exact isClosed_le (by fun_prop) continuous_const |>.measurableSet

/-- P0093 page 167 before equation 10.1. The actual large T minor set is measurable. -/
theorem measurable_exceptional357 (N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    MeasurableSet (exceptionalArcs280 N η) := by
  unfold exceptionalArcs280
  simp only [Set.setOf_and]
  exact measurableSet_Icc.inter ((measurable_major357 N).compl.inter
    (isOpen_lt continuous_const (continuous_power_fourier111 N hN).norm).measurableSet)


/-- LEAF. P0093 page 161 equation 7.1 and the triangle inequality.
The damped powers of two series is uniformly bounded by a constant times
log N. This leaf has no GRH or exceptional set hypothesis. -/
theorem power_uniform_log357 :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, ‖powerFourier111 N α‖ ≤ A * Real.log N := by
  exact power_uniform_log_proved357

/-- P0093 page 166 proof of Lemma 7. A uniform power series bound factors
out of the absolute arc integral, leaving only the prime square mass. -/
theorem arc_abs_le_prime_mass357 (k N : ℕ) (hN : 1 ≤ N) (s : Set ℝ)
    (hs : s ⊆ Set.Icc 0 1) (hms : MeasurableSet s) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ α ∈ s, ‖powerFourier111 N α‖ ≤ B) :
    |arcContribution280 k N s| ≤
      Real.exp 1 * B ^ k * (∫ α in s, ‖primeFourier111 N α‖ ^ 2) := by
  have hS := continuous_prime_fourier111 N hN
  have hP := continuous_power_fourier111 N hN
  have hF : Continuous (fun α : ℝ => primeFourier111 N α ^ 2 *
      powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by
    fun_prop
  have hInt : IntegrableOn (fun α : ℝ => primeFourier111 N α ^ 2 *
      powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) s :=
    hF.integrableOn_Icc.mono_set hs
  have hSq : IntegrableOn (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2) s :=
    (hS.norm.pow 2).integrableOn_Icc.mono_set hs
  unfold arcContribution280
  rw [abs_mul, abs_of_pos (Real.exp_pos 1)]
  calc
    _ ≤ Real.exp 1 * ‖∫ α in s, primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, ‖primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, B ^ k * ‖primeFourier111 N α‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      apply setIntegral_mono_on hInt.norm (hSq.const_mul _) hms
      intro α hα
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
      calc
        _ ≤ ‖primeFourier111 N α‖ ^ 2 * B ^ k := by gcongr; exact hT α hα
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring

end LeanLab.Linnik1951
