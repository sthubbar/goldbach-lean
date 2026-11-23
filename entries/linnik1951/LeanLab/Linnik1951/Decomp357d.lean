module

public import LeanLab.Linnik1951.Decomp357c

/-!
P0093 page 154 equation 2.2 and page 167 equation 10.2. Circle partition.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. P0093 page 154 equation 2.2. Termwise integration of the
absolutely convergent product counts its finite ordered representation fiber.
This is the full circle coefficient identity before any arc partition. -/
theorem count_circle_coefficient357 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) =
      (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
  exact count_circle_coefficient_proved435_up111 k N hN

/-- P0093 page 167 partition before equation 10.1. Integrating a continuous
function over the unit interval gives the sum of its three arc integrals. -/
theorem integral_circle_partition357 (N : ℕ) (hN : 1 ≤ N) (η : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in Set.Icc (0 : ℝ) 1, f α) =
      (∫ α in majorArcs280 N, f α) +
      (∫ α in exceptionalArcs280 N η, f α) +
      (∫ α in goodMinorArcs280 N η, f α) := by
  have hM := measurable_major357 N
  have hE := measurable_exceptional357 N hN η
  have hR : MeasurableSet (goodMinorArcs280 N η) :=
    measurableSet_Icc.diff (hM.union hE)
  have hsM : majorArcs280 N ⊆ Set.Icc 0 1 := fun _ h => h.1
  have hsE : exceptionalArcs280 N η ⊆ Set.Icc 0 1 := fun _ h => h.1
  have hsR : goodMinorArcs280 N η ⊆ Set.Icc 0 1 := Set.diff_subset
  have hi : IntegrableOn f (Set.Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have hd : Disjoint (majorArcs280 N) (exceptionalArcs280 N η) := by
    rw [Set.disjoint_left]
    intro α hM hE
    exact hE.2.1 hM
  have hd' : Disjoint (majorArcs280 N ∪ exceptionalArcs280 N η)
      (goodMinorArcs280 N η) := Set.disjoint_sdiff_right
  have hu : majorArcs280 N ∪ exceptionalArcs280 N η ∪ goodMinorArcs280 N η =
      Set.Icc 0 1 := by
    change _ ∪ (Set.Icc 0 1 \ _) = _
    exact Set.union_diff_cancel (Set.union_subset hsM hsE)
  rw [← hu, setIntegral_union hd' hR
    (hi.mono_set (Set.union_subset hsM hsE)) (hi.mono_set hsR),
    setIntegral_union hd hE (hi.mono_set hsM) (hi.mono_set hsE)]

/-- P0093 page 154 equation 2.2 and page 167 equation 10.2. Exact
circle_partition280 statement. CONDITIONAL on the full circle coefficient leaf. -/
theorem circle_partition_decomposed357 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111 k N : ℝ) =
      arcContribution280 k N (majorArcs280 N) +
      arcContribution280 k N (exceptionalArcs280 N η) +
      arcContribution280 k N (goodMinorArcs280 N η) := by
  have hS := continuous_prime_fourier111 N hN
  have hT := continuous_power_fourier111 N hN
  have hf : Continuous (fun α : ℝ => primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by fun_prop
  have hp := integral_circle_partition357 N hN η _ hf
  have hc := congrArg Complex.re (count_circle_coefficient357 k N hN)
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.natCast_re, zero_mul] at hc
  have hid : (representationCount111 k N : ℝ) =
      Real.exp 1 * (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re := by
    rw [hc, ← mul_assoc, he, one_mul]
  rw [hid, hp]
  simp only [arcContribution280, Complex.add_re]
  ring

end LeanLab.Linnik1951
