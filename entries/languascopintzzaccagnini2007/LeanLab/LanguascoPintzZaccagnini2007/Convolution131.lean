module

public import LeanLab.LanguascoPintzZaccagnini2007.Minor131

/-!
P0045 displays 3 to 6 on pages 3 and 4. Fourier inversion for the truncated count.
The finite sum manipulations use the paper proof and Mathlib finite product expansion.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- The count in display 3 with every exponent at most L - sqrt L. -/
def truncatedCount131 (k X N : ℕ) : ℝ :=
  ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X,
    ∑ ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊),
      if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else 0

/-- Match the phase to the existing lab finite Parseval library. -/
theorem phase_eq_library131 (t : ℝ) : phase131 t = LeanLab.PNTPort.LargeSieve.e t := by
  unfold phase131 LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- Multiplication of phases adds their arguments. -/
theorem phase_add131 (s t : ℝ) : phase131 s * phase131 t = phase131 (s + t) := by
  unfold phase131
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Integer arguments give phase one. -/
theorem phase_int131 (n : ℤ) : phase131 n = 1 := by
  rw [phase_eq_library131]
  exact LeanLab.PNTPort.LargeSieve.e_int n

/-- Orthogonality on every shifted unit interval, used in displays 4 to 6. -/
theorem phase_integral131 (a : ℝ) (n : ℤ) :
    (∫ α in a..a + 1, phase131 (n * α)) = if n = 0 then 1 else 0 := by
  have hp : Function.Periodic (fun α : ℝ => phase131 (n * α)) 1 := by
    intro α
    change phase131 ((n : ℝ) * (α + 1)) = phase131 ((n : ℝ) * α)
    rw [show (n : ℝ) * (α + 1) = (n : ℝ) * α + n by ring,
      ← phase_add131, phase_int131, mul_one]
  have he := hp.intervalIntegral_add_eq a (-(1 / 2 : ℝ))
  norm_num only [neg_add_cancel_left] at he
  rw [he]
  simp_rw [phase_eq_library131]
  convert LeanLab.PNTPort.Gallagher.integral_e_int n using 1

/-- The kth power of G is the sum over the k exponent tuples in display 3. -/
theorem powerSum_pow131 (X k : ℕ) (α : ℝ) :
    powerSum131 X α ^ k =
      ∑ ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊),
        phase131 (((∑ i, 2 ^ ν i : ℕ) : ℝ) * α) := by
  unfold powerSum131
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  apply sum_congr rfl
  intro ν _
  unfold phase131
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [sum_mul, mul_sum]

/-- The square of S is the sum over the two prime power variables in display 3. -/
theorem primeSum_sq131 (X : ℕ) (α : ℝ) :
    primeSum131 X α ^ 2 = ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X,
      ((Λ m₁ : ℂ) * (Λ m₂ : ℂ)) * phase131 (((m₁ + m₂ : ℕ) : ℝ) * α) := by
  unfold primeSum131
  rw [sq, sum_mul_sum]
  apply sum_congr rfl
  intro m₁ _
  apply sum_congr rfl
  intro m₂ _
  rw [show ((Λ m₁ : ℂ) * phase131 ((m₁ : ℝ) * α)) *
      ((Λ m₂ : ℂ) * phase131 ((m₂ : ℝ) * α)) =
      ((Λ m₁ : ℂ) * (Λ m₂ : ℂ)) *
        (phase131 ((m₁ : ℝ) * α) * phase131 ((m₂ : ℝ) * α)) by ring,
    phase_add131]
  congr 2
  push_cast
  ring

/-- Expand the entire Fourier integrand in displays 5 and 6. -/
theorem integrand_expansion131 (k X N : ℕ) (α : ℝ) :
    primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α) =
      ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊),
          ((Λ m₁ : ℂ) * (Λ m₂ : ℂ)) *
            phase131 ((((m₁ + m₂ + ∑ i, 2 ^ ν i : ℕ) : ℤ) - N : ℤ) * α) := by
  rw [primeSum_sq131, powerSum_pow131, sum_mul, sum_mul]
  apply sum_congr rfl
  intro m₁ _
  rw [sum_mul, sum_mul]
  apply sum_congr rfl
  intro m₂ _
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro ν _
  rw [mul_assoc, mul_assoc, phase_add131, phase_add131]
  congr 2
  push_cast
  ring

/-- Fourier inversion gives the exact truncated weighted count in displays 3 to 6. -/
theorem circle_identity131 (k X N : ℕ) (a : ℝ) :
    (∫ α in a..a + 1,
      primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)) =
        (truncatedCount131 k X N : ℂ) := by
  simp_rw [integrand_expansion131]
  have hc (c : ℂ) (n : ℤ) : Continuous (fun α : ℝ => c * phase131 (n * α)) :=
    continuous_const.mul (phase_continuous131.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_finsetSum (fun m₁ _ =>
    (continuous_finsetSum _ (fun m₂ _ => continuous_finsetSum _ (fun ν _ => hc _ _))).intervalIntegrable _ _)]
  unfold truncatedCount131
  simp only [Complex.ofReal_sum]
  apply sum_congr rfl
  intro m₁ _
  rw [intervalIntegral.integral_finsetSum (fun m₂ _ =>
    (continuous_finsetSum _ (fun ν _ => hc _ _)).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro m₂ _
  rw [intervalIntegral.integral_finsetSum (fun ν _ => (hc _ _).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro ν _
  rw [intervalIntegral.integral_const_mul, phase_integral131]
  by_cases h : m₁ + m₂ + ∑ i, 2 ^ ν i = N
  · rw [ite_eq_left (by rw [h]; ring), ite_eq_left h, mul_one]
    push_cast
    rfl
  · rw [ite_eq_right (by intro he; apply h; omega), ite_eq_right h, mul_zero]
    simp

/-- Page 3: when Q >= P+2, the major arcs lie in the shifted unit interval. -/
theorem majorArcs_subset131 {X : ℕ} {P : ℝ} (hX : 0 < X) (hP : 0 < P)
    (hQ : P + 2 ≤ arcQ131 X P) :
    majorArcs131 X P ⊆ Set.Icc (1 / arcQ131 X P) (1 / arcQ131 X P + 1) := by
  intro α hα
  obtain ⟨q, a, hq, hqP, ha, _, hlo, hhi⟩ := hα
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.mp ha).1
  have haq : (a : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp ha).2
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hQ0 : 0 < arcQ131 X P := div_pos hX0 hP
  have hlow : 1 / arcQ131 X P ≤ (a : ℝ) / q - 1 / ((q : ℝ) * arcQ131 X P) := by
    apply (mul_le_mul_iff_left₀ (mul_pos hq0 hQ0)).mp
    have he1 : (1 / arcQ131 X P) * ((q : ℝ) * arcQ131 X P) = q := by field_simp
    have he2 : ((a : ℝ) / q - 1 / ((q : ℝ) * arcQ131 X P)) *
        ((q : ℝ) * arcQ131 X P) = (a : ℝ) * arcQ131 X P - 1 := by
      field_simp
    rw [he1, he2]
    nlinarith [mul_le_mul_of_nonneg_right ha1 hQ0.le]
  have hfrac : (a : ℝ) / q ≤ 1 := (div_le_one hq0).mpr haq
  have hwidth : 1 / ((q : ℝ) * arcQ131 X P) ≤ 1 / arcQ131 X P :=
    one_div_le_one_div_of_le hQ0 (by nlinarith)
  exact ⟨hlow.trans hlo, by linarith⟩

/-- Displays 4 to 6: the major and minor integrals sum to the truncated count. -/
theorem arc_split131 (k X N : ℕ) (P : ℝ) (hX : 0 < X) (hP : 0 < P)
    (hQ : P + 2 ≤ arcQ131 X P) :
    majorContribution131 k X N P + minorContribution131 k X N P = truncatedCount131 k X N := by
  let a := 1 / arcQ131 X P
  let f : ℝ → ℂ := fun α =>
    primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)
  have hc : Continuous f :=
    (((primeSum_continuous131 X).pow 2).mul ((powerSum_continuous131 X).pow k)).mul
      (phase_continuous131.comp (continuous_const.mul continuous_id))
  have hi : IntegrableOn f (Set.Icc a (a + 1)) := hc.continuousOn.integrableOn_compact isCompact_Icc
  have hs := integral_inter_add_sdiff (majorArcs_measurable131 X P) hi
  rw [Set.inter_eq_right.mpr (majorArcs_subset131 hX hP hQ)] at hs
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : a ≤ a + 1)] at hs
  have hcircle : (∫ α in a..a + 1, f α) = (truncatedCount131 k X N : ℂ) := circle_identity131 k X N a
  rw [hcircle] at hs
  have hr := congrArg Complex.re hs
  change (∫ α in majorArcs131 X P, f α).re +
      (∫ α in Set.Icc a (a + 1) \ majorArcs131 X P, f α).re = truncatedCount131 k X N at hr
  simpa only [majorContribution131, minorContribution131, minorArcs131, a, f, add_comm (1 : ℝ)] using hr

/-- The truncated weighted count is nonnegative. -/
theorem truncatedCount_nonneg131 (k X N : ℕ) : 0 ≤ truncatedCount131 k X N := by
  apply sum_nonneg
  intro m₁ _
  apply sum_nonneg
  intro m₂ _
  apply sum_nonneg
  intro ν _
  split_ifs
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

end

end LeanLab.LPZ2007
