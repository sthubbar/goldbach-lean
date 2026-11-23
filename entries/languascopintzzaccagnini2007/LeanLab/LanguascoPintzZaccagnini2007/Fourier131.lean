module

public import LeanLab.LanguascoPintzZaccagnini2007.ArcDefinitions131

/-!
P0045 pages 3 and 4. Elementary Fourier infrastructure for the minor arcs.
Mathlib supplies Parseval on a real interval.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real MeasureTheory

noncomputable section

/-- The exponential phases on page 3 have norm one. -/
theorem phase_norm131 (t : ℝ) : ‖phase131 t‖ = 1 := by
  simp [phase131, Complex.norm_exp]

/-- The exponential phases on page 3 are continuous. -/
theorem phase_continuous131 : Continuous phase131 := by
  unfold phase131
  fun_prop

/-- The prime sum of page 3 is continuous. -/
theorem primeSum_continuous131 (X : ℕ) : Continuous (primeSum131 X) := by
  unfold primeSum131
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (phase_continuous131.comp (continuous_const.mul continuous_id))

/-- The power sum of page 3 is continuous. -/
theorem powerSum_continuous131 (X : ℕ) : Continuous (powerSum131 X) := by
  unfold powerSum131
  apply continuous_finsetSum
  intro ν _
  exact phase_continuous131.comp (continuous_const.mul continuous_id)

/-- Page 4 uses the trivial estimate abs(G) <= L. -/
theorem powerSum_norm_le131 {X : ℕ} (hL : 0 ≤ Lg X) (α : ℝ) :
    ‖powerSum131 X α‖ ≤ Lg X := by
  have hcard : (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ≤ Lg X := by
    by_cases h : 0 ≤ Lg X - Real.sqrt (Lg X)
    · exact (Nat.floor_le h).trans (by linarith [Real.sqrt_nonneg (Lg X)])
    · rw [Nat.floor_eq_zero.mpr (by linarith)]
      simpa using hL
  calc ‖powerSum131 X α‖ ≤ ∑ ν ∈ Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊,
        ‖phase131 ((2 : ℝ) ^ ν * α)‖ := norm_sum_le _ _
    _ = (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by simp [phase_norm131]
    _ ≤ Lg X := hcard

/-- The real part of a complex coefficient has square at most its squared norm. -/
theorem real_square_le_norm_square131 (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg z.im]

/-- Page 4 Bessel step, for real parts of coefficients on any shifted unit interval.
This is a direct finite consequence of Mathlib Parseval. -/
theorem bessel_real131 (a : ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a + 1)))) (T : Finset ℕ) :
    ∑ N ∈ T, (fourierCoeffOn (by linarith : a < a + 1) f (N : ℤ)).re ^ 2 ≤
      ∫ x in a..a + 1, ‖f x‖ ^ 2 := by
  classical
  have hsum := hasSum_sq_fourierCoeffOn (by linarith : a < a + 1) hf
  have hbound := hsum.summable.sum_le_tsum (T.image (fun N : ℕ => (N : ℤ)))
    (fun _ _ => sq_nonneg _)
  rw [hsum.tsum_eq] at hbound
  simp only [add_sub_cancel_left, inv_one, one_smul] at hbound
  calc ∑ N ∈ T, (fourierCoeffOn (by linarith : a < a + 1) f (N : ℤ)).re ^ 2
      ≤ ∑ N ∈ T, ‖fourierCoeffOn (by linarith : a < a + 1) f (N : ℤ)‖ ^ 2 :=
        sum_le_sum (fun _ _ => real_square_le_norm_square131 _)
    _ = ∑ n ∈ T.image (fun N : ℕ => (N : ℤ)),
        ‖fourierCoeffOn (by linarith : a < a + 1) f n‖ ^ 2 := by
      rw [sum_image]
      intro m _ n _ h
      exact Int.natCast_inj.mp h
    _ ≤ _ := hbound

/-- Page 3: the major arcs form a measurable set. -/
theorem majorArcs_measurable131 (X : ℕ) (P : ℝ) : MeasurableSet (majorArcs131 X P) := by
  unfold majorArcs131
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ (q : ℝ) ≤ P ∧ a ∈ Icc 1 q ∧ Nat.Coprime a q
  · convert (measurableSet_Icc : MeasurableSet (Set.Icc
        ((a : ℝ) / q - 1 / ((q : ℝ) * arcQ131 X P))
        ((a : ℝ) / q + 1 / ((q : ℝ) * arcQ131 X P)))) using 1
    ext α
    exact ⟨fun hα => hα.2.2.2.2, fun hα => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hα⟩⟩
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ)) using 1
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, _⟩
    exact h ⟨h₁, h₂, h₃, h₄⟩

/-- Page 3: the minor arcs form a measurable set. -/
theorem minorArcs_measurable131 (X : ℕ) (P : ℝ) : MeasurableSet (minorArcs131 X P) := by
  exact measurableSet_Icc.diff (majorArcs_measurable131 X P)

/-- The minor arc indicator times S squared G^k, for the Bessel step on page 4. -/
def minorIntegrand131 (k X : ℕ) (P : ℝ) : ℝ → ℂ :=
  (majorArcs131 X P)ᶜ.indicator (fun α => primeSum131 X α ^ 2 * powerSum131 X α ^ k)

/-- A uniform elementary bound for the prime exponential sum on page 3. -/
theorem primeSum_norm_le131 (X : ℕ) (α : ℝ) :
    ‖primeSum131 X α‖ ≤ ∑ m ∈ Icc 1 X, |(ArithmeticFunction.vonMangoldt m : ℝ)| := by
  calc ‖primeSum131 X α‖ ≤ ∑ m ∈ Icc 1 X,
        ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * phase131 ((m : ℝ) * α)‖ := norm_sum_le _ _
    _ = _ := by simp [phase_norm131]

/-- Display 6 on page 4 is the real Fourier coefficient of the minor integrand. -/
theorem minor_eq_fourier131 (k X N : ℕ) (P : ℝ) :
    minorContribution131 k X N P =
      (fourierCoeffOn (by linarith : 1 / arcQ131 X P < 1 / arcQ131 X P + 1)
        (minorIntegrand131 k X P) (N : ℤ)).re := by
  rw [fourierCoeffOn_eq_integral]
  simp only [add_sub_cancel_left, div_one, one_smul]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  unfold minorContribution131 minorArcs131
  rw [add_comm 1 (1 / arcQ131 X P), Set.sdiff_eq,
    ← setIntegral_indicator (majorArcs_measurable131 X P).compl]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro α _
  unfold minorIntegrand131
  by_cases h : α ∈ (majorArcs131 X P)ᶜ
  · simp only [Set.indicator_of_mem h, smul_eq_mul]
    rw [fourier_coe_apply]
    unfold phase131
    rw [mul_comm (primeSum131 X α ^ 2 * powerSum131 X α ^ k)]
    congr 1
    congr 1
    push_cast
    ring
  · simp [Set.indicator_of_notMem h]

/-- The minor integrand on page 4 is square integrable on its shifted unit interval. -/
theorem minorIntegrand_memLp131 (k X : ℕ) (P : ℝ) (hL : 0 ≤ Lg X) :
    MemLp (minorIntegrand131 k X P) 2
      (volume.restrict (Set.Ioc (1 / arcQ131 X P) (1 / arcQ131 X P + 1))) := by
  have hcont := (primeSum_continuous131 X).pow 2 |>.mul ((powerSum_continuous131 X).pow k)
  have hb : MemLp (fun α => primeSum131 X α ^ 2 * powerSum131 X α ^ k) 2
      (volume.restrict (Set.Ioc (1 / arcQ131 X P) (1 / arcQ131 X P + 1))) := by
    apply MemLp.of_bound hcont.aestronglyMeasurable
      ((∑ m ∈ Icc 1 X, |(ArithmeticFunction.vonMangoldt m : ℝ)|) ^ 2 * Lg X ^ k)
    apply Filter.Eventually.of_forall
    intro α
    change ‖primeSum131 X α ^ 2 * powerSum131 X α ^ k‖ ≤ _
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (primeSum_norm_le131 X α) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (powerSum_norm_le131 hL α) k)
      (by positivity) (by positivity)
  exact hb.indicator (majorArcs_measurable131 X P).compl

/-- Page 4: Bessel bounds the sum of squared real minor contributions by its L2 integral. -/
theorem minor_bessel131 (k X : ℕ) (P : ℝ) (hL : 0 ≤ Lg X) :
    ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
      ∫ α in 1 / arcQ131 X P..1 / arcQ131 X P + 1,
        ‖minorIntegrand131 k X P α‖ ^ 2 := by
  simpa only [minor_eq_fourier131] using
    bessel_real131 (1 / arcQ131 X P) (minorIntegrand131 k X P)
      (minorIntegrand_memLp131 k X P hL) (evenJ131 X)

end

end LeanLab.LPZ2007
