module

public import LeanLab.Linnik1951.Decomp357f

/-!
P0093 page 162 equation 7.4. Termwise phase integration for summable coefficients.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 162 equation 7.4. The Fourier coefficient functional is
integration against the negative integer phase on the unit interval. -/
theorem coefficient_integral357 (f : ℝ → ℂ) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f i =
      ∫ α in (0 : ℝ)..1, LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) * f α := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero, one_div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro α hα
  dsimp only
  rw [smul_eq_mul]
  congr 1
  rw [fourier_coe_apply]
  unfold LeanLab.Perelli1996.Kernel.e
  push_cast
  ring

/-- P0093 page 162 equation 7.4. Integer phase orthogonality for one
negative natural frequency, reusing the proved lab phase integral. -/
theorem negative_phase_coefficient357 (u : ℕ) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      if i = -(u : ℤ) then 1 else 0 := by
  rw [coefficient_integral357]
  have hp (α : ℝ) : LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) *
      Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I) =
      LeanLab.Perelli1996.Kernel.e (((-i - (u : ℤ) : ℤ) : ℝ) * α) := by
    unfold LeanLab.Perelli1996.Kernel.e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc,
    LeanLab.Perelli1996.Parseval103.integral_e_int]
  have hz : -i - (u : ℤ) = 0 ↔ i = -(u : ℤ) := by omega
  simp only [hz]

/-- P0093 page 162 equation 7.4. Absolute summability permits termwise
integration against any fixed Fourier phase. -/
theorem coefficient_tsum357 (a : ℕ → ℂ) (ha : Summable a) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => ∑' u : ℕ, a u *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      ∑' u : ℕ, a u * (if i = -(u : ℤ) then 1 else 0) := by
  let F : ℕ → ℝ → ℂ := fun u α =>
    LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) *
      (a u * Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I))
  have hF (u : ℕ) : Continuous (F u) := by
    dsimp [F, LeanLab.Perelli1996.Kernel.e]
    fun_prop
  have hFnorm (u : ℕ) (α : ℝ) : ‖F u α‖ = ‖a u‖ := by
    dsimp [F, LeanLab.Perelli1996.Kernel.e]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I]
    simp [Complex.norm_exp]
  have hI (u : ℕ) : IntegrableOn (F u) (Set.Ioc (0 : ℝ) 1) :=
    (hF u).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnormI (u : ℕ) : (∫ α in Set.Ioc (0 : ℝ) 1, ‖F u α‖) = ‖a u‖ := by
    simp only [hFnorm]
    simp
  have hswap := integral_tsum_of_summable_integral_norm hI
    (ha.norm.congr (fun u => (hnormI u).symm))
  rw [coefficient_integral357, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hs (α : ℝ) : LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) *
      (∑' u : ℕ, a u * Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) =
      ∑' u : ℕ, F u α := tsum_mul_left.symm
  simp_rw [hs]
  rw [← hswap]
  apply tsum_congr
  intro u
  have heq : (∫ α in Set.Ioc (0 : ℝ) 1, F u α) =
      a u * fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i := by
    rw [coefficient_integral357, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro α hα
    dsimp [F]
    ring
  rw [heq, negative_phase_coefficient357]

/-- P0093 page 162 equation 7.4. Exact negative_series_coefficient280
statement, with no prime or representation count assumption. -/
theorem negative_series_coefficient_proved357 (a : ℕ → ℂ) (ha : Summable a) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => ∑' u : ℕ, a u *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      if i ≤ 0 then a i.natAbs else 0 := by
  rw [coefficient_tsum357 a ha i]
  by_cases hi : i ≤ 0
  · rw [if_pos hi]
    have habs : i = -(i.natAbs : ℤ) := by omega
    rw [tsum_eq_single i.natAbs]
    · rw [if_pos habs, mul_one]
    · intro u hu
      have hne : i ≠ -(u : ℤ) := by
        intro heq
        apply hu
        have := congrArg Int.natAbs heq
        simpa using this.symm
      simp [hne]
  · rw [if_neg hi]
    have hne (u : ℕ) : i ≠ -(u : ℤ) := by omega
    simp only [hne, ite_false, mul_zero, tsum_zero]

/-- P0093 page 162 equation 7.4. Exact fourier_coefficient111 statement,
now using only the three clean convergence, grouping and integration proofs. -/
theorem fourier_coefficient_proved357 (N : ℕ) (hN : 1 ≤ N) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => primeFourier111 N α * powerFourier111 N α) i =
        if i ≤ 0 then
          ((primePowerCount111 i.natAbs : ℝ) * Real.exp (-(i.natAbs : ℝ) / N) : ℂ)
        else 0 := by
  simp_rw [product_grouped_proved357 N hN]
  exact negative_series_coefficient_proved357 _ (grouped_summable_proved357 N hN) i

end LeanLab.Linnik1951
