module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5791.

# Orthogonality on [0, 1] for the circle method

`e(x) = exp(2πix)`. `integral_ee_int`: `∫₀¹ e(kα) dα = 1` if `k = 0` and `0` for every other
integer `k`. From it, for any finite family `a`:

* `parseval`: `∫₀¹ S(α) conj(S(α)) dα = Σ |a n|²`, `S(α) = Σ_{n ∈ s} a n e(nα)`;
* `parseval_norm`: the real form `∫₀¹ ‖S(α)‖² dα = Σ ‖a n‖²`;
* `ternary_orth`: `∫₀¹ S(α)³ e(-Nα) dα = Σ_{x + y + z = N} a x a y a z`, the circle method identity.

KNOWN mathematics. The lab's other circle method files work on `ZMod M`; this is the continuous
form Zinoviev 1997 (0.4) and (3.17) use. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.CircleOrth
open Complex Finset

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * x)

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; push_cast; ring_nf

theorem conj_ee (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

theorem continuous_ee : Continuous ee := by
  unfold ee; fun_prop

/-- `∫₀¹ e(kα) dα = [k = 0]` for integers `k`. -/
theorem integral_ee_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, ee (k * α) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [ee]
  · have hc : (2 * Real.pi * I * k : ℂ) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [hpi, hk', Complex.I_ne_zero]
    have h1 : ∀ α : ℝ, ee (k * α) = Complex.exp ((2 * Real.pi * I * k) * α) := by
      intro α; unfold ee; push_cast; ring_nf
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((2 * Real.pi * I * k) * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I k
      rw [← this]; congr 1; push_cast; ring
    rw [h2]; simp

/-- The integer frequency form used below: `∫₀¹ e((m - n)α) dα = [m = n]`. -/
theorem integral_ee_sub (m n : ℤ) :
    ∫ α in (0 : ℝ)..1, ee (((m - n : ℤ) : ℝ) * α) = if m = n then 1 else 0 := by
  rw [integral_ee_int]; simp [sub_eq_zero]

/-- The exponential sum `S(α) = Σ_{n ∈ s} a n e(nα)`. -/
noncomputable def S (s : Finset ℤ) (a : ℤ → ℂ) (α : ℝ) : ℂ := ∑ n ∈ s, a n * ee (n * α)

theorem continuous_S (s : Finset ℤ) (a : ℤ → ℂ) : Continuous (S s a) := by
  unfold S
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id))

/-- **Parseval** on `[0, 1]`. -/
theorem parseval (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ α in (0 : ℝ)..1, S s a α * (starRingEnd ℂ) (S s a α) =
      ∑ n ∈ s, a n * (starRingEnd ℂ) (a n) := by
  have hexp : ∀ α : ℝ, S s a α * (starRingEnd ℂ) (S s a α) =
      ∑ m ∈ s, ∑ n ∈ s, (a m * (starRingEnd ℂ) (a n)) * ee (((m - n : ℤ) : ℝ) * α) := by
    intro α
    unfold S
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, conj_ee]
    have : ee (((m - n : ℤ) : ℝ) * α) = ee (m * α) * ee (-(n * α)) := by
      rw [← ee_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · have : ∀ m ∈ s, ∫ α in (0 : ℝ)..1, ∑ n ∈ s,
        (a m * (starRingEnd ℂ) (a n)) * ee (((m - n : ℤ) : ℝ) * α) =
        a m * (starRingEnd ℂ) (a m) := by
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul, integral_ee_sub]
        simp [hm]
      · intro n _
        exact ((continuous_ee.comp (continuous_const.mul continuous_id)).const_mul _
          ).intervalIntegrable _ _
    exact Finset.sum_congr rfl this
  · intro m _
    refine (continuous_finsetSum _ fun n _ => ?_).intervalIntegrable _ _
    exact (continuous_ee.comp (continuous_const.mul continuous_id)).const_mul _

/-- **Parseval**, real form: `∫₀¹ ‖S(α)‖² dα = Σ ‖a n‖²`. -/
theorem parseval_norm (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ α in (0 : ℝ)..1, ‖S s a α‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have h := parseval s a
  simp_rw [Complex.mul_conj'] at h
  have h2 : ∫ α in (0 : ℝ)..1, ((‖S s a α‖ ^ 2 : ℝ) : ℂ) = ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h
  rw [intervalIntegral.integral_ofReal] at h2
  exact_mod_cast h2

/-- The circle method identity: `∫₀¹ S(α)³ e(-Nα) dα = Σ_{x+y+z=N} a x a y a z`. -/
theorem ternary_orth (s : Finset ℤ) (a : ℤ → ℂ) (N : ℤ) :
    ∫ α in (0 : ℝ)..1, S s a α ^ 3 * ee (-(N * α)) =
      ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, if x + y + z = N then a x * a y * a z else 0 := by
  have hexp : ∀ α : ℝ, S s a α ^ 3 * ee (-(N * α)) =
      ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, (a x * a y * a z) * ee ((((x + y + z) - N : ℤ) : ℝ) * α) := by
    intro α
    unfold S
    rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    have : ee ((((x + y + z) - N : ℤ) : ℝ) * α) =
        ee (x * α) * (ee (y * α) * ee (z * α)) * ee (-(N * α)) := by
      rw [← ee_add, ← ee_add, ← ee_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hexp]
  have hint : ∀ c : ℂ, ∀ k : ℤ, IntervalIntegrable (fun α : ℝ => c * ee ((k : ℝ) * α))
      MeasureTheory.volume 0 1 := fun c k =>
    ((continuous_ee.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun x _ => by
    refine (continuous_finsetSum _ fun y _ => continuous_finsetSum _ fun z _ => ?_
      ).intervalIntegrable _ _
    exact (continuous_ee.comp (continuous_const.mul continuous_id)).const_mul _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun y _ => by
    refine (continuous_finsetSum _ fun z _ => ?_).intervalIntegrable _ _
    exact (continuous_ee.comp (continuous_const.mul continuous_id)).const_mul _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun z _ => hint _ _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_ee_int]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (by omega) h2
  · exact absurd (by omega) h1
  · simp

end LeanLab.CircleOrth
