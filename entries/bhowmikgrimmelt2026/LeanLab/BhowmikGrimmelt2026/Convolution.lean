module

public import LeanLab.BhowmikGrimmelt2026.Periodicity

/-!
The finite Fourier convolution identity used before Lemma 7.3, pages 25 and 26.
The orthogonality proof follows the lab's Lu2010Orth.integral_ee for the local ee definition.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Orthogonality of the local additive exponential over a full unit interval. -/
theorem integral_ee_int (j : ℤ) :
    ∫ α in (0 : ℝ)..1, ee ((j : ℝ) * α) = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · subst j
    simp [ee]
  · rw [if_neg hj]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hjc
    have hrw : (fun α : ℝ => ee ((j : ℝ) * α)) =
        fun α : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (j : ℂ)) * α) := by
      funext α
      unfold ee
      congr 1
      push_cast
      ring
    rw [hrw, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hphase : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * j) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * j = (j : ℂ) * (2 * Real.pi * Complex.I) by ring,
        Complex.exp_int_mul_two_pi_mul_I]
    rw [hphase, sub_self, zero_div]

/-- The coefficient of a product of two finite exponential sums is their finite convolution. -/
theorem finite_fourier_convolution (s t : Finset ℕ) (a b : ℕ → ℂ) (m : ℕ) :
    (∫ α in (0 : ℝ)..1,
      (∑ n ∈ s, a n * ee (n * α)) * (∑ k ∈ t, b k * ee (k * α)) * ee (-(m * α))) =
      ∑ n ∈ s, ∑ k ∈ t, if n + k = m then a n * b k else 0 := by
  have hexpand (α : ℝ) :
      (∑ n ∈ s, a n * ee (n * α)) * (∑ k ∈ t, b k * ee (k * α)) * ee (-(m * α)) =
      ∑ n ∈ s, ∑ k ∈ t,
        (a n * b k) * ee ((((n : ℤ) + k - m : ℤ) : ℝ) * α) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = (a n * b k) * ((ee (n * α) * ee (k * α)) * ee (-(m * α))) := by ring
      _ = (a n * b k) * ee ((((n : ℤ) + k - m : ℤ) : ℝ) * α) := by
        rw [ee_mul, ee_mul]
        congr 2
        push_cast
        ring
  simp_rw [hexpand]
  have hi (n k : ℕ) : IntervalIntegrable
      (fun α : ℝ => (a n * b k) * ee ((((n : ℤ) + k - m : ℤ) : ℝ) * α)) volume 0 1 :=
    (continuous_const.mul (ee_contDiff.continuous.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum (s := s)
    (f := fun n α => ∑ k ∈ t, (a n * b k) * ee ((((n : ℤ) + k - m : ℤ) : ℝ) * α))
    (fun n _ => by
      convert IntervalIntegrable.sum t (fun k _ => hi n k) using 1
      ext α
      simp)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finsetSum (fun k _ => hi n k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul, integral_ee_int]
  by_cases h : n + k = m
  · have hz : (n : ℤ) + k - m = 0 := by omega
    simp [h, hz]
  · have hz : (n : ℤ) + k - m ≠ 0 := by omega
    simp [h, hz]

/-- The smoothed convolution is exactly the Nth Fourier coefficient of Sphi squared. -/
theorem rphi_eq_integral (ϕ : ℝ → ℝ) (N : ℕ) :
    (rphi ϕ N : ℂ) = ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * ee (-(N * α)) := by
  let w : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n * ϕ (n / N) : ℝ) : ℂ)
  have h := finite_fourier_convolution (Finset.range (N + 1)) (Finset.range (N + 1)) w w N
  have hset : ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = N)) =
      (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · intro h
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr h.2
    · intro h
      have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp h
      exact ⟨⟨by omega, by omega⟩, heq⟩
  have hsum : (∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      if n + k = N then w n * w k else 0) = (rphi ϕ N : ℂ) := by
    rw [← Finset.sum_product (f := fun p : ℕ × ℕ => if p.1 + p.2 = N then w p.1 * w p.2 else 0),
      ← Finset.sum_filter, hset]
    unfold rphi
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [w]
    push_cast
    ring
  rw [hsum] at h
  exact h.symm.trans (by simp only [Sphi, w, pow_two, mul_comm])

end LeanLab.BhowmikGrimmelt2026
