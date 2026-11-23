module

public import LeanLab.Perelli1996.Parseval103

/-!
Perelli 1996, page 481 equation 2 and page 486 equation 27.
The finite geometric principal kernel has an explicit Fourier coefficient.
This uses the existing inclusive zero endpoint convention for Kernel.T.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Principal320
open Finset MeasureTheory
noncomputable section

/-- The full period coefficient of the squared principal kernel is m plus one.
Pages 481 and 486, principal term extraction with the inclusive zero endpoint.
The one unit difference from m is the endpoint term. -/
theorem full_coefficient (M m : ℕ) (hm : m ≤ M) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) = (m + 1 : ℂ) := by
  classical
  have hterm (p q : ℕ) :
      (∫ α in Set.Icc (0 : ℝ) 1,
        Kernel.e ((p : ℝ) * α) * Kernel.e ((q : ℝ) * α) * Kernel.e (-(m : ℝ) * α)) =
      if p + q = m then 1 else 0 := by
    have heq (α : ℝ) :
        Kernel.e ((p : ℝ) * α) * Kernel.e ((q : ℝ) * α) * Kernel.e (-(m : ℝ) * α) =
        Kernel.e ((((p : ℤ) + q - m : ℤ) : ℝ) * α) := by
      rw [← Parseval103.e_add, ← Parseval103.e_add]
      congr 1
      push_cast
      ring
    simp_rw [heq]
    rw [Parseval103.integral_e_int]
    have hz : ((p : ℤ) + q - m = 0) ↔ p + q = m := by omega
    rw [if_congr hz rfl rfl]
  have hexpand (α : ℝ) :
      Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α) =
      ∑ p ∈ range (M + 1), ∑ q ∈ range (M + 1),
        Kernel.e ((p : ℝ) * α) * Kernel.e ((q : ℝ) * α) * Kernel.e (-(m : ℝ) * α) := by
    unfold Kernel.T
    simp only [zero_add, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hint (p q : ℕ) : IntegrableOn (fun α : ℝ =>
      Kernel.e ((p : ℝ) * α) * Kernel.e ((q : ℝ) * α) * Kernel.e (-(m : ℝ) * α))
      (Set.Icc 0 1) volume := by
    apply Continuous.integrableOn_Icc
    unfold Kernel.e
    fun_prop
  have hi (p : ℕ) :
      (∫ α in Set.Icc (0 : ℝ) 1, ∑ q ∈ range (M + 1),
        Kernel.e ((p : ℝ) * α) * Kernel.e ((q : ℝ) * α) * Kernel.e (-(m : ℝ) * α)) =
      ∑ q ∈ range (M + 1), ∫ α in Set.Icc (0 : ℝ) 1,
        Kernel.e ((p : ℝ) * α) * Kernel.e ((q : ℝ) * α) * Kernel.e (-(m : ℝ) * α) :=
    integral_finsetSum _ (fun q _ => hint p q)
  simp_rw [hexpand]
  rw [integral_finsetSum]
  · simp_rw [hi, hterm]
    have hinner (p : ℕ) : (∑ q ∈ range (M + 1), if p + q = m then (1 : ℂ) else 0) =
        if p ≤ m then 1 else 0 := by
      by_cases hp : p ≤ m
      · rw [if_pos hp, Finset.sum_eq_single (m - p)]
        · simp [Nat.add_sub_of_le hp]
        · intro q hq hne
          rw [if_neg (by omega)]
        · intro hnot
          have hmem : m - p ∈ range (M + 1) := Finset.mem_range.mpr (by omega)
          exact (hnot hmem).elim
      · rw [if_neg hp]
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg (by omega)]
    simp_rw [hinner]
    have hsum : (∑ p ∈ range (M + 1), if p ≤ m then (1 : ℂ) else 0) =
        ∑ _p ∈ range (m + 1), (1 : ℂ) := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hm 1))]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [if_pos (by have := Finset.mem_range.mp hp; omega)]
      · intro p hp hpnot
        rw [if_neg (by simp only [Finset.mem_range] at hpnot; omega)]
    rw [hsum]
    simp
  · intro p hp
    exact integrable_finsetSum _ (fun q _ => hint p q)

end
end LeanLab.Perelli1996.Principal320
