module

public import LeanLab.Pintz2018.Statements

/-!
Theorem J of Pintz 2018, page 17, with the algebraic proof on page 33.
The final theorem has the existing cited Prop as its conclusion.
It is CONDITIONAL ON the zero density estimate 8.2.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Decomp117

/-- LEAF. Page 33, display 8.1. Weights at least one increase a sum of nonnegative excesses. -/
theorem leaf_weighted_excess {ι : Type*} (s : Finset ι) (A p : ι → ℝ) (psi : ℝ)
    (hA : ∀ j ∈ s, 1 ≤ A j) (hp : ∀ j ∈ s, psi ≤ p j) :
    (∑ j ∈ s, (p j - psi)) ≤ ∑ j ∈ s, A j * (p j - psi) := by
  apply Finset.sum_le_sum
  intro j hj
  simpa using mul_le_mul_of_nonneg_right (hA j hj) (sub_nonneg.mpr (hp j hj))

/-- LEAF. Page 30, display 7.5, used in 8.2 on page 33.
The weighted excess restores the centered sum with N prime equal to the sum of weights. -/
theorem leaf_centered_identity {ι : Type*} (s : Finset ι) (A p : ι → ℝ) (psi xi : ℝ) :
    (∑ j ∈ s, A j) * (psi - xi) + (∑ j ∈ s, A j * (p j - psi)) =
      (∑ j ∈ s, (A j * p j - xi)) + xi * ((s.card : ℝ) - ∑ j ∈ s, A j) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- LEAF. Page 33, displays 8.2 and 8.3.
Expand the square and discard the nonnegative square of D prime. -/
theorem leaf_drop_square (n Delta d xi eps : ℝ)
    (h : (n * Delta + d) ^ 2 ≤ n + xi * (n ^ 2 - n) + eps * n ^ 2) :
    n ^ 2 * (Delta ^ 2 - xi - eps) + n * (2 * Delta * d) ≤ n * (1 - xi) := by
  nlinarith [sq_nonneg d]

/-- LEAF. Page 33, displays 8.3 and 8.4.
A positive count and a nonnegative quadratic coefficient give the linear bound. -/
theorem leaf_positive_count (n Delta d xi eps : ℝ) (hn : 0 < n)
    (hDelta : 0 < Delta) (hgap : xi + eps ≤ Delta ^ 2)
    (h : n ^ 2 * (Delta ^ 2 - xi - eps) + n * (2 * Delta * d) ≤ n * (1 - xi)) :
    d ≤ (1 - xi) / (2 * Delta) := by
  have hquad : 0 ≤ n ^ 2 * (Delta ^ 2 - xi - eps) :=
    mul_nonneg (sq_nonneg n) (by linarith)
  have hlin : n * (2 * Delta * d) ≤ n * (1 - xi) := by linarith
  have hcancel : 2 * Delta * d ≤ 1 - xi := (mul_le_mul_iff_right₀ hn).mp hlin
  exact (le_div_iff₀ (by positivity : 0 < 2 * Delta)).mpr (by nlinarith)

/-- LEAF. Page 33, display 8.2, the empty zero set case.
A zero count forces the weighted excess to vanish. -/
theorem leaf_zero_count (d : ℝ) (h : d ^ 2 ≤ 0) : d = 0 := by
  nlinarith [sq_nonneg d]

/-- LEAF. Page 17, display 4.36.
A nonnegative explicit error in the numerator preserves the bound. -/
theorem leaf_error_allowance (d xi e Delta : ℝ) (hDelta : 0 < Delta) (he : 0 ≤ e)
    (h : d ≤ (1 - xi) / (2 * Delta)) : d ≤ (1 - xi + e) / (2 * Delta) := by
  exact h.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- Theorem J assembled as the exact existing cited Prop.
CONDITIONAL ON display 8.2 and the comparison from display 8.1.
The finite error is explicitly small enough for the gap in display 8.3. -/
theorem theoremJ_bound_of_leaves (D N Dprime : ℝ → ℝ) (xi e Delta eps : ℝ)
    (hDelta : 0 < Delta) (hxi : xi ≤ 1) (he : 0 ≤ e)
    (hgap : xi + eps ≤ Delta ^ 2)
    (hN : ∀ L, 0 ≤ N L)
    (hcompare : ∀ L, D L ≤ Dprime L)
    (h82 : ∀ L, (N L * Delta + Dprime L) ^ 2 ≤
      N L + xi * ((N L) ^ 2 - N L) + eps * (N L) ^ 2) :
    TheoremJ_bound D xi e Delta := by
  intro L
  apply leaf_error_allowance (D L) xi e Delta hDelta he
  apply (hcompare L).trans
  by_cases hn : N L = 0
  · have hd : Dprime L = 0 := leaf_zero_count (Dprime L) (by simpa [hn] using h82 L)
    rw [hd]
    exact div_nonneg (sub_nonneg.mpr hxi) (by positivity)
  · exact leaf_positive_count (N L) Delta (Dprime L) xi eps
      (lt_of_le_of_ne (hN L) (Ne.symm hn)) hDelta hgap
      (leaf_drop_square (N L) Delta (Dprime L) xi eps (h82 L))

end LeanLab.Pintz2018.Decomp117
