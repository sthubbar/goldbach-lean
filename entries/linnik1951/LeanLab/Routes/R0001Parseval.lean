module

public import Mathlib

/-!
Route R-0001, T3 MOONSHOT, the binary circle method L2 barrier.
Smallest Lean lemma the route needs: discrete Parseval on ZMod N for Mathlib's `ZMod.dft`.
AI wrote this Lean code. Goldbach is open; nothing here is progress on it.
-/

@[expose] public section

open ZMod Finset

namespace LeanLab.Routes.R0001

variable {N : ℕ} [NeZero N]

lemma conj_stdAddChar (x : ZMod N) :
    (starRingEnd ℂ) (stdAddChar x) = stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, stdAddChar_apply]
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]

/-- Orthogonality of the standard additive character of `ZMod N`. -/
lemma sum_stdAddChar_mul (b : ZMod N) :
    ∑ k : ZMod N, (stdAddChar (k * b) : ℂ) = if b = 0 then (N : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift b (isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

/-- Discrete Parseval for `ZMod.dft`, inner product form. -/
theorem dft_parseval (Φ : ZMod N → ℂ) :
    ∑ k, 𝓕 Φ k * (starRingEnd ℂ) (𝓕 Φ k) = (N : ℂ) * ∑ j, Φ j * (starRingEnd ℂ) (Φ j) := by
  classical
  simp only [dft_apply, smul_eq_mul, map_sum, map_mul, conj_stdAddChar, neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ i j : ZMod N,
      ∑ k : ZMod N, (stdAddChar (-(i * k)) : ℂ) * Φ i * ((stdAddChar (j * k) : ℂ) * (starRingEnd ℂ) (Φ j))
        = Φ i * (starRingEnd ℂ) (Φ j) * (if j - i = 0 then (N : ℂ) else 0) := by
    intro i j
    rw [← sum_stdAddChar_mul (j - i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (stdAddChar (k * (j - i)) : ℂ) = stdAddChar (-(i * k)) * stdAddChar (j * k) := by
      rw [← AddChar.map_add_eq_mul]; ring_nf
    rw [this]; ring
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  simp only [key, sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Discrete Parseval, norm form: the L2 mass of `𝓕 Φ` is `N` times that of `Φ`. -/
theorem dft_parseval_norm (Φ : ZMod N → ℂ) :
    ∑ k, ‖𝓕 Φ k‖ ^ 2 = (N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 := by
  have h := dft_parseval Φ
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- The L2 barrier in the form the route uses: if a set `m` of frequencies, the minor arcs,
misses a set `M` whose L2 mass is at most `A`, then the minor arcs carry at least
`N * ‖Φ‖₂² - A`. With `Φ` the prime indicator weighted by log p, `N ‖Φ‖₂²` is about
`N · x log x` while the binary main term is about `N · x`, so absolute values on the minor
arcs lose a factor log x. -/
theorem minor_l2_ge (Φ : ZMod N → ℂ) (Maj : Finset (ZMod N)) (A : ℝ)
    (hA : ∑ k ∈ Maj, ‖𝓕 Φ k‖ ^ 2 ≤ A) :
    (N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 - A ≤ ∑ k ∈ Majᶜ, ‖𝓕 Φ k‖ ^ 2 := by
  have h := dft_parseval_norm Φ
  rw [← Finset.sum_add_sum_compl Maj] at h
  linarith

/-- Vacuity test: the hypotheses can hold; for `N = 1` and `Φ = 1` both sides equal 1. -/
example : ∑ k : ZMod 1, ‖𝓕 (fun _ : ZMod 1 => (1 : ℂ)) k‖ ^ 2 = 1 := by
  rw [dft_parseval_norm]; simp

end LeanLab.Routes.R0001
