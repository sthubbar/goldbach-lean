module

public import LeanLab.Perelli1996.Kernel
public import LeanLab.Perelli1996.Totient

/-!
P0083, page 484, equation 17. Both cases of the explicit kernel bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Kernel17
open Real Kernel

noncomputable section

/-- Large moduli use the full period integral and the totient square bound. -/
theorem large_modulus (a M q : ℕ) {P : ℝ} (hq : 0 < q) (hP : 0 < P)
    (hPq : P ≤ q) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) / (q.totient : ℝ) ^ 2 ≤
      4 * (M : ℝ) / P := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφsq : 0 < (q.totient : ℝ) ^ 2 := sq_pos_of_pos hφ
  have hqφ : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by
    exact_mod_cast Totient.le_two_totient_sq q
  apply (div_le_div_iff₀ hφsq hP).2
  have hI := integral_norm_T_sq_le_two_mul a M
  have hI' := mul_le_mul_of_nonneg_right hI hP.le
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hpos := mul_nonneg hM0 (sub_nonneg.mpr (hPq.trans hqφ))
  nlinarith

/-- Small moduli use the tails outside the radius P over N. -/
theorem small_modulus (a M q : ℕ) {P N : ℝ} (hq : 0 < q) (hP : 0 < P)
    (hN : 0 < N) (hradius : P / N ≤ 1 / 2) :
    ((∫ x in (-1 / 2 : ℝ)..(-(P / N)), ‖T a M x‖ ^ 2) +
      (∫ x in (P / N)..(1 / 2 : ℝ), ‖T a M x‖ ^ 2)) / (q.totient : ℝ) ^ 2 ≤
      N / (2 * P) := by
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφsq : (1 : ℝ) ≤ (q.totient : ℝ) ^ 2 := by nlinarith
  have hI := integral_norm_T_sq_two_tails a M (div_pos hP hN) hradius
  have heq : 1 / (2 * (P / N)) = N / (2 * P) := by field_simp
  rw [heq] at hI
  apply (div_le_iff₀ (by nlinarith : 0 < (q.totient : ℝ) ^ 2)).2
  have hpos := mul_nonneg (show 0 ≤ N / (2 * P) by positivity) (sub_nonneg.mpr hφsq)
  nlinarith

/-- A bound for the kernel domain in equation 17, enlarged to two symmetric tails. -/
def kernelMass (a M q : ℕ) (P N : ℝ) : ℝ :=
  if (q : ℝ) ≤ P then
    ((∫ x in (-1 / 2 : ℝ)..(-(P / N)), ‖T a M x‖ ^ 2) +
      (∫ x in (P / N)..(1 / 2 : ℝ), ‖T a M x‖ ^ 2)) / (q.totient : ℝ) ^ 2
  else (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) / (q.totient : ℝ) ^ 2

/-- Equation 17 with P equal L to the B and an explicit constant four c. -/
theorem kernel17 (a M q : ℕ) {P N c : ℝ} (hq : 0 < q) (hP : 0 < P)
    (hN : 0 < N) (hc : 1 ≤ c) (hM : (M : ℝ) ≤ c * N) (hradius : P / N ≤ 1 / 2) :
    kernelMass a M q P N ≤ 4 * c * N / P := by
  unfold kernelMass
  split_ifs with hqP
  · refine (small_modulus a M q hq hP hN hradius).trans ?_
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * P) hP).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg hN.le hP.le)]
  · refine (large_modulus a M q hq hP (le_of_lt (lt_of_not_ge hqP))).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith) hP.le

end
end LeanLab.Perelli1996.Kernel17
