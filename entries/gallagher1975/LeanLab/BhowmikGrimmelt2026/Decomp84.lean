module

public import Mathlib
public import LeanLab.PNTPort.Vinogradov.Final

/-!
Proposition 4.1, page 16 display 4.8, with elementary denominator ranges separated.
Page 17 explicitly omits the proof of 4.8. The central range is supplied by the lab proof
of Vaughan, The Hardy-Littlewood method, second edition 1997, reference 23.
This is a dependency decomposition, not a claim that the survey supplies a bilinear proof.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `S(α) = Σ_{n ≤ N} Λ(n) e(αn)`, p. 14. -/
noncomputable def Ssum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℂ) * ee (α * n)

/-- Proposition 4.1, Vinogradov-Vaughan, (4.8), p. 16: if `|α − a/q| < q^{-2}`, `(a,q) = 1`,
then `S(α) ≪ (N q^{-1/2} + N^{4/5} + (Nq)^{1/2}) (log N)^4`. -/
def Prop41 : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
    |α - a / q| < 1 / (q : ℝ) ^ 2 →
    ‖Ssum N α‖ ≤ C * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
      Real.log N ^ 4


/-- LEAF. Page 14 definition of S and page 16 display 4.8. Match additive exponentials. -/
theorem ee_eq_library84 (x : ℝ) : ee x = LeanLab.PNTPort.LargeSieve.e x := by
  unfold ee LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- LEAF. Page 16 display 4.8. The elementary triangle bound for the prime sum. -/
theorem ssum_triangle84 (N : ℕ) (α : ℝ) :
    ‖Ssum N α‖ ≤ ∑ n ∈ Finset.Icc 1 N, vonMangoldt n := by
  unfold Ssum
  apply norm_sum_le_of_le
  intro n hn
  simp [norm_mul, ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

/-- LEAF. Page 14 definition of S and page 16 display 4.8. Match the two prime sums. -/
theorem ssum_eq_library84 (N : ℕ) (α : ℝ) :
    Ssum N α = LeanLab.PNTPort.Vinogradov.S N α := by
  unfold Ssum LeanLab.PNTPort.Vinogradov.S
  simp only [ee_eq_library84, mul_comm α]

/-- LEAF. Page 16 display 4.8. A uniform elementary bound valid at every frequency. -/
theorem ssum_log_bound84 (N : ℕ) (α : ℝ) :
    ‖Ssum N α‖ ≤ N * Real.log N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, vonMangoldt n := ssum_triangle84 N α
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      exact vonMangoldt_le_log.trans (Real.log_le_log
        (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnN))
    _ = N * Real.log N := by simp [Nat.card_Icc]

/-- LEAF. Page 16 display 4.8. Convert the library logarithm to the paper logarithm. -/
theorem log_four_compare84 {N : ℕ} (hN : 2 ≤ N) :
    (1 + Real.log N) ^ 4 ≤ 81 * Real.log N ^ 4 := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log N := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ N by exact_mod_cast hN)
    linarith [Real.log_two_gt_d9]
  calc
    _ ≤ (3 * Real.log N) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    _ = _ := by ring

/-- LEAF. Page 16 display 4.8. Vaughan's bound when the denominator is at most N.
Source: Vaughan reference 23, Theorem 3.1, proved in PNTPort.Vinogradov.Final. -/
theorem vaughan_small_denominator84 {N q : ℕ} (hN : 2 ≤ N) (hq : 1 ≤ q)
    {a : ℤ} (hcop : Int.gcd a q = 1) {α : ℝ}
    (hα : |α - a / q| < 1 / (q : ℝ) ^ 2) (hqN : q ≤ N) :
    ‖Ssum N α‖ ≤ 24300 * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) +
      Real.sqrt (N * q)) * Real.log N ^ 4 := by
  rw [ssum_eq_library84]
  have h := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop) hα.le hqN
  calc
    _ ≤ 300 * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) +
        Real.sqrt (N * q)) * (1 + Real.log N) ^ 4 := h
    _ ≤ 300 * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) +
        Real.sqrt (N * q)) * (81 * Real.log N ^ 4) :=
      mul_le_mul_of_nonneg_left (log_four_compare84 hN) (by positivity)
    _ = _ := by ring

/-- LEAF. Page 16 display 4.8. The triangle bound suffices for denominators at least N. -/
theorem vaughan_large_denominator84 {N q : ℕ} (hN : 2 ≤ N) (hqN : N ≤ q) (α : ℝ) :
    ‖Ssum N α‖ ≤ 24300 * (N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) +
      Real.sqrt (N * q)) * Real.log N ^ 4 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast hqN
  have hhalf : (1 / 2 : ℝ) ≤ Real.log N := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ N by exact_mod_cast hN)
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log N ≤ 8 * Real.log N ^ 4 := by
    have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 3
    have hp := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ Real.log N)
    norm_num at hp
    nlinarith only [hp]
  let B : ℝ := N / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt (N * q)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : (N : ℝ) ≤ Real.sqrt (N * q) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [mul_le_mul_of_nonneg_left hNq hN0])
  have hNB : (N : ℝ) ≤ B := by
    have h1 : 0 ≤ (N : ℝ) / Real.sqrt q := by positivity
    have h2 : 0 ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by positivity
    dsimp [B]
    linarith
  change ‖Ssum N α‖ ≤ 24300 * B * Real.log N ^ 4
  calc
    _ ≤ N * Real.log N := ssum_log_bound84 N α
    _ ≤ N * (8 * Real.log N ^ 4) := mul_le_mul_of_nonneg_left hlog hN0
    _ = 8 * N * Real.log N ^ 4 := by ring
    _ ≤ 8 * B * Real.log N ^ 4 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNB (by norm_num)) (by positivity)
    _ ≤ 24300 * B * Real.log N ^ 4 := by gcongr; norm_num

/-- Proposition 4.1 assembled with its exact existing proposition type. -/
theorem prop41_decomposed84 : Prop41 := by
  refine ⟨24300, fun N hN α a q hq hcop hα => ?_⟩
  rcases le_total q N with hqN | hNq
  · exact vaughan_small_denominator84 hN hq hcop hα hqN
  · exact vaughan_large_denominator84 hN hNq α

/-- Proposition 4.1 with its sealed statement and a completed proof. -/
theorem prop41 : Prop41 := prop41_decomposed84

end LeanLab.BhowmikGrimmelt2026


