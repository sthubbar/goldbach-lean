module

public import LeanLab.Perelli1996.Section3
public import LeanLab.Perelli1996.B.Sing

/-!
P0083, page 488, equation 36. An explicit arithmetic factor bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Section3
open Finset Real

/-- An elementary finite product estimate behind equation 36. -/
theorem product_p_sub_two (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p) :
    (∏ p ∈ s, (p : ℝ)) * (∏ p ∈ s, 1 / ((p : ℝ) - 2)) ≤
      8 * (∏ p ∈ s, (1 + 1 / (p : ℝ))) ^ 2 := by
  have hC := B.prod_ge_half s hs
  have himg : ∀ p ∈ s.image (fun p => p + 1), 3 ≤ p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := hs q hq
    omega
  have hD' := B.prod_ge_half (s.image (fun p => p + 1)) himg
  have hD : (1 : ℝ) / 2 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [Finset.prod_image (by intro a ha b hb h; dsimp at h; omega)] at hD'
    simpa using hD'
  have hid :
      (∏ p ∈ s, (p : ℝ)) * (∏ p ∈ s, 1 / ((p : ℝ) - 2)) *
      (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
      (∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)) ^ 2 =
      (∏ p ∈ s, (1 + 1 / (p : ℝ))) ^ 2 := by
    calc _ = ∏ p ∈ s, (p : ℝ) * (1 / ((p : ℝ) - 2)) *
          (1 - 1 / ((p : ℝ) - 1) ^ 2) * (1 - 1 / (p : ℝ) ^ 2) ^ 2 := by
            simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      _ = ∏ p ∈ s, (1 + 1 / (p : ℝ)) ^ 2 := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hs p hp
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
        field_simp
        ring
      _ = _ := by rw [Finset.prod_pow]
  have hD2 : (1 : ℝ) / 4 ≤ (∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)) ^ 2 := by nlinarith
  have hCD := mul_le_mul hC hD2 (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith)
  have hAB : 0 ≤ (∏ p ∈ s, (p : ℝ)) * (∏ p ∈ s, 1 / ((p : ℝ) - 2)) := by
    apply mul_nonneg (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _))
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hs p hp
    exact div_nonneg (by norm_num) (by linarith)
  have hle := mul_le_mul_of_nonneg_left hCD hAB
  nlinarith [hid]

/-- Explicit form of f n bounded by log squared n over n, equation 36. -/
theorem arithmeticFactor_le (n : ℕ) (hn : 1 ≤ n) :
    arithmeticFactor n ≤ 8 * (1 + Real.log n) ^ 2 / n := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  by_cases hn1 : n = 1
  · subst n; norm_num [arithmeticFactor]
  by_cases hneven : 2 ∣ n
  · rw [arithmeticFactor_even hneven]; positivity
  by_cases hnsq : Squarefree n
  · have hs : ∀ p ∈ n.primeFactors, 3 ≤ p := by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      have hp2 := hprime.two_le
      have hpne : p ≠ 2 := by intro h; subst p; exact hneven hdvd
      omega
    have hmu : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hnsq
    have hf : arithmeticFactor n = ∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) := by
      simp [arithmeticFactor, hn1, hneven, hmu]
    have hprod : (∏ p ∈ n.primeFactors, (p : ℝ)) = n := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hnsq]
    have hb := product_p_sub_two n.primeFactors hs
    rw [hprod, ← hf] at hb
    let invAF : ArithmeticFunction ℝ := ⟨fun k => (k : ℝ)⁻¹, by simp⟩
    have hi : invAF.IsMultiplicative := by
      refine ⟨by simp [invAF], fun {m k} _ => ?_⟩
      change ((m * k : ℕ) : ℝ)⁻¹ = (m : ℝ)⁻¹ * (k : ℝ)⁻¹
      simp [mul_inv_rev, mul_comm]
    have hEeq : (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) =
        ∑ d ∈ n.divisors, (d : ℝ)⁻¹ := by
      simpa [invAF, one_div] using hi.prodPrimeFactors_one_add_of_squarefree hnsq
    have hdiv : ∑ d ∈ n.divisors, (d : ℝ)⁻¹ ≤ ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
          Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)⟩
      · intro d _ _; positivity
    have hH : (∑ d ∈ Icc 1 n, (d : ℝ)⁻¹) = (harmonic n : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hE : (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) ≤ 1 + Real.log n := by
      rw [hEeq]
      exact hdiv.trans (hH ▸ harmonic_le_one_add_log n)
    have hE0 : 0 ≤ ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by positivity
    have hEsq := pow_le_pow_left₀ hE0 hE 2
    apply (le_div_iff₀ hnR).2
    nlinarith
  · rw [arithmeticFactor_nonsquarefree hnsq]; positivity

/-- Equation 36 with the explicit constant thirty two for n at least four. -/
theorem arithmeticFactor_le_log_sq (n : ℕ) (hn : 4 ≤ n) :
    arithmeticFactor n ≤ 32 * Real.log n ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnR]
    have hexp := Real.exp_one_lt_d9
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine (arithmeticFactor_le n (by omega)).trans ?_
  apply div_le_div_of_nonneg_right _ hnR.le
  nlinarith

end LeanLab.Perelli1996.Section3
