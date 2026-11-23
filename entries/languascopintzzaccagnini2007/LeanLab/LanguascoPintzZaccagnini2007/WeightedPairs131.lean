module

public import LeanLab.LanguascoPintzZaccagnini2007.Convolution131
public import LeanLab.SchnirelmannGoldbach.LoglogUpper

/-!
P0045 page 3, the upper bound used after display 3.
This derivation uses the proved lab Selberg bound and Mathlib Chebyshev.
It follows the prime power separation in the earlier LPZ2007.RgUpperProof.
That module has incompatible declarations and cannot be imported here.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- The full weighted convolution for the bound after display 3. -/
def weightedConvolution131 (n : ℕ) : ℝ := ∑ m ∈ range n, Λ m * Λ (n - m)

/-- The finite weighted prime pair count used in display 3. -/
def weightedPair131 (X n : ℕ) : ℝ :=
  ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X, if m₁ + m₂ = n then Λ m₁ * Λ m₂ else 0

/-- The finite weighted prime pair count is bounded by the full convolution. -/
theorem weightedPair_le_convolution131 (X n : ℕ) : weightedPair131 X n ≤ weightedConvolution131 n := by
  have hg : ∀ m₁ ∈ Icc 1 X, (∑ m₂ ∈ Icc 1 X,
      if m₁ + m₂ = n then Λ m₁ * Λ m₂ else (0 : ℝ)) ≤
        if m₁ < n then Λ m₁ * Λ (n - m₁) else 0 := by
    intro m₁ _
    split_ifs with hlt
    · calc _ ≤ ∑ m₂ ∈ Icc 1 X, if m₂ = n - m₁ then Λ m₁ * Λ (n - m₁) else (0 : ℝ) := by
            apply sum_le_sum
            intro m₂ _
            by_cases h : m₁ + m₂ = n
            · rw [ite_eq_left h, ite_eq_left (by omega), show m₂ = n - m₁ by omega]
            · rw [ite_eq_right h]
              split_ifs
              · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
              · exact le_rfl
        _ ≤ Λ m₁ * Λ (n - m₁) := by
            rw [sum_ite_eq']
            split_ifs
            · exact le_rfl
            · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    · apply le_of_eq
      apply sum_eq_zero
      intro m₂ hm₂
      have := mem_Icc.mp hm₂
      rw [ite_eq_right (by omega)]
  calc weightedPair131 X n ≤ ∑ m₁ ∈ Icc 1 X, (if m₁ < n then Λ m₁ * Λ (n - m₁) else 0) := sum_le_sum hg
    _ = ∑ m₁ ∈ (Icc 1 X).filter (· < n), Λ m₁ * Λ (n - m₁) := (sum_filter _ _).symm
    _ ≤ weightedConvolution131 n :=
      sum_le_sum_of_subset_of_nonneg (fun m hm => by simp only [mem_filter] at hm; simp [hm.2])
        (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)

/-- Lambda is bounded by log n at every m <= n. -/
theorem mangoldt_le_log131 {m n : ℕ} (h : m ≤ n) : Λ m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [ArithmeticFunction.map_zero]
    exact Real.log_natCast_nonneg n
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h))

/-- The nonprime Lambda terms equal psi minus theta. -/
theorem nonprime_mangoldt_sum131 (n : ℕ) :
    ∑ j ∈ range (n + 1), (if ¬ j.Prime then Λ j else 0) = Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter,
    Nat.range_succ_eq_Icc_zero]
  symm
  apply sum_subset (Icc_subset_Icc (by omega) le_rfl)
  intro j hj hj'
  have hj0 : j = 0 := by simp only [mem_Icc] at hj hj'; omega
  subst hj0
  simp

/-- Separate prime pairs from higher prime powers in the upper bound after display 3. -/
theorem convolution_prime_power_split131 (n : ℕ) :
    weightedConvolution131 n ≤ Real.log n ^ 2 * (LeanLab.SchnirelmannGoldbach.r n : ℝ) +
      2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n) := by
  let G : ℕ → ℝ := fun j => if ¬ j.Prime then Λ j else 0
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hG0 : ∀ j, 0 ≤ G j := by
    intro j
    dsimp [G]
    split_ifs <;> positivity
  have hpt : ∀ m ∈ range n, Λ m * Λ (n - m) ≤
      (if m.Prime ∧ (n - m).Prime then Real.log n ^ 2 else 0) +
        Real.log n * G m + Real.log n * G (n - m) := by
    intro m hm
    have h₁ := mangoldt_le_log131 (mem_range.mp hm).le
    have h₂ := mangoldt_le_log131 (Nat.sub_le n m)
    by_cases hp : m.Prime
    · by_cases hq : (n - m).Prime
      · rw [ite_eq_left ⟨hp, hq⟩, sq]
        have := mul_le_mul h₁ h₂ ArithmeticFunction.vonMangoldt_nonneg hlog
        nlinarith [hG0 m, hG0 (n - m)]
      · rw [ite_eq_right (fun h => hq h.2)]
        have he : G (n - m) = Λ (n - m) := by simp only [G]; rw [ite_eq_left hq]
        rw [he]
        nlinarith [mul_le_mul_of_nonneg_right h₁ (ArithmeticFunction.vonMangoldt_nonneg (n := n - m)), hG0 m]
    · rw [ite_eq_right (fun h => hp h.1)]
      have he : G m = Λ m := by simp only [G]; rw [ite_eq_left hp]
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left h₂ (ArithmeticFunction.vonMangoldt_nonneg (n := m)), hG0 (n - m)]
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hpairs : ∑ m ∈ range n, (if m.Prime ∧ (n - m).Prime then Real.log n ^ 2 else 0) =
      Real.log n ^ 2 * (LeanLab.SchnirelmannGoldbach.r n : ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rfl
  have hG1 : ∑ m ∈ range n, G m ≤ Chebyshev.psi n - Chebyshev.theta n := by
    rw [← nonprime_mangoldt_sum131, sum_range_succ]
    have := hG0 n
    dsimp [G] at *
    linarith
  have hG2 : ∑ m ∈ range n, G (n - m) ≤ Chebyshev.psi n - Chebyshev.theta n := by
    have href := sum_range_reflect (fun j => G (j + 1)) n
    have he : ∑ j ∈ range n, G (n - 1 - j + 1) = ∑ m ∈ range n, G (n - m) := by
      apply sum_congr rfl
      intro j hj
      have := mem_range.mp hj
      congr 1
      omega
    rw [he] at href
    rw [href, ← nonprime_mangoldt_sum131, sum_range_succ']
    have h0 : (if ¬ Nat.Prime 0 then Λ 0 else (0 : ℝ)) = 0 := by simp
    rw [h0, add_zero]
  calc weightedConvolution131 n ≤ _ := hsum
    _ ≤ _ := by rw [hpairs]; nlinarith

/-- An explicit absolute constant for the weighted pair bound after display 3. -/
def pairConstant131 : ℝ := LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 + 64

/-- A uniform weighted convolution bound for all n <= N, including higher prime powers. -/
theorem convolution_upper131 {n N : ℕ} (hnN : n ≤ N) (hN : 3 ≤ N) :
    weightedConvolution131 n ≤ pairConstant131 * N * (Real.log (Real.log N) + 2) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN1 : 1 ≤ Real.log N :=
    (Real.le_log_iff_exp_le hN0).mpr (Real.exp_one_lt_three.le.trans hN3)
  have hlogN : 0 < Real.log N := by linarith
  have hLL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlogN1
  have hC : 0 < LeanLab.SchnirelmannExplicit.C1 := by norm_num [LeanLab.SchnirelmannExplicit.C1]
  have hK : 0 ≤ pairConstant131 := by unfold pairConstant131; positivity
  by_cases hn : n ≤ 2
  · have hz : weightedConvolution131 n = 0 := by
      interval_cases n <;> norm_num [weightedConvolution131, sum_range_succ]
    rw [hz]
    positivity
  have hn3 : 3 ≤ n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogn1 : 1 ≤ Real.log n :=
    (Real.le_log_iff_exp_le hn0).mpr (Real.exp_one_lt_three.le.trans hnR)
  have hlln : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlogn1
  have hlognN : Real.log n ≤ Real.log N := Real.log_le_log hn0 hnN'
  have hll : Real.log (Real.log n) ≤ Real.log (Real.log N) := Real.log_le_log hlogn hlognN
  have hpart1 : Real.log n ^ 2 * (LeanLab.SchnirelmannGoldbach.r n : ℝ) ≤
      LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * N * (Real.log (Real.log N) + 2) := by
    calc Real.log n ^ 2 * (LeanLab.SchnirelmannGoldbach.r n : ℝ)
        ≤ Real.log n ^ 2 * (LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * n /
            Real.log n ^ 2 * (Real.log (Real.log n) + 2)) :=
          mul_le_mul_of_nonneg_left (LeanLab.SchnirelmannGoldbach.r_le_loglog n hn3) (sq_nonneg _)
      _ = LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * n * (Real.log (Real.log n) + 2) := by
          field_simp
      _ ≤ _ := by gcongr
  have hpt := Chebyshev.psi_sub_theta_le (x := (n : ℝ)) (by linarith : (1 : ℝ) ≤ n)
  have hlog4 : Real.log N ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div hN0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hq : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hsqrtN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hpt' : Chebyshev.psi n - Chebyshev.theta n ≤ 2 * Real.sqrt N * Real.log N := by
    calc _ ≤ 2 * Real.sqrt n * Real.log n := hpt
      _ ≤ _ := by gcongr
  have hl2 : Real.log N ^ 2 ≤ 16 * Real.sqrt N := by
    calc Real.log N ^ 2 ≤ (4 * (N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 :=
          pow_le_pow_left₀ hlogN.le hlog4 2
      _ = 16 * Real.sqrt N := by rw [mul_pow, hq]; norm_num
  have htheta : 0 ≤ Chebyshev.psi n - Chebyshev.theta n := sub_nonneg.mpr (Chebyshev.theta_le_psi (n : ℝ))
  have hpart2 : 2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n) ≤ 64 * N := by
    calc 2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n)
        ≤ 2 * Real.log N * (2 * Real.sqrt N * Real.log N) := by gcongr
      _ = 4 * Real.sqrt N * Real.log N ^ 2 := by ring
      _ ≤ 4 * Real.sqrt N * (16 * Real.sqrt N) := by gcongr
      _ = 64 * N := by nlinarith [hsqrtN]
  have ht := convolution_prime_power_split131 n
  unfold pairConstant131
  nlinarith

/-- The weighted Goldbach upper bound needed after display 3, uniform for n <= N. -/
theorem weightedPair_upper131 (X : ℕ) {n N : ℕ} (hn : n ≤ N) (hN : 3 ≤ N) :
    weightedPair131 X n ≤ pairConstant131 * N * (Real.log (Real.log N) + 2) :=
  (weightedPair_le_convolution131 X n).trans (convolution_upper131 hn hN)

end

end LeanLab.LPZ2007
