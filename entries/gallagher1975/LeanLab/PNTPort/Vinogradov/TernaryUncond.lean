module

public import LeanLab.PNTPort.Vinogradov.TernaryAssembly
public import LeanLab.PNTPort.Vinogradov.MajorArcUncond

/-!
# Vinogradov's ternary estimate, explicit and unconditional

Lab proof, unit U-5254. AI wrote this file. Known mathematics, no cited input: the major arc
input is `major_arc`, from the lab's unconditional, ineffective Siegel-Walfisz theorem.

`ternary_uncond`: for every `A > 0` there are `c > 0`, `K ≥ 0` such that for `N ≥ e⁴`,
`3N < M`, `n < M`, `1 ≤ P ≤ (log N)^A`, `1 ≤ Q ≤ N` with `2/(Q + 1) < 1/P²`,
`‖r₃(n) - J(n) 𝔖_P(n)‖ ≤ B ∑Λ² + P² (2/(Q + 1) + 1/M) 3R² E (1 + 2πN/(Q + 1)) + N P² (Q + 1)/2`
with `E = 7√N + P K N e^{-c√(log N/2)} + (log P/log 2) log N`. Ternary Goldbach is
Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open scoped ArithmeticFunction.Moebius

theorem ternary_uncond (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ {N M P Q n : ℕ} [NeZero M], Real.exp 4 ≤ N →
      3 * N < M → n < M → 1 ≤ P → (P : ℝ) ≤ Real.log N ^ A → 1 ≤ Q → Q ≤ N →
      2 / ((Q : ℝ) + 1) < 1 / (P : ℝ) ^ 2 →
      ‖(r3 N n : ℂ) - (J N n : ℂ) * singP P n‖ ≤
        300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
            (1 + Real.log N) ^ 4 * ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2
          + (P : ℝ) ^ 2 * (2 / ((Q : ℝ) + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * N) ^ 2 *
            ((7 * Real.sqrt N + P * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) +
              Real.log P / Real.log 2 * Real.log N) * (1 + 2 * π * N / (Q + 1))))
          + N * (P : ℝ) ^ 2 * (Q + 1) / 2 := by
  obtain ⟨c, hc, K, hK, hmaj⟩ := major_arc A hA
  refine ⟨c, hc, K, hK, ?_⟩
  intro N M P Q n _ hN h3 hn hP hPA hQ hQN hPQ
  have hlogN : 4 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 4) hN; rwa [Real.log_exp] at this
  apply ternary_explicit h3 hn hP hQ hQN hPQ (by
    have : 0 ≤ Real.log P / Real.log 2 * Real.log N :=
      mul_nonneg (div_nonneg (Real.log_natCast_nonneg P) (Real.log_nonneg (by norm_num)))
        (by linarith)
    positivity)
  intro q hq a' hcop β
  rw [mem_Icc] at hq
  have hqP : (q : ℝ) ≤ P := by exact_mod_cast hq.2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.1
  refine (hmaj N hN q hq.1 (hqP.trans hPA) a' hcop β).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h1 : (q : ℝ) * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) ≤
      P * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by
    have : 0 ≤ K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by positivity
    nlinarith
  have h2 : Real.log q / Real.log 2 * Real.log N ≤ Real.log P / Real.log 2 * Real.log N := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hqP)
      (Real.log_nonneg (by norm_num))
  linarith

end LeanLab.PNTPort.Vinogradov

