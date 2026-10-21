module

public import LeanLab.PNTPort.Gallagher.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# P0058 Lemma 3, the Parseval identity behind it

Lab proof, unit U-5860, CLOUD 20261020T0014Z-cloud30. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 3, Lemma 3, quoting Lemma 2.3 of their 2012 paper:
`∫_{-1/2}^{1/2} |S̃(α) − 1/z|² dα = (N/2) log N + O(N (log N)^{1/2})`, with
`S̃(α) = ∑ Λ(n) e^{−n/N} e(nα)` and, Lemma 4, `V(α) = ∑_{m ≥ 1} e^{−m/N} e(mα) = 1/z + O(1)`.
The first step of its proof is Parseval for `S̃ − V`; this file proves that step exactly:

* `parseval_tsum`: `∫_{-1/2}^{1/2} ‖∑' c n e(nβ)‖² dβ = ∑' ‖c n‖²` for absolutely summable `c`;
* `St_sub_V`: `S̃(β) − V(β) = ∑' (Λ(n) − [n ≥ 1]) e^{−n/N} e(nβ)`;
* `lemma3_parseval`: `∫_{-1/2}^{1/2} ‖S̃ − V‖² = ∑' (Λ(n) − [n ≥ 1])² e^{−2n/N}`.
The asymptotic `(N/2) log N + O(N)` of the right side needs the prime number theorem and is not
done here; with `LZCesaroShort.lemma4` it would give the paper's Lemma 3 with a better error.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher
open scoped ArithmeticFunction.vonMangoldt

/-- Parseval for an absolutely convergent trigonometric series with frequencies `n ≥ 0`. -/
theorem parseval_tsum (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑' n, c n * e (n * β)‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
  set T := ∑' n, ‖c n‖ with hT
  have hsumm : ∀ β : ℝ, Summable (fun n => c n * e (n * β)) := fun β =>
    Summable.of_norm_bounded hc (fun n => by rw [norm_mul, norm_e, mul_one])
  have hcT : ∀ n, ‖c n‖ ≤ T := fun n => hc.le_tsum n (fun m _ => norm_nonneg _)
  have hsq : Summable (fun n => ‖c n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hc.mul_left T)
    rw [sq]; exact mul_le_mul_of_nonneg_right (hcT n) (norm_nonneg _)
  have hcont : ∀ M : ℕ, Continuous fun β : ℝ => ∑ n ∈ range M, c n * e (n * β) := fun M =>
    continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_e_mul _)
  have hlim : Tendsto (fun M : ℕ => ∫ β in (-(1 / 2 : ℝ))..(1 / 2),
      ‖∑ n ∈ range M, c n * e (n * β)‖ ^ 2) atTop
      (𝓝 (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑' n, c n * e (n * β)‖ ^ 2)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => T ^ 2)
      (Eventually.of_forall fun M => (((hcont M).norm).pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun M => ae_of_all _ fun β _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun β _ => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc ‖∑ n ∈ range M, c n * e (n * β)‖ ≤ ∑ n ∈ range M, ‖c n * e (n * β)‖ := norm_sum_le _ _
        _ = ∑ n ∈ range M, ‖c n‖ := by simp_rw [norm_mul, norm_e, mul_one]
        _ ≤ T := hc.sum_le_tsum _ (fun n _ => norm_nonneg _)
    · exact (((hsumm β).hasSum.tendsto_sum_nat).norm).pow 2
  have heq : (fun M : ℕ => ∫ β in (-(1 / 2 : ℝ))..(1 / 2),
      ‖∑ n ∈ range M, c n * e (n * β)‖ ^ 2) = fun M => ∑ n ∈ range M, ‖c n‖ ^ 2 :=
    funext fun M => parseval c M
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hsq.hasSum.tendsto_sum_nat

/-- The coefficients of `S̃ − V`: `(Λ(n) − [n ≥ 1]) e^{−n/N}`. -/
noncomputable def cLZ (N : ℝ) (n : ℕ) : ℝ := (Λ n - if n = 0 then 0 else 1) * Real.exp (-n / N)

lemma summable_n_exp {N : ℝ} (hN : 0 < N) : Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-n / N)) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity : (0 : ℝ) < 1 / N)
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by positivity : (0 : ℝ) < 1 / N)
  refine (h1.add h0).congr fun n => ?_
  simp only [pow_one, pow_zero, one_mul]
  rw [show -(1 / N) * (n : ℝ) = -n / N by ring]; ring

lemma norm_cLZ_le {N : ℝ} (n : ℕ) : ‖cLZ N n‖ ≤ ((n : ℝ) + 1) * Real.exp (-n / N) := by
  unfold cLZ
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have h1 : Λ n ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_sub_one_of_pos (by exact_mod_cast h)).trans (by linarith))
  rw [abs_le]; constructor <;> split_ifs <;> linarith

lemma summable_cLZ {N : ℝ} (hN : 0 < N) : Summable (fun n => ‖((cLZ N n : ℝ) : ℂ)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (summable_n_exp hN)
  rw [Complex.norm_real]; exact norm_cLZ_le n

/-- `S̃(β) − V(β) = ∑' (Λ(n) − [n ≥ 1]) e^{−n/N} e(nβ)`. -/
theorem St_sub_V {N : ℝ} (hN : 0 < N) (β : ℝ) :
    (∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * e (n * β))
      - (∑' n : ℕ, (((if n = 0 then 0 else 1) * Real.exp (-n / N) : ℝ) : ℂ) * e (n * β))
      = ∑' n : ℕ, ((cLZ N n : ℝ) : ℂ) * e (n * β) := by
  have hb : ∀ n : ℕ, ‖((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * e (n * β)‖
      ≤ ((n : ℝ) + 1) * Real.exp (-n / N) := by
    intro n
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have := ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_sub_one_of_pos (by exact_mod_cast h : (0 : ℝ) < n)))
      linarith
  have hv : ∀ n : ℕ, ‖(((if n = 0 then 0 else 1) * Real.exp (-n / N) : ℝ) : ℂ) * e (n * β)‖
      ≤ ((n : ℝ) + 1) * Real.exp (-n / N) := by
    intro n
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    split_ifs <;> simp <;> positivity
  rw [← (Summable.of_norm_bounded (summable_n_exp hN) hb).tsum_sub
    (Summable.of_norm_bounded (summable_n_exp hN) hv)]
  refine tsum_congr fun n => ?_
  unfold cLZ; push_cast; ring

/-- **The Parseval step of Lemma 3**: `∫_{-1/2}^{1/2} ‖S̃ − V‖² = ∑' (Λ(n) − [n ≥ 1])² e^{−2n/N}`. -/
theorem lemma3_parseval {N : ℝ} (hN : 0 < N) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2),
      ‖(∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * e (n * β))
        - (∑' n : ℕ, (((if n = 0 then 0 else 1) * Real.exp (-n / N) : ℝ) : ℂ) * e (n * β))‖ ^ 2
      = ∑' n : ℕ, (Λ n - if n = 0 then 0 else 1) ^ 2 * Real.exp (-2 * n / N) := by
  simp_rw [St_sub_V hN]
  rw [parseval_tsum _ (summable_cLZ hN)]
  refine tsum_congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold cLZ
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

end LeanLab.LZCesaroShort

