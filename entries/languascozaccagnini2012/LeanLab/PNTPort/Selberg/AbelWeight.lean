module

public import Mathlib

/-!
# Decreasing weights in mean square, by Abel summation and Cauchy-Schwarz

Lab proof, unit U-6003, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058 Lemma 1.
AI wrote this file. Elementary, no cited input.

With `A_k = Σ_{i<k} a_i`, nonnegative antitone weights `w` and `c_n = w_n - w_{n+1}`:

* `abel_eq`: `Σ_{n<M} w_n a_n = Σ_{n<M} c_n A_{n+1} + w_M A_M`;
* `cs_weighted`: `‖Σ c_i v_i‖² ≤ (Σ c_i) Σ c_i ‖v_i‖²` for `c ≥ 0`;
* `abel_cs`: `‖Σ_{n<M} w_n a_n‖² ≤ w_0 (Σ_{n<M} c_n ‖A_{n+1}‖² + w_M ‖A_M‖²)`;
* `abel_cs_integral`: the same after integrating over `[-ξ, ξ]`, for continuous `a_n(β)`.

Use: `a_n(β) = (Λ(n) - 1) e(nβ)` and `w_n = e^{-n/N}` move `gallagher_selberg` from the sharp
sum `Σ_{n<k}` to the exponentially weighted sum `S̃` of P0058, as a weighted average of the
sharp mean squares with total weight `w_0 = 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset MeasureTheory

/-- **Abel summation.** -/
lemma abel_eq (a : ℕ → ℂ) (w : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ range M, (w n : ℂ) * a n =
      (∑ n ∈ range M, ((w n - w (n + 1) : ℝ) : ℂ) * ∑ i ∈ range (n + 1), a i) +
        (w M : ℂ) * ∑ i ∈ range M, a i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun n => ((w n - w (n + 1) : ℝ) : ℂ) * _),
      sum_range_succ a M]
    push_cast; ring

/-- **Weighted Cauchy-Schwarz.** -/
lemma cs_weighted (s : Finset ℕ) (c : ℕ → ℝ) (v : ℕ → ℂ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    ‖∑ i ∈ s, (c i : ℂ) * v i‖ ^ 2 ≤ (∑ i ∈ s, c i) * ∑ i ∈ s, c i * ‖v i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (c i : ℂ) * v i‖ ≤ ∑ i ∈ s, c i * ‖v i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun i hi => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc i hi)]
  have h2 : (∑ i ∈ s, c i * ‖v i‖) ^ 2 ≤ (∑ i ∈ s, c i) * ∑ i ∈ s, c i * ‖v i‖ ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (c i))
      (fun i => Real.sqrt (c i) * ‖v i‖)
    have e1 : ∀ i ∈ s, Real.sqrt (c i) * (Real.sqrt (c i) * ‖v i‖) = c i * ‖v i‖ := by
      intro i hi; rw [← mul_assoc, Real.mul_self_sqrt (hc i hi)]
    have e2 : ∀ i ∈ s, Real.sqrt (c i) ^ 2 = c i := fun i hi => Real.sq_sqrt (hc i hi)
    have e3 : ∀ i ∈ s, (Real.sqrt (c i) * ‖v i‖) ^ 2 = c i * ‖v i‖ ^ 2 := by
      intro i hi; rw [mul_pow, Real.sq_sqrt (hc i hi)]
    rwa [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at this
  have h0 : 0 ≤ ‖∑ i ∈ s, (c i : ℂ) * v i‖ := norm_nonneg _
  exact (pow_le_pow_left₀ h0 h1 2).trans h2

/-- **Abel plus Cauchy-Schwarz.** -/
lemma abel_cs (a : ℕ → ℂ) (w : ℕ → ℝ) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) (M : ℕ) :
    ‖∑ n ∈ range M, (w n : ℂ) * a n‖ ^ 2 ≤
      w 0 * ((∑ n ∈ range M, (w n - w (n + 1)) * ‖∑ i ∈ range (n + 1), a i‖ ^ 2) +
        w M * ‖∑ i ∈ range M, a i‖ ^ 2) := by
  rw [abel_eq]
  -- one sum over `range (M + 1)`
  set c : ℕ → ℝ := fun n => if n < M then w n - w (n + 1) else w M with hc
  set v : ℕ → ℂ := fun n => if n < M then ∑ i ∈ range (n + 1), a i else ∑ i ∈ range M, a i
    with hv
  have hc0 : ∀ i ∈ range (M + 1), 0 ≤ c i := by
    intro i _; simp only [hc]; split_ifs
    · linarith [hw (Nat.le_succ i)]
    · exact hw0 M
  have hsplit : ∀ f : ℕ → ℂ, ∑ n ∈ range (M + 1), f n = ∑ n ∈ range M, f n + f M :=
    fun f => sum_range_succ f M
  have hsplitR : ∀ f : ℕ → ℝ, ∑ n ∈ range (M + 1), f n = ∑ n ∈ range M, f n + f M :=
    fun f => sum_range_succ f M
  have hcs := cs_weighted (range (M + 1)) c v hc0
  rw [hsplit, hsplitR, hsplitR] at hcs
  have ec : ∀ n ∈ range M, c n = w n - w (n + 1) := fun n hn => by
    simp only [hc, if_pos (mem_range.mp hn)]
  have ev : ∀ n ∈ range M, v n = ∑ i ∈ range (n + 1), a i := fun n hn => by
    simp only [hv, if_pos (mem_range.mp hn)]
  have cM : c M = w M := by simp [hc]
  have vM : v M = ∑ i ∈ range M, a i := by simp [hv]
  have e1 : ∑ n ∈ range M, (c n : ℂ) * v n =
      ∑ n ∈ range M, ((w n - w (n + 1) : ℝ) : ℂ) * ∑ i ∈ range (n + 1), a i :=
    sum_congr rfl fun n hn => by rw [ec n hn, ev n hn]
  have e2 : ∑ n ∈ range M, c n * ‖v n‖ ^ 2 =
      ∑ n ∈ range M, (w n - w (n + 1)) * ‖∑ i ∈ range (n + 1), a i‖ ^ 2 :=
    sum_congr rfl fun n hn => by rw [ec n hn, ev n hn]
  have e3 : ∑ n ∈ range M, c n = ∑ n ∈ range M, (w n - w (n + 1)) := sum_congr rfl ec
  rw [e1, e2, e3, cM, vM] at hcs
  have htel : ∑ n ∈ range M, (w n - w (n + 1)) + w M = w 0 := by
    rw [sum_range_sub']; ring
  rw [htel] at hcs
  exact hcs

/-- **Abel plus Cauchy-Schwarz in mean square.** -/
lemma abel_cs_integral (a : ℕ → ℝ → ℂ) (ha : ∀ n, Continuous (a n)) (w : ℕ → ℝ)
    (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) (M : ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ∫ β in (-ξ)..ξ, ‖∑ n ∈ range M, (w n : ℂ) * a n β‖ ^ 2 ≤
      w 0 * ((∑ n ∈ range M, (w n - w (n + 1)) *
          ∫ β in (-ξ)..ξ, ‖∑ i ∈ range (n + 1), a i β‖ ^ 2) +
        w M * ∫ β in (-ξ)..ξ, ‖∑ i ∈ range M, a i β‖ ^ 2) := by
  have hcont : ∀ k, Continuous (fun β => ‖∑ i ∈ range k, a i β‖ ^ 2) := fun k =>
    (continuous_finsetSum _ fun i _ => ha i).norm.pow 2
  have hii : ∀ k, IntervalIntegrable (fun β => ‖∑ i ∈ range k, a i β‖ ^ 2) volume (-ξ) ξ :=
    fun k => (hcont k).intervalIntegrable _ _
  have hle : -ξ ≤ ξ := by linarith
  have hL : IntervalIntegrable (fun β => ‖∑ n ∈ range M, (w n : ℂ) * a n β‖ ^ 2) volume (-ξ) ξ :=
    ((continuous_finsetSum _ fun n _ => continuous_const.mul (ha n)).norm.pow 2).intervalIntegrable _ _
  have hR : IntervalIntegrable (fun β => w 0 * ((∑ n ∈ range M, (w n - w (n + 1)) *
      ‖∑ i ∈ range (n + 1), a i β‖ ^ 2) + w M * ‖∑ i ∈ range M, a i β‖ ^ 2)) volume (-ξ) ξ := by
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_const.mul ((continuous_finsetSum _ fun n _ =>
      continuous_const.mul (hcont (n + 1))).add (continuous_const.mul (hcont M)))
  calc ∫ β in (-ξ)..ξ, ‖∑ n ∈ range M, (w n : ℂ) * a n β‖ ^ 2
      ≤ ∫ β in (-ξ)..ξ, w 0 * ((∑ n ∈ range M, (w n - w (n + 1)) *
          ‖∑ i ∈ range (n + 1), a i β‖ ^ 2) + w M * ‖∑ i ∈ range M, a i β‖ ^ 2) :=
        intervalIntegral.integral_mono_on hle hL hR fun β _ => abel_cs (fun n => a n β) w hw hw0 M
    _ = _ := by
        have hS : IntervalIntegrable (fun β => ∑ n ∈ range M, (w n - w (n + 1)) *
            ‖∑ i ∈ range (n + 1), a i β‖ ^ 2) volume (-ξ) ξ :=
          (continuous_finsetSum _ fun n _ => continuous_const.mul (hcont (n + 1))).intervalIntegrable _ _
        have hT : IntervalIntegrable (fun β => w M * ‖∑ i ∈ range M, a i β‖ ^ 2) volume (-ξ) ξ :=
          (hii M).const_mul _
        have hsum : ∫ β in (-ξ)..ξ, ∑ n ∈ range M, (w n - w (n + 1)) *
            ‖∑ i ∈ range (n + 1), a i β‖ ^ 2 = ∑ n ∈ range M, ∫ β in (-ξ)..ξ, (w n - w (n + 1)) *
            ‖∑ i ∈ range (n + 1), a i β‖ ^ 2 :=
          intervalIntegral.integral_finsetSum fun n _ => (hii (n + 1)).const_mul _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hS hT, hsum,
          intervalIntegral.integral_const_mul]
        congr 1
        rw [sum_congr rfl fun n _ => intervalIntegral.integral_const_mul _ _]

end LeanLab.PNTPort.Selberg

