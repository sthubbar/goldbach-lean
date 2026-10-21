module

public import LeanLab.PNTPort.Gallagher.Psi

/-!
# Gallagher's lemma for `Λ - 1` with exact edge windows

Lab proof, unit U-6200, CLOUD 20261020T0817Z-cloud38, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file. Known mathematics, no cited input.

`gallagher_psi` of `Gallagher/Psi.lean` bounds each of the `2L` edge windows by `L (log N + 1)`,
which costs `L log² N` after division by `L²`. Here the edge windows are kept exact, as values of
the partial sums `Gp(j) = ∑_{n ≤ j} (Λ(n) - 1) = ψ(j) - j - 1`, so that Cramér's mean square can
bound them on average later.

* `Gp_eq`: `Gp j = ψ(j) - j - 1`;
* `win_eq`: every window is `Gp(min m (k - 1)) - [L ≤ m] Gp(m - L)`;
* `gallagher_psi_edge`: for `k, L ≥ 1`,
  `∫_{|β| ≤ 1/(2L)} ‖∑_{n<k} (Λ(n) - 1) e(nβ)‖² ≤ (π/(2L))² (∑_{L ≤ m < k} (ψ(m) - ψ(m - L) - L)²
     + 2 ∑_{m<L} ‖Gp m‖² + 4 L ‖Gp(k - 1)‖² + 2 ∑_{i<L} ‖Gp(k + i - L)‖²)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset Real MeasureTheory
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- `Gp(j) = ∑_{n ≤ j} (Λ(n) - 1)`. -/
noncomputable def Gp (j : ℕ) : ℂ := ∑ n ∈ range (j + 1), lam1 n

lemma win_eq_hi {k L m : ℕ} (hk : 1 ≤ k) (hm : m < k + L) (hLm : L ≤ m) :
    win lam1 k L m = Gp (min m (k - 1)) - Gp (m - L) := by
  have hsub : range (m - L + 1) ⊆ range (min m (k - 1) + 1) := by
    intro n hn; simp only [mem_range] at hn ⊢; omega
  have hset : (range k).filter (fun n => n ≤ m ∧ m < n + L) =
      range (min m (k - 1) + 1) \ range (m - L + 1) := by
    ext n; simp only [mem_filter, mem_range, mem_sdiff]; omega
  unfold win Gp
  rw [hset, sum_sdiff_eq_sub hsub]

lemma win_eq_lo {k L m : ℕ} (hk : 1 ≤ k) (hLm : m < L) :
    win lam1 k L m = Gp (min m (k - 1)) := by
  have hset : (range k).filter (fun n => n ≤ m ∧ m < n + L) = range (min m (k - 1) + 1) := by
    ext n; simp only [mem_filter, mem_range]; omega
  unfold win Gp
  rw [hset]

lemma norm_win_sq_le {k L m : ℕ} (hk : 1 ≤ k) (hm : m < k + L) :
    ‖win lam1 k L m‖ ^ 2 ≤ 2 * ‖Gp (min m (k - 1))‖ ^ 2 + 2 * ‖Gp (m - L)‖ ^ 2 := by
  rcases le_or_gt L m with h | h
  · rw [win_eq_hi hk hm h]
    have := norm_sub_le (Gp (min m (k - 1))) (Gp (m - L))
    nlinarith [norm_nonneg (Gp (min m (k - 1))), norm_nonneg (Gp (m - L)),
      sq_nonneg (‖Gp (min m (k - 1))‖ - ‖Gp (m - L)‖), norm_nonneg (Gp (min m (k - 1)) - Gp (m - L))]
  · rw [win_eq_lo hk h]
    nlinarith [sq_nonneg ‖Gp (min m (k - 1))‖, sq_nonneg ‖Gp (m - L)‖]

lemma norm_Gp_zero : ‖Gp 0‖ = 1 := by
  simp [Gp, lam1]

lemma sum_union_le_of_nonneg {s t : Finset ℕ} (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s ∪ t, f i ≤ ∑ i ∈ s, f i + ∑ i ∈ t, f i := by
  rw [← sum_union_inter]
  have : 0 ≤ ∑ i ∈ s ∩ t, f i := sum_nonneg fun i _ => hf i
  linarith

/-- **Gallagher's lemma for `Λ - 1` with exact edges.** -/
theorem gallagher_psi_edge (k L : ℕ) (hL : 0 < L) (hk : 1 ≤ k) :
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range k, lam1 n * e (n * β)‖ ^ 2
      ≤ (π / (2 * L)) ^ 2 * (∑ m ∈ Ico L k, (ψ (m : ℝ) - ψ ((m - L : ℕ) : ℝ) - L) ^ 2
          + (2 * ∑ m ∈ range L, ‖Gp m‖ ^ 2 + 2 * L + 4 * L * ‖Gp (k - 1)‖ ^ 2
            + 2 * ∑ i ∈ range L, ‖Gp (k + i - L)‖ ^ 2)) := by
  refine (gallagher lam1 k L hL).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hsub : Ico L k ⊆ range (k + L) := by
    intro m hm; simp only [mem_Ico, mem_range] at hm ⊢; omega
  rw [← sum_sdiff hsub, add_comm]
  apply add_le_add
  · refine le_of_eq (sum_congr rfl fun m hm => ?_)
    rw [mem_Ico] at hm
    rw [win_interior hm.1 hm.2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · set f : ℕ → ℝ := fun m => 2 * ‖Gp (min m (k - 1))‖ ^ 2 + 2 * ‖Gp (m - L)‖ ^ 2 with hf
    have hf0 : ∀ m, 0 ≤ f m := fun m => by simp only [hf]; positivity
    have h1 : ∑ m ∈ range (k + L) \ Ico L k, ‖win lam1 k L m‖ ^ 2 ≤
        ∑ m ∈ range (k + L) \ Ico L k, f m := by
      refine sum_le_sum fun m hm => ?_
      simp only [mem_sdiff, mem_range] at hm
      exact norm_win_sq_le hk hm.1
    have hsub2 : range (k + L) \ Ico L k ⊆ range L ∪ Ico k (k + L) := by
      intro m hm; simp only [mem_sdiff, mem_range, mem_Ico, mem_union] at hm ⊢; omega
    have h2 := sum_le_sum_of_subset_of_nonneg hsub2 (fun m _ _ => hf0 m)
    have h3 := sum_union_le_of_nonneg (s := range L) (t := Ico k (k + L)) f hf0
    have h4 : ∑ m ∈ range L, f m ≤ 2 * ∑ m ∈ range L, ‖Gp m‖ ^ 2 + 2 * L
        + 2 * L * ‖Gp (k - 1)‖ ^ 2 := by
      have : ∀ m ∈ range L, f m ≤ 2 * ‖Gp m‖ ^ 2 + 2 * ‖Gp (k - 1)‖ ^ 2 + 2 := by
        intro m hm
        have hmL : m - L = 0 := by have := mem_range.mp hm; omega
        simp only [hf, hmL, norm_Gp_zero]
        rcases le_total m (k - 1) with h | h
        · rw [min_eq_left h]; nlinarith [sq_nonneg ‖Gp (k - 1)‖]
        · rw [min_eq_right h]; nlinarith [sq_nonneg ‖Gp m‖]
      refine (sum_le_sum this).trans (le_of_eq ?_)
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, sum_const, card_range,
        nsmul_eq_mul, nsmul_eq_mul]
      ring
    have h5 : ∑ m ∈ Ico k (k + L), f m = 2 * L * ‖Gp (k - 1)‖ ^ 2
        + 2 * ∑ i ∈ range L, ‖Gp (k + i - L)‖ ^ 2 := by
      rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      have : ∀ i ∈ range L, f (k + i) = 2 * ‖Gp (k - 1)‖ ^ 2 + 2 * ‖Gp (k + i - L)‖ ^ 2 := by
        intro i _
        simp only [hf]
        rw [min_eq_right (by omega)]
      rw [sum_congr rfl this, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
      ring
    linarith

lemma sum_range_succ_vonMangoldt (j : ℕ) : ∑ n ∈ range (j + 1), Λ n = ψ (j : ℝ) := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), ArithmeticFunction.map_zero, zero_add]
  rfl

lemma Gp_eq (j : ℕ) : Gp j = ((ψ (j : ℝ) - j - 1 : ℝ) : ℂ) := by
  unfold Gp lam1
  rw [← Complex.ofReal_sum, sum_sub_distrib, sum_range_succ_vonMangoldt]
  simp; ring

lemma norm_Gp_sq_le (j : ℕ) : ‖Gp j‖ ^ 2 ≤ 2 * (ψ (j : ℝ) - j) ^ 2 + 2 := by
  rw [Gp_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (ψ (j : ℝ) - j + 1)]

end LeanLab.PNTPort.Selberg

