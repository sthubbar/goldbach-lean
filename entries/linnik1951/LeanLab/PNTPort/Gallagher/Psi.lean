module

public import LeanLab.PNTPort.Gallagher.Basic
public import Mathlib.NumberTheory.Chebyshev

/-!
# Gallagher's lemma for `Λ - 1`

Lab proof, unit U-5851, CLOUD 20261020T0014Z-cloud30. AI wrote this file. Known mathematics,
no cited input.

`gallagher_psi`: for integers `N`, `L ≥ 1`,

  `∫_{|β| ≤ 1/(2L)} ‖∑_{n<N} (Λ(n) - 1) e(nβ)‖² dβ
     ≤ (π/(2L))² (∑_{L ≤ m < N} (ψ(m) - ψ(m - L) - L)² + 2L (L (log N + 1))²)`.

So the mean square of `S(β) - T(β)` near `0`, `S` the exponential sum of `Λ` and `T` that of
`1`, is controlled by the variance of primes in short intervals `(m - L, m]`. This is how
Selberg's mean square under RH, `∑_{m ≤ N} (ψ(m) - ψ(m - L) - L)² ≪ L N log² N`, becomes the
major arc `L²` input of Languasco-Perelli 1996 and Languasco-Zaccagnini 2016 Lemma 1; that
mean square is not in the lab yet.
-/

@[expose] public section


namespace LeanLab.PNTPort.Gallagher

open Complex Finset Real MeasureTheory
open LeanLab.PNTPort.LargeSieve
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- `Λ(n) - 1` as a complex number. -/
noncomputable def lam1 (n : ℕ) : ℂ := ((Λ n - 1 : ℝ) : ℂ)

/-- `ψ(m) - ψ(m - L) = ∑_{m - L < n ≤ m} Λ(n)`. -/
lemma psi_sub_eq (m L : ℕ) (h : L ≤ m) :
    ψ (m : ℝ) - ψ ((m - L : ℕ) : ℝ) = ∑ n ∈ Ioc (m - L) m, Λ n := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [← sum_Ioc_consecutive _ (Nat.zero_le (m - L)) (Nat.sub_le m L)]
  ring

/-- An interior window is `ψ(m) - ψ(m - L) - L`. -/
lemma win_interior {N L m : ℕ} (hLm : L ≤ m) (hmN : m < N) :
    win lam1 N L m = ((ψ (m : ℝ) - ψ ((m - L : ℕ) : ℝ) - L : ℝ) : ℂ) := by
  have hset : (range N).filter (fun n => n ≤ m ∧ m < n + L) = Ioc (m - L) m := by
    ext n; simp only [mem_filter, mem_range, mem_Ioc]; omega
  unfold win lam1
  rw [hset, psi_sub_eq m L hLm, ← Complex.ofReal_sum, sum_sub_distrib]
  congr 1
  simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  rw [Nat.sub_sub_self hLm]

/-- `‖Λ(n) - 1‖ ≤ log N + 1` for `n < N`. -/
lemma norm_lam1_le {N n : ℕ} (hn : n < N) : ‖lam1 n‖ ≤ Real.log N + 1 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hΛ : Λ n ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [hlogN]
    · refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hpos) ?_)
      exact_mod_cast hn.le
  unfold lam1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  constructor <;> linarith

/-- Every window is at most `L (log N + 1)` in norm. -/
lemma norm_win_le (N L m : ℕ) : ‖win lam1 N L m‖ ≤ L * (Real.log N + 1) := by
  unfold win
  have hsub : (range N).filter (fun n => n ≤ m ∧ m < n + L) ⊆ Ico (m + 1 - L) (m + 1) := by
    intro n hn; simp only [mem_filter, mem_range, mem_Ico] at hn ⊢; omega
  have hcard : (((range N).filter (fun n => n ≤ m ∧ m < n + L)).card : ℝ) ≤ L := by
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast this.trans (by omega)
  calc ‖∑ n ∈ (range N).filter (fun n => n ≤ m ∧ m < n + L), lam1 n‖
      ≤ ∑ n ∈ (range N).filter (fun n => n ≤ m ∧ m < n + L), ‖lam1 n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (range N).filter (fun n => n ≤ m ∧ m < n + L), (Real.log N + 1) := by
        refine sum_le_sum fun n hn => norm_lam1_le ?_
        exact mem_range.mp (mem_filter.mp hn).1
    _ = (((range N).filter (fun n => n ≤ m ∧ m < n + L)).card : ℝ) * (Real.log N + 1) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ L * (Real.log N + 1) := by
        rcases Nat.eq_zero_or_pos N with h0 | hpos
        · subst h0; simp
        · have : 0 ≤ Real.log N + 1 := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hpos); linarith
          exact mul_le_mul_of_nonneg_right hcard this

/-- **Gallagher's lemma for `Λ - 1`.** The mean square of `∑_{n<N} (Λ(n) - 1) e(nβ)` on
`|β| ≤ 1/(2L)` is at most `(π/(2L))²` times the short interval variance of `ψ` plus edges. -/
theorem gallagher_psi (N L : ℕ) (hL : 0 < L) :
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range N, lam1 n * e (n * β)‖ ^ 2
      ≤ (π / (2 * L)) ^ 2 * (∑ m ∈ Ico L N, (ψ (m : ℝ) - ψ ((m - L : ℕ) : ℝ) - L) ^ 2
          + 2 * L * (L * (Real.log N + 1)) ^ 2) := by
  refine (gallagher lam1 N L hL).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hsub : Ico L N ⊆ range (N + L) := by
    intro m hm; simp only [mem_Ico, mem_range] at hm ⊢; omega
  rw [← sum_sdiff hsub, add_comm]
  apply add_le_add
  · refine le_of_eq (sum_congr rfl fun m hm => ?_)
    rw [mem_Ico] at hm
    rw [win_interior hm.1 hm.2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · have hc : ((range (N + L) \ Ico L N).card : ℝ) ≤ 2 * L := by
      rw [card_sdiff_of_subset hsub, card_range, Nat.card_Ico]
      exact_mod_cast (by omega : N + L - (N - L) ≤ 2 * L)
    calc ∑ m ∈ range (N + L) \ Ico L N, ‖win lam1 N L m‖ ^ 2
        ≤ ∑ m ∈ range (N + L) \ Ico L N, (L * (Real.log N + 1)) ^ 2 :=
          sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (norm_win_le N L m) 2
      _ = ((range (N + L) \ Ico L N).card : ℝ) * (L * (Real.log N + 1)) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * L * (L * (Real.log N + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end LeanLab.PNTPort.Gallagher

