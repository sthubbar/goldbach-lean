module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.DERZ1997.Statements
public import LeanLab.Verifications.Statements

/-!
The ternary Goldbach problem, from Hardy-Littlewood to Helfgott.
P0004 Hardy, Littlewood 1923, Partitio numerorum III: under GRH, every large odd n.
  Their hypothesis is weaker, no L-function zero with real part at least θ for some
  θ < 3/4, as P0061 notes; the GRH form is implied.
P0003 Vinogradov 1937: every sufficiently large odd n, unconditionally.
P0033 Chen, Wang 1996: C = exp(exp(9.715)), as P0061's history states it.
P0023 Liu, Wang 2002, Acta Arith. 105, Theorem 1: every odd integer ≥ V = e^3100. P0061's
  history rounds this to 2 · 10^1346, which is smaller than e^3100; VERIFY caught it.
P0001 Helfgott 2013, arXiv 1312.7748: Main Theorem, every odd n > 5 is a sum of three
  primes; "the proof given here works for all n ≥ C = 10^27", the rest from Helfgott-Platt.
P0061 Helfgott 2015, the book, arXiv 1501.05438: the same Main Theorem.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Ternary
open LeanLab.DERZ1997

/-- Every odd `n ≥ C` is a sum of three primes. -/
def TernaryAbove (C : ℝ) : Prop := ∀ n : ℕ, Odd n → C ≤ n → IsTernarySum n

/-! ### The papers, cited, with `sorry` -/

/-- P0004 Hardy-Littlewood 1923: assuming GRH, every sufficiently large odd number is a sum
of three primes. -/
def hardyLittlewood_stmt : Prop := GRH → ∃ C : ℝ, TernaryAbove C
-- PROVED as `hardyLittlewood` in Ternary/Discharged.lean with GRH unused, audit U-1058;
-- NOT a formalization of Hardy and Littlewood's argument.

/-- P0003 Vinogradov 1937: every sufficiently large odd number is a sum of three primes. -/
def vinogradov_stmt : Prop := ∃ C : ℝ, TernaryAbove C
-- PROVED unconditional, ineffective C, as `vinogradov` in Ternary/Discharged.lean, audit U-1058.




/-! ### Links, zero sorry -/

theorem ternaryAbove_mono {C C' : ℝ} (hC : C ≤ C') (h : TernaryAbove C) : TernaryAbove C' :=
  fun n ho hn => h n ho (hC.trans hn)

/-- Helfgott's Main Theorem from the analytic range and Helfgott-Platt's verification
to `8.875 · 10^30`, P0006. -/
theorem helfgott_main_of (hA : TernaryAbove (10 ^ 27))
    (hHP : TernaryGoldbachUpTo 8875694145621773516800000000000) : TernaryGoldbach := by
  intro n ho h7
  rcases le_or_gt ((10 : ℝ) ^ 27) n with hbig | hsmall
  · exact hA n ho hbig
  · have : n < 10 ^ 27 := by exact_mod_cast hsmall
    exact hHP n ho h7 (by omega)

theorem ternaryAbove_of_ternaryGoldbach (h : TernaryGoldbach) (C : ℝ) (hC : 7 ≤ C) :
    TernaryAbove C := fun n ho hn => h n ho (by exact_mod_cast hC.trans hn)

theorem two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  rw [show Real.exp n = Real.exp 1 ^ n by rw [← Real.exp_nat_mul]; ring_nf]
  gcongr
  linarith [Real.exp_one_gt_d9]

/-- Helfgott's analytic bound implies Liu-Wang's: `10^27 < 2^3100 ≤ e^3100`. -/
theorem liuWang_of_helfgott (h : TernaryAbove (10 ^ 27)) : TernaryAbove (Real.exp 3100) := by
  refine ternaryAbove_mono ?_ h
  have a : (10 : ℝ) ^ 27 ≤ 2 ^ 108 := by
    rw [show (108 : ℕ) = 4 * 27 from rfl, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have b : (2 : ℝ) ^ 108 ≤ 2 ^ 3100 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have c := two_pow_le_exp 3100
  push_cast at c
  exact a.trans (b.trans c)

theorem exp_9715_ge : (3100 : ℝ) ≤ Real.exp 9.715 := by
  have : Real.exp 9 ≤ Real.exp 9.715 := Real.exp_le_exp.mpr (by norm_num)
  have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have : (2.7 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := by gcongr
  nlinarith [show (3100 : ℝ) ≤ 2.7 ^ 9 by norm_num]

/-- Liu-Wang's bound implies Chen-Wang's. -/
theorem chenWang_of_liuWang (h : TernaryAbove (Real.exp 3100)) :
    TernaryAbove (Real.exp (Real.exp 9.715)) :=
  ternaryAbove_mono (Real.exp_le_exp.mpr exp_9715_ge) h

/-- Chen-Wang gives Vinogradov's qualitative theorem. -/
theorem vinogradov_of_chenWang (h : TernaryAbove (Real.exp (Real.exp 9.715))) :
    ∃ C : ℝ, TernaryAbove C := ⟨_, h⟩

/-- Vinogradov makes the Hardy-Littlewood hypothesis unnecessary. -/
theorem hardyLittlewood_of_vinogradov (h : ∃ C : ℝ, TernaryAbove C) :
    GRH → ∃ C : ℝ, TernaryAbove C := fun _ => h

/-- DERZ 1997 under GRH gives Hardy-Littlewood with `C = 7`. -/
theorem hardyLittlewood_of_derz (h : GRH → TernaryGoldbach) :
    GRH → ∃ C : ℝ, TernaryAbove C :=
  fun hG => ⟨7, ternaryAbove_of_ternaryGoldbach (h hG) 7 le_rfl⟩

/-- The whole chain from Helfgott's analytic range. -/
theorem all_of_helfgott (h : TernaryAbove (10 ^ 27)) :
    TernaryAbove (Real.exp 3100) ∧ TernaryAbove (Real.exp (Real.exp 9.715)) ∧
      ∃ C : ℝ, TernaryAbove C := by
  have h1 := liuWang_of_helfgott h
  have h2 := chenWang_of_liuWang h1
  exact ⟨h1, h2, vinogradov_of_chenWang h2⟩

end LeanLab.Ternary
